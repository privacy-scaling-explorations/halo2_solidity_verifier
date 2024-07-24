use crate::codegen::{
    evaluator::{Evaluator, EvaluatorVK},
    pcs::{
        bdfg21_computations, queries, rotation_sets,
        BatchOpenScheme::{Bdfg21, Gwc19},
    },
    template::{Halo2Verifier, Halo2VerifyingKey},
    util::{
        expression_consts, fr_to_u256, g1_to_u256s, g2_to_u256s, ConstraintSystemMeta, Data, Ptr,
    },
};
use evaluator::{LookupsDataEncoded, PermutationDataEncoded};
use halo2_proofs::{
    halo2curves::{bn256, ff::Field},
    plonk::VerifyingKey,
    poly::{commitment::ParamsProver, kzg::commitment::ParamsKZG, Rotation},
};
use itertools::{chain, Itertools};
use ruint::aliases::U256;
use std::{
    collections::HashMap,
    fmt::{self, Debug},
};
use template::Halo2VerifierReusable;

mod evaluator;
mod pcs;
mod template;
pub(crate) mod util;

pub use pcs::BatchOpenScheme;

/// Solidity verifier generator for [`halo2`] proof with KZG polynomial commitment scheme on BN254.
#[derive(Debug)]
pub struct SolidityGenerator<'a> {
    params: &'a ParamsKZG<bn256::Bn256>,
    vk: &'a VerifyingKey<bn256::G1Affine>,
    scheme: BatchOpenScheme,
    num_instances: usize,
    acc_encoding: Option<AccumulatorEncoding>,
    meta: ConstraintSystemMeta,
}

/// KZG accumulator encoding information.
/// Limbs of each field element are assumed to be least significant limb first.
///
/// Given instances and `AccumulatorEncoding`, the accumulator will be interpreted as below:
/// ```rust
/// use halo2_proofs::halo2curves::{bn256, ff::{Field, PrimeField}, CurveAffine};
///
/// fn accumulator_from_limbs(
///     instances: &[bn256::Fr],
///     offset: usize,
///     num_limbs: usize,
///     num_limb_bits: usize,
/// ) -> (bn256::G1Affine, bn256::G1Affine) {
///     let limbs = |offset| &instances[offset..offset + num_limbs];
///     let acc_lhs_x = fe_from_limbs(limbs(offset), num_limb_bits);
///     let acc_lhs_y = fe_from_limbs(limbs(offset + num_limbs), num_limb_bits);
///     let acc_rhs_x = fe_from_limbs(limbs(offset + 2 * num_limbs), num_limb_bits);
///     let acc_rhs_y = fe_from_limbs(limbs(offset + 3 * num_limbs), num_limb_bits);
///     let acc_lhs = bn256::G1Affine::from_xy(acc_lhs_x, acc_lhs_y).unwrap();
///     let acc_rhs = bn256::G1Affine::from_xy(acc_rhs_x, acc_rhs_y).unwrap();
///     (acc_lhs, acc_rhs)
/// }
///
/// fn fe_from_limbs(limbs: &[bn256::Fr], num_limb_bits: usize) -> bn256::Fq {
///     limbs.iter().rev().fold(bn256::Fq::ZERO, |acc, limb| {
///         acc * bn256::Fq::from(2).pow_vartime([num_limb_bits as u64])
///             + bn256::Fq::from_repr_vartime(limb.to_repr()).unwrap()
///     })
/// }
/// ```
///
/// In the end of `verifyProof`, the accumulator will be used to do batched pairing with the
/// pairing input of incoming proof.
#[derive(Clone, Copy, Debug)]
pub struct AccumulatorEncoding {
    /// Offset of accumulator limbs in instances.
    pub offset: usize,
    /// Number of limbs per base field element.
    pub num_limbs: usize,
    /// Number of bits per limb.
    pub num_limb_bits: usize,
}

impl AccumulatorEncoding {
    /// Return a new `AccumulatorEncoding`.
    pub fn new(offset: usize, num_limbs: usize, num_limb_bits: usize) -> Self {
        Self {
            offset,
            num_limbs,
            num_limb_bits,
        }
    }
}

impl<'a> SolidityGenerator<'a> {
    /// Return a new `SolidityGenerator`.
    pub fn new(
        params: &'a ParamsKZG<bn256::Bn256>,
        vk: &'a VerifyingKey<bn256::G1Affine>,
        scheme: BatchOpenScheme,
        num_instances: usize,
    ) -> Self {
        assert_ne!(vk.cs().num_advice_columns(), 0);
        assert!(
            vk.cs().num_instance_columns() <= 1,
            "Multiple instance columns is not yet implemented"
        );
        assert!(
            !vk.cs()
                .instance_queries()
                .iter()
                .any(|(_, rotation)| *rotation != Rotation::cur()),
            "Rotated query to instance column is not yet implemented"
        );
        assert_eq!(
            scheme,
            BatchOpenScheme::Bdfg21,
            "BatchOpenScheme::Gwc19 is not yet implemented"
        );

        Self {
            params,
            vk,
            scheme,
            num_instances,
            acc_encoding: None,
            meta: ConstraintSystemMeta::new(vk.cs()),
        }
    }

    /// Set `AccumulatorEncoding`.
    pub fn set_acc_encoding(mut self, acc_encoding: Option<AccumulatorEncoding>) -> Self {
        self.acc_encoding = acc_encoding;
        self
    }
}

impl<'a> SolidityGenerator<'a> {
    /// Render `Halo2Verifier.sol` with verifying key embedded into writer.
    pub fn render_into(&self, verifier_writer: &mut impl fmt::Write) -> Result<(), fmt::Error> {
        self.generate_verifier().render(verifier_writer)
    }

    /// Render `Halo2Verifier.sol` with verifying key embedded and return it as `String`.
    pub fn render(&self) -> Result<String, fmt::Error> {
        let mut verifier_output = String::new();
        self.render_into(&mut verifier_output)?;
        Ok(verifier_output)
    }

    /// Render `Halo2Verifier.sol` and `Halo2VerifyingKey.sol` into writers.
    pub fn render_separately_into(
        &self,
        verifier_writer: &mut impl fmt::Write,
        vk_writer: &mut impl fmt::Write,
    ) -> Result<(), fmt::Error> {
        self.generate_separate_verifier().render(verifier_writer)?;
        self.generate_vk(true).render(vk_writer)?;
        Ok(())
    }

    /// Render `Halo2Verifier.sol` and `Halo2VerifyingKey.sol` and return them as `String`.
    pub fn render_separately(&self) -> Result<(String, String), fmt::Error> {
        let mut verifier_output = String::new();
        let mut vk_output = String::new();
        self.render_separately_into(&mut verifier_output, &mut vk_output)?;
        Ok((verifier_output, vk_output))
    }

    fn dummy_vk_constants(separate: bool) -> Vec<(&'static str, U256)> {
        if separate {
            vec![
                ("vk_digest", U256::from(0)),
                ("vk_mptr", U256::from(0)),
                ("vk_len", U256::from(0)),
                ("num_instances", U256::from(0)),
                ("num_advices_user_challenges_offset", U256::from(0)),
                ("last_quotient_x_cptr", U256::from(0)),
                ("first_quotient_x_cptr", U256::from(0)),
                ("instance_cptr", U256::from(0)),
                ("k", U256::from(0)),
                ("n_inv", U256::from(0)),
                ("omega", U256::from(0)),
                ("omega_inv", U256::from(0)),
                ("omega_inv_to_l", U256::from(0)),
                ("has_accumulator", U256::from(0)),
                ("acc_offset", U256::from(0)),
                ("num_acc_limbs", U256::from(0)),
                ("num_acc_limb_bits", U256::from(0)),
                ("g1_x", U256::from(0)),
                ("g1_y", U256::from(0)),
                ("g2_x_1", U256::from(0)),
                ("g2_x_2", U256::from(0)),
                ("g2_y_1", U256::from(0)),
                ("g2_y_2", U256::from(0)),
                ("neg_s_g2_x_1", U256::from(0)),
                ("neg_s_g2_x_2", U256::from(0)),
                ("neg_s_g2_y_1", U256::from(0)),
                ("neg_s_g2_y_2", U256::from(0)),
                ("challenges_offset", U256::from(0)),
                ("gate_computations_len_offset", U256::from(0)),
                ("permutation_computations_len_offset", U256::from(0)),
                ("lookup_computations_len_offset", U256::from(0)),
                ("num_evals", U256::from(0)),
                ("num_neg_lagranges", U256::from(0)),
            ]
        } else {
            vec![
                ("vk_digest", U256::from(0)),
                ("num_instances", U256::from(0)),
                ("k", U256::from(0)),
                ("n_inv", U256::from(0)),
                ("omega", U256::from(0)),
                ("omega_inv", U256::from(0)),
                ("omega_inv_to_l", U256::from(0)),
                ("has_accumulator", U256::from(0)),
                ("acc_offset", U256::from(0)),
                ("num_acc_limbs", U256::from(0)),
                ("num_acc_limb_bits", U256::from(0)),
                ("g1_x", U256::from(0)),
                ("g1_y", U256::from(0)),
                ("g2_x_1", U256::from(0)),
                ("g2_x_2", U256::from(0)),
                ("g2_y_1", U256::from(0)),
                ("g2_y_2", U256::from(0)),
                ("neg_s_g2_x_1", U256::from(0)),
                ("neg_s_g2_x_2", U256::from(0)),
                ("neg_s_g2_y_1", U256::from(0)),
                ("neg_s_g2_y_2", U256::from(0)),
            ]
        }
    }

    fn generate_vk(&self, separate: bool) -> Halo2VerifyingKey {
        // Get the dummy constants using the new function
        let mut constants = Self::dummy_vk_constants(separate);

        // Fill in the actual values where applicable
        let domain = self.vk.get_domain();
        let vk_digest = fr_to_u256(vk_transcript_repr(self.vk));
        let num_instances = U256::from(self.num_instances);
        let k = U256::from(domain.k());
        let n_inv = fr_to_u256(bn256::Fr::from(1 << domain.k()).invert().unwrap());
        let omega = fr_to_u256(domain.get_omega());
        let omega_inv = fr_to_u256(domain.get_omega_inv());
        let omega_inv_to_l = {
            let l = self.meta.rotation_last.unsigned_abs() as u64;
            fr_to_u256(domain.get_omega_inv().pow_vartime([l]))
        };
        let has_accumulator = U256::from(self.acc_encoding.is_some() as usize);
        let acc_offset = self
            .acc_encoding
            .map(|acc_encoding| U256::from(acc_encoding.offset))
            .unwrap_or_default();
        let num_acc_limbs = self
            .acc_encoding
            .map(|acc_encoding| U256::from(acc_encoding.num_limbs))
            .unwrap_or_default();
        let num_acc_limb_bits = self
            .acc_encoding
            .map(|acc_encoding| U256::from(acc_encoding.num_limb_bits))
            .unwrap_or_default();
        let g1 = self.params.get_g()[0];
        let g1 = g1_to_u256s(g1);
        let g2 = g2_to_u256s(self.params.g2());
        let neg_s_g2 = g2_to_u256s(-self.params.s_g2());

        constants = constants
            .into_iter()
            .map(|(name, dummy_val)| {
                let value = match name {
                    "vk_digest" => vk_digest,
                    "num_instances" => num_instances,
                    "k" => k,
                    "n_inv" => n_inv,
                    "omega" => omega,
                    "omega_inv" => omega_inv,
                    "omega_inv_to_l" => omega_inv_to_l,
                    "has_accumulator" => has_accumulator,
                    "acc_offset" => acc_offset,
                    "num_acc_limbs" => num_acc_limbs,
                    "num_acc_limb_bits" => num_acc_limb_bits,
                    "g1_x" => g1[0],
                    "g1_y" => g1[1],
                    "g2_x_1" => g2[0],
                    "g2_x_2" => g2[1],
                    "g2_y_1" => g2[2],
                    "g2_y_2" => g2[3],
                    "neg_s_g2_x_1" => neg_s_g2[0],
                    "neg_s_g2_x_2" => neg_s_g2[1],
                    "neg_s_g2_y_1" => neg_s_g2[2],
                    "neg_s_g2_y_2" => neg_s_g2[3],
                    "challenges_offset" => U256::from(self.meta.challenge_indices.len() * 32),
                    "num_evals" => U256::from(self.meta.num_evals),
                    "num_neg_lagranges" => {
                        U256::from(self.meta.rotation_last.unsigned_abs() as usize)
                    }
                    _ => dummy_val,
                };
                (name, value)
            })
            .collect();

        let fixed_comms: Vec<(U256, U256)> = chain![self.vk.fixed_commitments()]
            .flat_map(g1_to_u256s)
            .tuples()
            .collect();
        let permutation_comms: Vec<(U256, U256)> = chain![self.vk.permutation().commitments()]
            .flat_map(g1_to_u256s)
            .tuples()
            .collect();

        let attached_vk = Halo2VerifyingKey {
            constants: constants.clone(),
            fixed_comms: fixed_comms.clone(),
            permutation_comms: permutation_comms.clone(),
            const_expressions: vec![],
            num_advices_user_challenges: vec![],
            gate_computations: vec![],
            gate_computations_total_length: 0,
            permutation_computations: PermutationDataEncoded::default(),
            lookup_computations: LookupsDataEncoded::default(),
        };

        if !separate {
            return attached_vk;
        }

        fn set_constant_value(constants: &mut [(&str, U256)], name: &str, value: U256) {
            if let Some((_, val)) = constants.iter_mut().find(|(n, _)| *n == name) {
                *val = value;
            }
        }

        let const_expressions = expression_consts(self.vk.cs())
            .into_iter()
            .map(fr_to_u256)
            .collect::<Vec<_>>();

        let vk_mptr_mock =
            self.estimate_static_working_memory_size(&attached_vk, Ptr::calldata(0x84));

        let dummy_data = Data::new(
            &self.meta,
            &attached_vk,
            Ptr::memory(vk_mptr_mock),
            Ptr::calldata(0x84),
            true,
        );

        let mut vk_lookup_const_table_dummy: HashMap<ruint::Uint<256, 4>, Ptr> = HashMap::new();

        let offset = vk_mptr_mock
            + (attached_vk.constants.len() * 0x20)
            + (attached_vk.fixed_comms.len() + attached_vk.permutation_comms.len()) * 0x40;

        // keys to the map are the values of vk.const_expressions and values are the memory location of the vk.const_expressions.
        const_expressions.iter().enumerate().for_each(|(idx, _)| {
            let mptr = offset + (0x20 * idx);
            let mptr = Ptr::memory(mptr);
            vk_lookup_const_table_dummy.insert(const_expressions[idx], mptr);
        });

        let evaluator_dummy = EvaluatorVK::new(
            self.vk.cs(),
            &self.meta,
            &dummy_data,
            vk_lookup_const_table_dummy,
        );

        // Fill in the gate computations with dummy values. (maintains the correct shape)
        let mut cumulative_length = 0;
        let dummy_gate_computations: Vec<(Vec<U256>, usize)> =
            chain![evaluator_dummy.gate_computations()]
                .map(|lines| {
                    let operations = lines.iter().map(|_line| U256::from(0)).collect::<Vec<_>>();
                    let length = operations.len();
                    let gate_computation = (operations, cumulative_length);
                    cumulative_length += length;
                    gate_computation
                })
                .collect();

        let num_advices = self.meta.num_advices();
        let num_user_challenges = self.meta.num_challenges();
        // truncate the last elements of num_user_challenges to match the length of num_advices.
        let num_user_challenges = num_user_challenges
            .iter()
            .take(num_advices.len())
            .copied()
            .collect::<Vec<_>>();
        // Create a new vec of type of Vec<usize, usize> with the values of num_advices and num_user_challenges.
        let num_advices_user_challenges: Vec<(U256, U256)> = num_advices
            .iter()
            .zip(num_user_challenges.iter())
            .map(|(num_advices, num_user_challenges)| {
                (U256::from(*num_advices), U256::from(*num_user_challenges))
            })
            .collect_vec();

        // Update constants

        let first_quotient_x_cptr = dummy_data.quotient_comm_cptr;
        let last_quotient_x_cptr = first_quotient_x_cptr + 2 * (self.meta.num_quotients - 1);
        let instance_cptr = U256::from(self.meta.proof_len(self.scheme) + 0xa4);
        let num_advices_user_challenges_offset = (constants.len() * 0x20)
            + (fixed_comms.len() + permutation_comms.len()) * 0x40
            + (const_expressions.len() * 0x20);
        let gate_computations_len_offset = num_advices_user_challenges_offset
            + ((num_advices_user_challenges.len() * 0x40) + 0x20);
        let permutations_computations_len_offset = gate_computations_len_offset
            + (0x20 * (dummy_gate_computations.len() + cumulative_length) + 0x20);
        let lookup_computations_len_offset = permutations_computations_len_offset
            + (0x20 * evaluator_dummy.permutation_computations().len());

        set_constant_value(&mut constants, "instance_cptr", instance_cptr);
        set_constant_value(
            &mut constants,
            "first_quotient_x_cptr",
            U256::from(first_quotient_x_cptr.value().as_usize()),
        );
        set_constant_value(
            &mut constants,
            "last_quotient_x_cptr",
            U256::from(last_quotient_x_cptr.value().as_usize()),
        );
        set_constant_value(
            &mut constants,
            "num_advices_user_challenges_offset",
            U256::from(num_advices_user_challenges_offset),
        );
        set_constant_value(
            &mut constants,
            "gate_computations_len_offset",
            U256::from(gate_computations_len_offset),
        );
        set_constant_value(
            &mut constants,
            "permutation_computations_len_offset",
            U256::from(permutations_computations_len_offset),
        );
        set_constant_value(
            &mut constants,
            "lookup_computations_len_offset",
            U256::from(lookup_computations_len_offset),
        );

        // Recreate the vk with the correct shape
        let mut vk = Halo2VerifyingKey {
            constants,
            fixed_comms,
            permutation_comms,
            const_expressions,
            num_advices_user_challenges,
            gate_computations: dummy_gate_computations,
            gate_computations_total_length: cumulative_length,
            permutation_computations: evaluator_dummy.permutation_computations(),
            lookup_computations: evaluator_dummy.lookup_computations(0),
        };

        // Now generate the real vk_mptr with a vk that has the correct length
        let vk_mptr = self.estimate_static_working_memory_size(&vk, Ptr::calldata(0x84));

        // replace the mock vk_mptr with the real vk_mptr
        set_constant_value(&mut vk.constants, "vk_mptr", U256::from(vk_mptr));
        // replace the mock vk_len with the real vk_len
        let vk_len = vk.len();
        set_constant_value(&mut vk.constants, "vk_len", U256::from(vk_len));

        // Generate the real data.
        let data = Data::new(
            &self.meta,
            &vk,
            Ptr::memory(vk_mptr),
            Ptr::calldata(0x84),
            true,
        );

        // Regenerate the gate computations with the correct offsets.
        let mut vk_lookup_const_table: HashMap<ruint::Uint<256, 4>, Ptr> = HashMap::new();

        // create a hashmap of vk.const_expressions values to its vk memory location.
        let offset = vk_mptr
            + (vk.constants.len() * 0x20)
            + (vk.fixed_comms.len() + vk.permutation_comms.len()) * 0x40;

        // keys to the map are the values of vk.const_expressions and values are the memory location of the vk.const_expressions.
        vk.const_expressions
            .iter()
            .enumerate()
            .for_each(|(idx, _)| {
                let mptr = offset + (0x20 * idx);
                let mptr = Ptr::memory(mptr);
                vk_lookup_const_table.insert(vk.const_expressions[idx], mptr);
            });

        // Now we initalize the real evaluator_vk which will contain the correct offsets in the vk_lookup_const_table.
        let evaluator = EvaluatorVK::new(self.vk.cs(), &self.meta, &data, vk_lookup_const_table);

        let mut cumulative_length = 0;
        let gate_computations: Vec<(Vec<U256>, usize)> = chain![evaluator.gate_computations()]
            .map(|lines| {
                let operations = lines
                    .iter()
                    .map(|line: &ruint::Uint<256, 4>| U256::from(*line))
                    .collect::<Vec<_>>();
                let length = operations.len();
                let gate_computation = (operations, cumulative_length);
                cumulative_length += length;
                gate_computation
            })
            .collect();

        // NOTE: We don't need to replace the gate_computations_total_length since we are only potentially modifying the offsets for each constant mload operation.
        vk.gate_computations = gate_computations;
        // We need to replace the lookup_computations so that the constant mptrs in the encoded input expessions have the correct offsets.
        vk.lookup_computations =
            evaluator.lookup_computations(vk_mptr + lookup_computations_len_offset);
        vk
    }

    fn generate_verifier(&self) -> Halo2Verifier {
        let proof_cptr = Ptr::calldata(0x64);

        let proof_len_cptr = Ptr::calldata(0x6014F51944);

        let vk = self.generate_vk(false);
        let vk_m = self.estimate_static_working_memory_size(&vk, proof_cptr);
        let vk_mptr = Ptr::memory(vk_m);
        let data = Data::new(&self.meta, &vk, vk_mptr, proof_cptr, false);

        let evaluator = Evaluator::new(self.vk.cs(), &self.meta, &data);
        let quotient_eval_numer_computations: Vec<Vec<String>> = chain![
            evaluator.gate_computations(),
            evaluator.permutation_computations(false),
            evaluator.lookup_computations(None, false),
        ]
        .enumerate()
        .map(|(idx, (mut lines, var))| {
            let line = if idx == 0 {
                format!("quotient_eval_numer := {var}")
            } else {
                format!(
                    "quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), {var}, r)"
                )
            };
            lines.push(line);
            lines
        })
        .collect();

        let pcs_computations = match self.scheme {
            Bdfg21 => bdfg21_computations(&self.meta, &data, false),
            Gwc19 => unimplemented!(),
        };

        Halo2Verifier {
            scheme: self.scheme,
            embedded_vk: vk,
            vk_mptr,
            num_neg_lagranges: self.meta.rotation_last.unsigned_abs() as usize,
            num_advices: self.meta.num_advices(),
            num_challenges: self.meta.num_challenges(),
            num_evals: self.meta.num_evals,
            num_quotients: self.meta.num_quotients,
            proof_cptr,
            proof_len_cptr,
            quotient_comm_cptr: data.quotient_comm_cptr,
            proof_len: self.meta.proof_len(self.scheme),
            challenge_mptr: data.challenge_mptr,
            theta_mptr: data.theta_mptr,
            quotient_eval_numer_computations,
            pcs_computations,
        }
    }

    fn generate_separate_verifier(&self) -> Halo2VerifierReusable {
        let proof_cptr = Ptr::calldata(0x84);

        let vk = self.generate_vk(true);
        let vk_m = self.estimate_static_working_memory_size(&vk, proof_cptr);
        let vk_mptr = Ptr::memory(vk_m);
        // if separate then create a hashmap of vk.const_expressions values to its vk memory location.
        let mut vk_lookup_const_table: HashMap<ruint::Uint<256, 4>, Ptr> = HashMap::new();
        // create hashmap of vk.const_expressions values to its vk memory location.
        let offset = vk_m
            + (vk.constants.len() * 0x20)
            + (vk.fixed_comms.len() + vk.permutation_comms.len()) * 0x40;
        // keys to the map are the values of vk.const_expressions and values are the memory location of the vk.const_expressions.
        vk.const_expressions
            .iter()
            .enumerate()
            .for_each(|(idx, _)| {
                let mptr = offset + (0x20 * idx);
                let mptr = Ptr::memory(mptr);
                vk_lookup_const_table.insert(vk.const_expressions[idx], mptr);
            });

        let data = Data::new(&self.meta, &vk, vk_mptr, proof_cptr, true);
        let dummy_constants = Self::dummy_vk_constants(true);
        let vk_const_offsets: HashMap<&'static str, U256> = dummy_constants
            .iter()
            .enumerate()
            .map(|(idx, &(key, _))| (key, U256::from(idx * 32)))
            .collect();
        // iterate through the quotient_eval_numer_computations and determine longest Vec<String> within the Vec<Vec<String>>.
        // TODO: Use this to estimate static working memory size
        // let quotient_eval_numer_computations_longest = quotient_eval_numer_computations
        //     .iter()
        //     .max_by_key(|x| x.len())
        //     .unwrap()
        //     .clone();
        // println!(
        //     "longest computation: {:?}",
        //     quotient_eval_numer_computations_longest.len()
        // );

        let pcs_computations = match self.scheme {
            Bdfg21 => bdfg21_computations(&self.meta, &data, true),
            Gwc19 => unimplemented!(),
        };

        Halo2VerifierReusable {
            scheme: self.scheme,
            pcs_computations,
            vk_const_offsets,
        }
    }

    fn estimate_static_working_memory_size(
        &self,
        vk: &Halo2VerifyingKey,
        proof_cptr: Ptr,
    ) -> usize {
        // TODO add a check for the amount of memory required for the compute quotient evavluation
        let pcs_computation = match self.scheme {
            Bdfg21 => {
                let mock_vk_mptr = Ptr::memory(0x100000);
                let mock = Data::new(&self.meta, vk, mock_vk_mptr, proof_cptr, false);
                let (superset, sets) = rotation_sets(&queries(&self.meta, &mock));
                let num_coeffs = sets.iter().map(|set| set.rots().len()).sum::<usize>();
                2 * (1 + num_coeffs) + 6 + 2 * superset.len() + 1 + 3 * sets.len()
            }
            Gwc19 => unimplemented!(),
        };

        itertools::max([
            // Keccak256 input (can overwrite vk)
            itertools::max(chain![
                self.meta.num_advices().into_iter().map(|n| n * 2 + 1),
                [self.meta.num_evals + 1],
            ])
            .unwrap()
            .saturating_sub(vk.len() / 0x20),
            // PCS computation
            pcs_computation,
            // Pairing
            12,
        ])
        .unwrap()
            * 0x20
    }
}

// Remove when `vk.transcript_repr()` is ready for usage.
fn vk_transcript_repr(vk: &VerifyingKey<bn256::G1Affine>) -> bn256::Fr {
    use blake2b_simd::Params;
    use halo2_proofs::halo2curves::ff::FromUniformBytes;

    let fmtted_pinned_vk = format!("{:?}", vk.pinned());
    let mut hasher = Params::new()
        .hash_length(64)
        .personal(b"Halo2-Verify-Key")
        .to_state();
    hasher
        .update(&(fmtted_pinned_vk.len() as u64).to_le_bytes())
        .update(fmtted_pinned_vk.as_bytes());
    FromUniformBytes::from_uniform_bytes(hasher.finalize().as_array())
}
