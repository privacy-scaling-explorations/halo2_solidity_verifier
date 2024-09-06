use crate::codegen::{
    evaluator::{EvaluatorDynamic, EvaluatorStatic},
    pcs::{
        bdfg21_computations_dynamic, bdfg21_computations_static, queries, rotation_sets,
        BatchOpenScheme::{Bdfg21, Gwc19},
    },
    template::{
        Halo2Verifier, Halo2VerifierReusable, Halo2VerifyingArtifact, Halo2VerifyingKey,
        VerifyingCache,
    },
    util::{
        expression_consts, fr_to_u256, g1_to_u256s, g2_to_u256s, ConstraintSystemMeta, Data, Ptr,
    },
};
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

mod evaluator;
mod pcs;
mod template;
pub(crate) mod util;

pub use pcs::BatchOpenScheme;

// Maximum capacity of 10 words allocated for the num_advices_user_challenges encoded data.
const NUM_ADVICES_USER_CHALLENGES_LABELS: [&str; 10] = [
    "num_advices_user_challenges_0",
    "num_advices_user_challenges_1",
    "num_advices_user_challenges_2",
    "num_advices_user_challenges_3",
    "num_advices_user_challenges_4",
    "num_advices_user_challenges_5",
    "num_advices_user_challenges_6",
    "num_advices_user_challenges_7",
    "num_advices_user_challenges_8",
    "num_advices_user_challenges_9",
];

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

    /// Render `Halo2VerifierReusable.sol` and `Halo2VerifyingArtifact.sol` into writers.
    pub fn render_separately_into(
        &self,
        verifier_writer: &mut impl fmt::Write,
        vk_writer: &mut impl fmt::Write,
    ) -> Result<(), fmt::Error> {
        self.generate_separate_verifier().render(verifier_writer)?;
        self.generate_verifying_artifact().render(vk_writer)?;
        Ok(())
    }

    /// Render `Halo2VerifierReusable.sol` and `Halo2VerifyingArtifact.sol` and return them as `String`.
    pub fn render_separately(&self) -> Result<(String, String), fmt::Error> {
        let mut verifier_output = String::new();
        let mut vk_output = String::new();
        self.render_separately_into(&mut verifier_output, &mut vk_output)?;
        Ok((verifier_output, vk_output))
    }

    fn dummy_vka_constants(&self) -> Vec<(&'static str, U256)> {
        // Number of words the num_advices_user_challenges will take up.
        let num_advices_len = self.meta.num_advices().len();
        let slots = 10;
        let num_advices_user_challenges_capacity =
            num_advices_len / slots + if num_advices_len % slots == 0 { 0 } else { 1 };

        // assert that the predefined_labels length are less than the num_advices_user_challenges_capacity
        assert!(
            NUM_ADVICES_USER_CHALLENGES_LABELS.len() >= num_advices_user_challenges_capacity,
            "predefined_labels length of 10 must be less than or equal to num_advices_user_challenges_capacity"
        );

        let mut constants = vec![
            ("vk_digest", U256::from(0)),
            ("vk_mptr", U256::from(0)),
            ("vk_len", U256::from(0)),
            ("instance_cptr", U256::from(0)),
            ("num_instances", U256::from(0)),
            ("num_evals", U256::from(0)),
            ("challenges_offset", U256::from(0)),
            ("fsm_challenges", U256::from(0)), // The fsm position that we can move the num_advices_user_challenges to.
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
            ("last_quotient_x_cptr", U256::from(0)),
            ("first_quotient_x_cptr", U256::from(0)),
            ("gate_computations_len_offset", U256::from(0)),
            ("permutation_computations_len_offset", U256::from(0)),
            ("lookup_computations_len_offset", U256::from(0)),
            ("pcs_computations_len_offset", U256::from(0)),
            ("num_neg_lagranges", U256::from(0)),
        ];
        // Find the index of "fsm_challenges" and insert after it.
        let fsm_challenges_index = constants
            .iter()
            .position(|(label, _)| *label == "fsm_challenges")
            .unwrap();

        // Create a vector of tuples with the num_advices_user_challenges elements.
        let advices_entries: Vec<(&str, U256)> = (0..num_advices_user_challenges_capacity)
            .map(|i| (NUM_ADVICES_USER_CHALLENGES_LABELS[i], U256::from(0)))
            .collect();

        // Insert the num_advices_user_challenges after the "fsm_challenges".
        constants.splice(
            fsm_challenges_index + 1..fsm_challenges_index + 1,
            advices_entries,
        );

        constants
    }

    fn dummy_vk_constants() -> Vec<(&'static str, U256)> {
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

    fn generate_vk(&self, reusable: bool) -> Halo2VerifyingKey {
        // Get the dummy constants using the new function
        let mut constants = if reusable {
            self.dummy_vka_constants()
        } else {
            Self::dummy_vk_constants()
        };

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

        Halo2VerifyingKey {
            constants: constants.clone(),
            fixed_comms: fixed_comms.clone(),
            permutation_comms: permutation_comms.clone(),
        }
    }

    fn generate_verifying_artifact(&self) -> Halo2VerifyingArtifact {
        let mut dummy_vk = self.generate_vk(true);

        fn set_constant_value(constants: &mut [(&str, U256)], name: &str, value: U256) {
            if let Some((_, val)) = constants.iter_mut().find(|(n, _)| *n == name) {
                *val = value;
            }
        }

        let const_expressions = expression_consts(self.vk.cs())
            .into_iter()
            .map(fr_to_u256)
            .collect::<Vec<_>>();

        let vk_mptr_mock = self.estimate_static_working_memory_size(
            &VerifyingCache::Key(&dummy_vk),
            Ptr::calldata(0x84),
        );

        let dummy_data = Data::new(
            &self.meta,
            &VerifyingCache::Key(&dummy_vk),
            Ptr::memory(vk_mptr_mock),
            Ptr::calldata(0x84),
        );

        let mut vk_lookup_const_table_dummy: HashMap<ruint::Uint<256, 4>, Ptr> = HashMap::new();

        let offset = vk_mptr_mock
            + (dummy_vk.constants.len() * 0x20)
            + (dummy_vk.fixed_comms.len() + dummy_vk.permutation_comms.len()) * 0x40;

        // keys to the map are the values of vk.const_expressions and values are the memory location of the vk.const_expressions.
        const_expressions.iter().enumerate().for_each(|(idx, _)| {
            let mptr = offset + (0x20 * idx);
            let mptr = Ptr::memory(mptr);
            vk_lookup_const_table_dummy.insert(const_expressions[idx], mptr);
        });

        let evaluator_dummy = EvaluatorDynamic::new(
            self.vk.cs(),
            &self.meta,
            &dummy_data,
            vk_lookup_const_table_dummy,
        );

        // Fill in the quotient eval computations with dummy values. (maintains the correct shape)
        let gate_computations_dummy = evaluator_dummy.gate_computations();
        let permutation_computations_dummy = evaluator_dummy.permutation_computations();
        let lookup_computations_dummy = evaluator_dummy.lookup_computations(0);
        // Same for the pcs computations
        let pcs_computations_dummy = match self.scheme {
            Bdfg21 => bdfg21_computations_dynamic(&self.meta, &dummy_data),
            Gwc19 => unimplemented!(),
        };

        let num_advices = self.meta.num_advices();
        let num_user_challenges = self.meta.num_challenges();
        // truncate the last elements of num_user_challenges to match the length of num_advices.
        let num_user_challenges = num_user_challenges
            .iter()
            .take(num_advices.len())
            .copied()
            .collect::<Vec<_>>();

        let mut fsm_challenges = 0x20 * (1 + self.num_instances); // initialize fsm_challenges with the space that loading the instances into memory will take up.
        let mut max_advices_value = 0; // Initialize variable to track the maximum value of *num_advices * 0x40

        let num_advices_user_challenges: Vec<U256> = {
            let mut packed_words: Vec<U256> = vec![U256::from(0)];
            let mut bit_counter = 8;
            let mut last_idx = 0;
            for (num_advices, num_user_challenges) in
                num_advices.iter().zip(num_user_challenges.iter())
            {
                let offset = 24;
                let next_bit_counter = bit_counter + offset;
                if next_bit_counter > 256 {
                    last_idx += 1;
                    packed_words.push(U256::from(0));
                    bit_counter = 0;
                }

                let advices_value = *num_advices * 0x40;

                // Ensure that the packed num_advices and num_user_challenges data doesn't overflow.
                assert!(
                    advices_value < 0x10000,
                    "num_advices * 0x40 must be less than 0x10000"
                );
                assert!(
                    *num_user_challenges < 0x100,
                    "num_user_challenges must be less than 0x100"
                );

                // Track the maximum value of *num_advices * 0x40
                if advices_value > max_advices_value {
                    max_advices_value = advices_value;
                }

                packed_words[last_idx] |= U256::from(advices_value) << bit_counter;
                bit_counter += 16;
                packed_words[last_idx] |= U256::from(*num_user_challenges) << bit_counter;
                bit_counter += 8;
            }
            let packed_words_len = packed_words.len();
            // Encode the length of the exprs vec in the first word
            packed_words[0] |= U256::from(packed_words_len);
            packed_words
        };

        fsm_challenges += max_advices_value;

        // Iterate through the `num_advices_user_challenges` and update corresponding values in `constants`
        for (i, value) in num_advices_user_challenges.iter().enumerate() {
            if i >= NUM_ADVICES_USER_CHALLENGES_LABELS.len() {
                panic!("word capacity for num_advices_user_challenges encoded vka data must be less than or equal to 10")
            }
            set_constant_value(
                &mut dummy_vk.constants,
                NUM_ADVICES_USER_CHALLENGES_LABELS[i],
                *value,
            );
        }

        // Update constants
        let first_quotient_x_cptr = dummy_data.quotient_comm_cptr;
        let last_quotient_x_cptr = first_quotient_x_cptr + 2 * (self.meta.num_quotients - 1);
        let instance_cptr = U256::from(self.meta.proof_len(self.scheme) + 0xa4);
        let gate_computations_len_offset = dummy_vk.len(true) + (const_expressions.len() * 0x20);
        let permutations_computations_len_offset =
            gate_computations_len_offset + (0x20 * gate_computations_dummy.len());
        let lookup_computations_len_offset =
            permutations_computations_len_offset + (0x20 * permutation_computations_dummy.len());
        let pcs_computations_len_offset =
            lookup_computations_len_offset + (0x20 * lookup_computations_dummy.len());

        set_constant_value(
            &mut dummy_vk.constants,
            "fsm_challenges",
            U256::from(fsm_challenges),
        );

        set_constant_value(&mut dummy_vk.constants, "instance_cptr", instance_cptr);
        set_constant_value(
            &mut dummy_vk.constants,
            "first_quotient_x_cptr",
            U256::from(first_quotient_x_cptr.value().as_usize()),
        );
        set_constant_value(
            &mut dummy_vk.constants,
            "last_quotient_x_cptr",
            U256::from(last_quotient_x_cptr.value().as_usize()),
        );
        set_constant_value(
            &mut dummy_vk.constants,
            "gate_computations_len_offset",
            U256::from(gate_computations_len_offset),
        );
        set_constant_value(
            &mut dummy_vk.constants,
            "permutation_computations_len_offset",
            U256::from(permutations_computations_len_offset),
        );
        set_constant_value(
            &mut dummy_vk.constants,
            "lookup_computations_len_offset",
            U256::from(lookup_computations_len_offset),
        );
        set_constant_value(
            &mut dummy_vk.constants,
            "pcs_computations_len_offset",
            U256::from(pcs_computations_len_offset),
        );

        // Recreate the vk with the correct shape
        let mut vk = Halo2VerifyingArtifact {
            constants: dummy_vk.constants,
            fixed_comms: dummy_vk.fixed_comms,
            permutation_comms: dummy_vk.permutation_comms,
            const_expressions,
            gate_computations: gate_computations_dummy,
            permutation_computations: permutation_computations_dummy,
            lookup_computations: lookup_computations_dummy,
            pcs_computations: pcs_computations_dummy,
        };

        // Now generate the real vk_mptr with a vk that has the correct length
        let vk_mptr = self.estimate_static_working_memory_size(
            &VerifyingCache::Artifact(&vk),
            Ptr::calldata(0x84),
        );

        // replace the mock vk_mptr with the real vk_mptr
        set_constant_value(&mut vk.constants, "vk_mptr", U256::from(vk_mptr));
        // replace the mock vk_len with the real vk_len
        let vk_len = vk.len(true);
        set_constant_value(&mut vk.constants, "vk_len", U256::from(vk_len));

        // Generate the real data.
        let data = Data::new(
            &self.meta,
            &VerifyingCache::Artifact(&vk),
            Ptr::memory(vk_mptr),
            Ptr::calldata(0x84),
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
        let evaluator =
            EvaluatorDynamic::new(self.vk.cs(), &self.meta, &data, vk_lookup_const_table);

        // NOTE: We don't need to replace the gate_computations_total_length since we are only potentially modifying the offsets for each constant mload operation.
        vk.gate_computations = evaluator.gate_computations();
        // We need to replace the lookup_computations so that the constant mptrs in the encoded input expessions have the correct offsets.
        vk.lookup_computations =
            evaluator.lookup_computations(vk_mptr + lookup_computations_len_offset);
        vk
    }

    fn generate_verifier(&self) -> Halo2Verifier {
        let proof_cptr = Ptr::calldata(0x64);

        let proof_len_cptr = Ptr::calldata(0x6014F51944);

        let vk = self.generate_vk(false);
        let vk_m = self.estimate_static_working_memory_size(&VerifyingCache::Key(&vk), proof_cptr);
        let vk_mptr = Ptr::memory(vk_m);
        let data = Data::new(&self.meta, &VerifyingCache::Key(&vk), vk_mptr, proof_cptr);

        let evaluator = EvaluatorStatic::new(self.vk.cs(), &self.meta, &data);
        let quotient_eval_numer_computations: Vec<Vec<String>> = chain![
            evaluator.gate_computations(),
            evaluator.permutation_computations(),
            evaluator.lookup_computations(),
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
            Bdfg21 => bdfg21_computations_static(&self.meta, &data),
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
        let vk_const_offsets: HashMap<&'static str, U256> = self
            .dummy_vka_constants()
            .iter()
            .enumerate()
            .map(|(idx, &(key, _))| (key, U256::from(idx * 32)))
            .collect();

        Halo2VerifierReusable {
            scheme: self.scheme,
            vk_const_offsets,
        }
    }

    fn estimate_static_working_memory_size(&self, vk: &VerifyingCache, proof_cptr: Ptr) -> usize {
        let mock_vk_mptr = Ptr::memory(0x100000);
        let mock = Data::new(&self.meta, vk, mock_vk_mptr, proof_cptr);
        let pcs_computation = match self.scheme {
            Bdfg21 => {
                let (superset, sets) = rotation_sets(&queries(&self.meta, &mock));
                let num_coeffs = sets.iter().map(|set| set.rots().len()).sum::<usize>();
                2 * (1 + num_coeffs) + 6 + 2 * superset.len() + 1 + 3 * sets.len()
            }
            Gwc19 => unimplemented!(),
        };

        let fsm_usage = itertools::max([
            // Keccak256 input (can overwrite vk)
            itertools::max(chain![
                self.meta.num_advices().into_iter().map(|n| n * 2 + 1),
                [self.meta.num_evals + 1],
            ])
            .unwrap()
            .saturating_sub(vk.len(true) / 0x20),
            // PCS computation
            pcs_computation,
            // Pairing
            12,
        ])
        .unwrap()
            * 0x20;
        //  match statement for vk
        match vk {
            VerifyingCache::Artifact(_) => {
                let mut vk_lookup_const_table_dummy: HashMap<ruint::Uint<256, 4>, Ptr> =
                    HashMap::new();
                let const_expressions = expression_consts(self.vk.cs())
                    .into_iter()
                    .map(fr_to_u256)
                    .collect::<Vec<_>>();
                const_expressions.iter().enumerate().for_each(|(idx, _)| {
                    let mptr = 0x20 * idx;
                    let mptr = Ptr::memory(mptr);
                    vk_lookup_const_table_dummy.insert(const_expressions[idx], mptr);
                });
                let evaluator = EvaluatorDynamic::new(
                    self.vk.cs(),
                    &self.meta,
                    &mock,
                    vk_lookup_const_table_dummy,
                );

                let expression_eval_computations = evaluator.quotient_eval_fsm_usage();
                itertools::max([fsm_usage, expression_eval_computations]).unwrap()
            }
            _ => fsm_usage,
        }
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
