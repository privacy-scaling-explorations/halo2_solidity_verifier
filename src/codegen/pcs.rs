#![allow(clippy::useless_format)]

use crate::codegen::util::{for_loop, ConstraintSystemMeta, Data, EcPoint, Location, Ptr, Word};
use itertools::{chain, izip, Itertools};
use ruint::aliases::U256;
use std::collections::{BTreeMap, BTreeSet};

/// KZG batch open schemes in `halo2`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BatchOpenScheme {
    /// Batch open scheme in [Plonk] paper.
    /// Corresponding to `halo2_proofs::poly::kzg::multiopen::ProverGWC`
    ///
    /// [Plonk]: https://eprint.iacr.org/2019/953.pdf
    Gwc19,
    /// Batch open scheme in [BDFG21] paper.
    /// Corresponding to `halo2_proofs::poly::kzg::multiopen::ProverSHPLONK`
    ///
    /// [BDFG21]: https://eprint.iacr.org/2020/081.pdf
    Bdfg21,
}

#[derive(Debug)]
pub(crate) struct Query {
    comm: EcPoint,
    rot: i32,
    eval: Word,
}

impl Query {
    fn new(comm: EcPoint, rot: i32, eval: Word) -> Self {
        Self { comm, rot, eval }
    }
}

#[cfg(feature = "mv-lookup")]
pub(crate) fn queries(meta: &ConstraintSystemMeta, data: &Data) -> Vec<Query> {
    chain![
        meta.advice_queries.iter().map(|query| {
            let comm = data.advice_comms[query.0];
            let eval = data.advice_evals[query];
            Query::new(comm, query.1, eval)
        }),
        izip!(&data.permutation_z_comms, &data.permutation_z_evals).flat_map(|(&comm, evals)| {
            [Query::new(comm, 0, evals.0), Query::new(comm, 1, evals.1)]
        }),
        izip!(&data.permutation_z_comms, &data.permutation_z_evals)
            .rev()
            .skip(1)
            .map(|(&comm, evals)| Query::new(comm, meta.rotation_last, evals.2)),
        izip!(
            &data.lookup_m_comms,
            &data.lookup_phi_comms,
            &data.lookup_evals
        )
        .flat_map(|(&m_comm, &phi_comm, evals)| {
            [
                Query::new(phi_comm, 0, evals.0),
                Query::new(phi_comm, 1, evals.1),
                Query::new(m_comm, 0, evals.2),
            ]
        }),
        meta.fixed_queries.iter().map(|query| {
            let comm = data.fixed_comms[query.0];
            let eval = data.fixed_evals[query];
            Query::new(comm, query.1, eval)
        }),
        meta.permutation_columns.iter().map(|column| {
            let comm = data.permutation_comms[column];
            let eval = data.permutation_evals[column];
            Query::new(comm, 0, eval)
        }),
        [
            Query::new(data.computed_quotient_comm, 0, data.computed_quotient_eval),
            Query::new(data.random_comm, 0, data.random_eval),
        ]
    ]
    .collect()
}

#[cfg(not(feature = "mv-lookup"))]
pub(crate) fn queries(meta: &ConstraintSystemMeta, data: &Data) -> Vec<Query> {
    chain![
        meta.advice_queries.iter().map(|query| {
            let comm = data.advice_comms[query.0];
            let eval = data.advice_evals[query];
            Query::new(comm, query.1, eval)
        }),
        izip!(&data.permutation_z_comms, &data.permutation_z_evals).flat_map(|(&comm, evals)| {
            [Query::new(comm, 0, evals.0), Query::new(comm, 1, evals.1)]
        }),
        izip!(&data.permutation_z_comms, &data.permutation_z_evals)
            .rev()
            .skip(1)
            .map(|(&comm, evals)| Query::new(comm, meta.rotation_last, evals.2)),
        izip!(
            &data.lookup_permuted_comms,
            &data.lookup_z_comms,
            &data.lookup_evals
        )
        .flat_map(|(permuted_comms, &z_comm, evals)| {
            [
                Query::new(z_comm, 0, evals.0),
                Query::new(permuted_comms.0, 0, evals.2),
                Query::new(permuted_comms.1, 0, evals.4),
                Query::new(permuted_comms.0, -1, evals.3),
                Query::new(z_comm, 1, evals.1),
            ]
        }),
        meta.fixed_queries.iter().map(|query| {
            let comm = data.fixed_comms[query.0];
            let eval = data.fixed_evals[query];
            Query::new(comm, query.1, eval)
        }),
        meta.permutation_columns.iter().map(|column| {
            let comm = data.permutation_comms[column];
            let eval = data.permutation_evals[column];
            Query::new(comm, 0, eval)
        }),
        [
            Query::new(data.computed_quotient_comm, 0, data.computed_quotient_eval),
            Query::new(data.random_comm, 0, data.random_eval),
        ]
    ]
    .collect()
}

#[derive(Debug)]
pub(crate) struct RotationSet {
    rots: BTreeSet<i32>,
    diffs: BTreeSet<i32>,
    comms: Vec<EcPoint>,
    evals: Vec<Vec<Word>>,
}

impl RotationSet {
    pub(crate) fn rots(&self) -> &BTreeSet<i32> {
        &self.rots
    }

    pub(crate) fn diffs(&self) -> &BTreeSet<i32> {
        &self.diffs
    }

    pub(crate) fn comms(&self) -> &[EcPoint] {
        &self.comms
    }

    pub(crate) fn evals(&self) -> &[Vec<Word>] {
        &self.evals
    }
}

pub(crate) fn rotation_sets(queries: &[Query]) -> (BTreeSet<i32>, Vec<RotationSet>) {
    let mut superset = BTreeSet::new();
    let comm_queries = queries.iter().fold(
        Vec::<(EcPoint, BTreeMap<i32, Word>)>::new(),
        |mut comm_queries, query| {
            superset.insert(query.rot);
            if let Some(pos) = comm_queries
                .iter()
                .position(|(comm, _)| comm == &query.comm)
            {
                let (_, queries) = &mut comm_queries[pos];
                assert!(!queries.contains_key(&query.rot));
                queries.insert(query.rot, query.eval);
            } else {
                comm_queries.push((query.comm, BTreeMap::from_iter([(query.rot, query.eval)])));
            }
            comm_queries
        },
    );
    let superset = superset;
    let sets: Vec<RotationSet> =
        comm_queries
            .into_iter()
            .fold(Vec::<RotationSet>::new(), |mut sets, (comm, queries)| {
                if let Some(pos) = sets
                    .iter()
                    .position(|set| itertools::equal(&set.rots, queries.keys()))
                {
                    let set = &mut sets[pos];
                    if !set.comms.contains(&comm) {
                        set.comms.push(comm);
                        set.evals.push(queries.into_values().collect_vec());
                    }
                } else {
                    let diffs = BTreeSet::from_iter(
                        superset
                            .iter()
                            .filter(|rot| !queries.contains_key(rot))
                            .copied(),
                    );
                    let set = RotationSet {
                        rots: BTreeSet::from_iter(queries.keys().copied()),
                        diffs,
                        comms: vec![comm],
                        evals: vec![queries.into_values().collect()],
                    };
                    sets.push(set);
                }
                sets
            });
    (superset, sets)
}

pub(crate) fn bdfg21_computations_static(
    meta: &ConstraintSystemMeta,
    data: &Data,
) -> Vec<Vec<String>> {
    let queries = queries(meta, data);
    let (superset, sets) = rotation_sets(&queries);
    let min_rot = *superset.first().unwrap();
    let max_rot = *superset.last().unwrap();
    let num_coeffs = sets.iter().map(|set| set.rots().len()).sum::<usize>();

    let w = EcPoint::from(data.w_cptr);
    let w_prime = EcPoint::from(data.w_cptr + 2);

    let diff_0 = Word::from(Ptr::memory(0x00));
    let coeffs = sets
        .iter()
        .scan(diff_0.ptr() + 1, |state, set| {
            let ptrs = Word::range(*state).take(set.rots().len()).collect_vec();
            *state = *state + set.rots().len();
            Some(ptrs)
        })
        .collect_vec();

    let first_batch_invert_end = diff_0.ptr() + 1 + num_coeffs;
    let second_batch_invert_end = diff_0.ptr() + sets.len();
    let free_mptr = diff_0.ptr() + 2 * (1 + num_coeffs) + 6;

    let point_mptr = free_mptr;
    let mu_minus_point_mptr = point_mptr + superset.len();
    let vanishing_0_mptr = mu_minus_point_mptr + superset.len();
    let diff_mptr = vanishing_0_mptr + 1;
    let r_eval_mptr = diff_mptr + sets.len();
    let sum_mptr = r_eval_mptr + sets.len();

    let point_vars =
        izip!(&superset, (0..).map(|idx| format!("point_{idx}"))).collect::<BTreeMap<_, _>>();
    let points = izip!(&superset, Word::range(point_mptr)).collect::<BTreeMap<_, _>>();
    let mu_minus_points =
        izip!(&superset, Word::range(mu_minus_point_mptr)).collect::<BTreeMap<_, _>>();
    let vanishing_0 = Word::from(vanishing_0_mptr);
    let diffs = Word::range(diff_mptr).take(sets.len()).collect_vec();
    let r_evals = Word::range(r_eval_mptr).take(sets.len()).collect_vec();
    let sums = Word::range(sum_mptr).take(sets.len()).collect_vec();

    let point_computations = chain![
        [
            format!("let x := mload({})", "X_MPTR").as_str(),
            format!("let omega := mload({})", "OMEGA_MPTR").as_str(),
            format!("let omega_inv := mload({})", "OMEGA_INV_MPTR").as_str(),
            "let x_pow_of_omega := mulmod(x, omega, R)"
        ]
        .map(str::to_string),
        (1..=max_rot).flat_map(|rot| {
            chain![
                points
                    .get(&rot)
                    .map(|point| format!("mstore({}, x_pow_of_omega)", point.ptr())),
                (rot != max_rot)
                    .then(|| { "x_pow_of_omega := mulmod(x_pow_of_omega, omega, R)".to_string() })
            ]
        }),
        [
            format!("mstore({}, x)", points[&0].ptr()),
            format!("x_pow_of_omega := mulmod(x, omega_inv, R)")
        ],
        (min_rot..0).rev().flat_map(|rot| {
            chain![
                points
                    .get(&rot)
                    .map(|point| format!("mstore({}, x_pow_of_omega)", point.ptr())),
                (rot != min_rot).then(|| {
                    "x_pow_of_omega := mulmod(x_pow_of_omega, omega_inv, R)".to_string()
                })
            ]
        })
    ]
    .collect_vec();
    // print the point computations
    // println!("{:?}", point_computations);
    let vanishing_computations = chain![
        [format!("let mu := mload(MU_MPTR)").to_string()],
        {
            let mptr = mu_minus_points.first_key_value().unwrap().1.ptr();
            let mptr_end = mptr + mu_minus_points.len();
            for_loop(
                [
                    format!("let mptr := {mptr}"),
                    format!("let mptr_end := {mptr_end}"),
                    format!("let point_mptr := {free_mptr}"),
                ],
                "lt(mptr, mptr_end)",
                [
                    "mptr := add(mptr, 0x20)",
                    "point_mptr := add(point_mptr, 0x20)",
                ]
                .map(str::to_string),
                ["mstore(mptr, addmod(mu, sub(R, mload(point_mptr)), R))".to_string()],
            )
        },
        ["let s".to_string()],
        chain![
            [format!(
                "s := {}",
                mu_minus_points[sets[0].rots().first().unwrap()]
            )],
            chain![sets[0].rots().iter().skip(1)]
                .map(|rot| { format!("s := mulmod(s, {}, R)", mu_minus_points[rot]) }),
            [format!("mstore({}, s)", vanishing_0.ptr())],
        ],
        ["let diff".to_string()],
        izip!(0.., &sets, &diffs).flat_map(|(set_idx, set, diff)| {
            chain![
                [set.diffs()
                    .first()
                    .map(|rot| format!("diff := {}", mu_minus_points[rot]))
                    .unwrap_or_else(|| "diff := 1".to_string())],
                chain![set.diffs().iter().skip(1)]
                    .map(|rot| { format!("diff := mulmod(diff, {}, R)", mu_minus_points[rot]) }),
                [format!("mstore({}, diff)", diff.ptr())],
                (set_idx == 0).then(|| format!("mstore({}, diff)", diff_0.ptr())),
            ]
        })
    ]
    .collect_vec();

    let coeff_computations = izip!(&sets, &coeffs)
        .map(|(set, coeffs)| {
            let coeff_points = set
                .rots()
                .iter()
                .map(|rot| &point_vars[rot])
                .enumerate()
                .map(|(i, rot_i)| {
                    set.rots()
                        .iter()
                        .map(|rot| &point_vars[rot])
                        .enumerate()
                        .filter_map(|(j, rot_j)| (i != j).then_some((rot_i, rot_j)))
                        .collect_vec()
                })
                .collect_vec();
            chain![
                set.rots()
                    .iter()
                    .map(|rot| { format!("let {} := {}", &point_vars[rot], points[rot]) }),
                ["let coeff".to_string()],
                izip!(set.rots(), &coeff_points, coeffs).flat_map(
                    |(rot_i, coeff_points, coeff)| chain![
                        [coeff_points
                            .first()
                            .map(|(point_i, point_j)| {
                                format!("coeff := addmod({point_i}, sub(R, {point_j}), R)")
                            })
                            .unwrap_or_else(|| { "coeff := 1".to_string() })],
                        coeff_points.iter().skip(1).map(|(point_i, point_j)| {
                            let item = format!("addmod({point_i}, sub(R, {point_j}), R)");
                            format!("coeff := mulmod(coeff, {item}, R)")
                        }),
                        [
                            format!("coeff := mulmod(coeff, {}, R)", mu_minus_points[rot_i]),
                            format!("mstore({}, coeff)", coeff.ptr())
                        ],
                    ]
                )
            ]
            .collect_vec()
        })
        .collect_vec();

    let normalized_coeff_computations = chain![
        [
            format!("success := batch_invert(success, 0, {first_batch_invert_end})"),
            format!("let diff_0_inv := {diff_0}"),
            format!("mstore({}, diff_0_inv)", diffs[0].ptr()),
        ],
        for_loop(
            [
                format!("let mptr := {}", diffs[0].ptr() + 1),
                format!("let mptr_end := {}", diffs[0].ptr() + sets.len()),
            ],
            "lt(mptr, mptr_end)",
            ["mptr := add(mptr, 0x20)".to_string()],
            ["mstore(mptr, mulmod(mload(mptr), diff_0_inv, R))".to_string()],
        ),
    ]
    .collect_vec();

    let r_evals_computations = izip!(0.., &sets, &coeffs, &diffs, &r_evals).map(
        |(set_idx, set, coeffs, set_coeff, r_eval)| {
            let is_single_rot_set = set.rots().len() == 1;
            chain![
                is_single_rot_set.then(|| format!("let coeff := {}", coeffs[0])),
                [
                    format!("let zeta := mload({})", "ZETA_MPTR").as_str(),
                    "let r_eval := 0"
                ]
                .map(str::to_string),
                if is_single_rot_set {
                    let eval_groups = set.evals().iter().rev().fold(
                        Vec::<Vec<&Word>>::new(),
                        |mut eval_groups, evals| {
                            let eval = &evals[0];
                            if let Some(last_group) = eval_groups.last_mut() {
                                let last_eval = **last_group.last().unwrap();
                                if last_eval.ptr().value().is_integer()
                                    && last_eval.ptr() - 1 == eval.ptr()
                                {
                                    last_group.push(eval)
                                } else {
                                    eval_groups.push(vec![eval])
                                }
                                eval_groups
                            } else {
                                vec![vec![eval]]
                            }
                        },
                    );
                    chain![eval_groups.iter().enumerate()]
                        .flat_map(|(group_idx, evals)| {
                            if evals.len() < 3 {
                                chain![evals.iter().enumerate()]
                                    .flat_map(|(eval_idx, eval)| {
                                        let is_first_eval = group_idx == 0 && eval_idx == 0;
                                        let item = format!("mulmod(coeff, {eval}, R)");
                                        chain![
                                            (!is_first_eval).then(|| format!(
                                                "r_eval := mulmod(r_eval, zeta, R)"
                                            )),
                                            [format!("r_eval := addmod(r_eval, {item}, R)")],
                                        ]
                                    })
                                    .collect_vec()
                            } else {
                                let item = "mulmod(coeff, calldataload(mptr), R)";
                                for_loop(
                                    [
                                        format!("let mptr := {}", evals[0].ptr()),
                                        format!("let mptr_end := {}", evals[0].ptr() - evals.len()),
                                    ],
                                    "lt(mptr_end, mptr)".to_string(),
                                    ["mptr := sub(mptr, 0x20)".to_string()],
                                    [format!(
                                        "r_eval := addmod(mulmod(r_eval, zeta, R), {item}, R)"
                                    )],
                                )
                            }
                        })
                        .collect_vec()
                } else {
                    chain![set.evals().iter().enumerate().rev()]
                        .flat_map(|(idx, evals)| {
                            chain![
                                izip!(evals, coeffs).map(|(eval, coeff)| {
                                    let item = format!("mulmod({coeff}, {eval}, R)");
                                    format!("r_eval := addmod(r_eval, {item}, R)")
                                }),
                                (idx != 0).then(|| format!("r_eval := mulmod(r_eval, zeta, R)")),
                            ]
                        })
                        .collect_vec()
                },
                (set_idx != 0).then(|| format!("r_eval := mulmod(r_eval, {set_coeff}, R)")),
                [format!("mstore({}, r_eval)", r_eval.ptr())],
            ]
            .collect_vec()
        },
    );

    let coeff_sums_computation = izip!(&coeffs, &sums).map(|(coeffs, sum)| {
        let (coeff_0, rest_coeffs) = coeffs.split_first().unwrap();
        chain![
            [format!("let sum := {coeff_0}")],
            rest_coeffs
                .iter()
                .map(|coeff_mptr| format!("sum := addmod(sum, {coeff_mptr}, R)")),
            [format!("mstore({}, sum)", sum.ptr())],
        ]
        .collect_vec()
    });
    let r_eval_computations = chain![
        for_loop(
            [
                format!("let mptr := 0x00"),
                format!("let mptr_end := {second_batch_invert_end}"),
                format!("let sum_mptr := {}", sums[0].ptr()),
            ],
            "lt(mptr, mptr_end)",
            ["mptr := add(mptr, 0x20)", "sum_mptr := add(sum_mptr, 0x20)"].map(str::to_string),
            ["mstore(mptr, mload(sum_mptr))".to_string()],
        ),
        [
            format!("success := batch_invert(success, 0, {second_batch_invert_end})"),
            format!(
                "let r_eval := mulmod(mload({}), {}, R)",
                second_batch_invert_end - 1,
                r_evals.last().unwrap()
            )
        ],
        for_loop(
            [
                format!("let sum_inv_mptr := {}", second_batch_invert_end - 2),
                format!("let sum_inv_mptr_end := {second_batch_invert_end}"),
                format!("let r_eval_mptr := {}", r_evals[r_evals.len() - 2].ptr()),
            ],
            "lt(sum_inv_mptr, sum_inv_mptr_end)",
            [
                "sum_inv_mptr := sub(sum_inv_mptr, 0x20)",
                "r_eval_mptr := sub(r_eval_mptr, 0x20)"
            ]
            .map(str::to_string),
            [
                format!("r_eval := mulmod(r_eval, mload(NU_MPTR), R)").as_str(),
                "r_eval := addmod(r_eval, mulmod(mload(sum_inv_mptr), mload(r_eval_mptr), R), R)"
            ]
            .map(str::to_string),
        ),
        [format!("mstore(R_EVAL_MPTR, r_eval)")],
    ]
    .collect_vec();
    let pairing_input_computations = chain![
        [format!("let nu := mload(NU_MPTR)").to_string()],
        izip!(0.., &sets, &diffs).flat_map(|(set_idx, set, set_coeff)| {
            let is_first_set = set_idx == 0;
            let is_last_set = set_idx == sets.len() - 1;

            let ec_add = &format!("ec_add_{}", if is_first_set { "acc" } else { "tmp" });
            let ec_mul = &format!("ec_mul_{}", if is_first_set { "acc" } else { "tmp" });
            let acc_x = Ptr::memory(0x00) + if is_first_set { 0 } else { 4 };
            let acc_y = acc_x + 1;

            let comm_groups = set.comms().iter().rev().skip(1).fold(
                Vec::<(Location, Vec<&EcPoint>)>::new(),
                |mut comm_groups, comm| {
                    if let Some(last_group) = comm_groups.last_mut() {
                        let last_comm = **last_group.1.last().unwrap();
                        if last_group.0 == comm.loc()
                            && last_comm.x().ptr().value().is_integer()
                            && last_comm.x().ptr() - 2 == comm.x().ptr()
                        {
                            last_group.1.push(comm)
                        } else {
                            comm_groups.push((comm.loc(), vec![comm]))
                        }
                        comm_groups
                    } else {
                        vec![(comm.loc(), vec![comm])]
                    }
                },
            );
            chain![
                set.comms()
                    .last()
                    .map(|comm| {
                        [
                            format!("mstore({acc_x}, {})", comm.x()),
                            format!("mstore({acc_y}, {})", comm.y()),
                        ]
                    })
                    .into_iter()
                    .flatten(),
                comm_groups.into_iter().flat_map(move |(loc, comms)| {
                    if comms.len() < 3 {
                        comms
                            .iter()
                            .flat_map(|comm| {
                                let (x, y) = (comm.x(), comm.y());
                                [
                                    format!("success := {ec_mul}(success, mload(ZETA_MPTR))"),
                                    format!("success := {ec_add}(success, {x}, {y})"),
                                ]
                            })
                            .collect_vec()
                    } else {
                        let mptr = comms.first().unwrap().x().ptr();
                        let mptr_end = mptr - 2 * comms.len();
                        let x = Word::from(Ptr::new(loc, "mptr"));
                        let y = Word::from(Ptr::new(loc, "add(mptr, 0x20)"));
                        for_loop(
                            [
                                format!("let mptr := {mptr}"),
                                format!("let mptr_end := {mptr_end}"),
                            ],
                            "lt(mptr_end, mptr)",
                            ["mptr := sub(mptr, 0x40)".to_string()],
                            [
                                format!("success := {ec_mul}(success, mload(ZETA_MPTR))"),
                                format!("success := {ec_add}(success, {x}, {y})"),
                            ],
                        )
                    }
                }),
                (!is_first_set)
                    .then(|| {
                        let scalar = format!("mulmod(nu, {set_coeff}, R)");
                        chain![
                            [
                                format!("success := ec_mul_tmp(success, {scalar})"),
                                format!("success := ec_add_acc(success, mload(0x80), mload(0xa0))"),
                            ],
                            (!is_last_set).then(|| format!("nu := mulmod(nu, mload(NU_MPTR), R)"))
                        ]
                    })
                    .into_iter()
                    .flatten(),
            ]
            .collect_vec()
        }),
        [
            format!("mstore(0x80, mload({}))", "G1_X_MPTR"),
            format!("mstore(0xa0, mload({}))", "G1_Y_MPTR"),
            format!("success := ec_mul_tmp(success, sub(R, mload(R_EVAL_MPTR)))"),
            format!("success := ec_add_acc(success, mload(0x80), mload(0xa0))"),
            format!("mstore(0x80, {})", w.x()),
            format!("mstore(0xa0, {})", w.y()),
            format!("success := ec_mul_tmp(success, sub(R, {vanishing_0}))"),
            format!("success := ec_add_acc(success, mload(0x80), mload(0xa0))"),
            format!("mstore(0x80, {})", w_prime.x()),
            format!("mstore(0xa0, {})", w_prime.y()),
            format!("success := ec_mul_tmp(success, mload(MU_MPTR))"),
            format!("success := ec_add_acc(success, mload(0x80), mload(0xa0))"),
            format!("mstore(PAIRING_LHS_X_MPTR, mload(0x00))"),
            format!("mstore(PAIRING_LHS_Y_MPTR, mload(0x20))"),
            format!("mstore(PAIRING_RHS_X_MPTR, {})", w_prime.x()),
            format!("mstore(PAIRING_RHS_Y_MPTR, {})", w_prime.y()),
        ],
    ]
    .collect_vec();

    chain![
        [point_computations, vanishing_computations],
        coeff_computations,
        [normalized_coeff_computations],
        r_evals_computations,
        coeff_sums_computation,
        [r_eval_computations, pairing_input_computations],
    ]
    .collect_vec()
}

// Holds the encoded data stored in the separate VK
// needed to perform the pcs computations portion of the reusable verifier.
#[derive(Clone, PartialEq, Eq, Default)]
pub struct PcsDataEncoded {
    pub(crate) point_computations: Vec<U256>,
    pub(crate) vanishing_computations: Vec<U256>,
    pub(crate) coeff_computations: Vec<U256>,
    pub(crate) normalized_coeff_computations: U256,
    pub(crate) r_evals_computations: Vec<U256>,
    pub(crate) coeff_sums_computation: Vec<U256>,
    pub(crate) r_eval_computations: U256,
    pub(crate) pairing_input_computations: Vec<U256>,
}

// implement length of PcsDataEncoded
impl PcsDataEncoded {
    pub fn len(&self) -> usize {
        self.point_computations.len()
            + self.vanishing_computations.len()
            + self.coeff_computations.len()
            + 1 // normalized_coeff_computations
            + self.r_evals_computations.len()
            + self.coeff_sums_computation.len()
            + 1 // r_eval_computations
            + self.pairing_input_computations.len()
    }
}

pub(crate) fn bdfg21_computations_dynamic(
    meta: &ConstraintSystemMeta,
    data: &Data,
) -> PcsDataEncoded {
    let queries = queries(meta, data);
    let (superset, sets) = rotation_sets(&queries);
    let min_rot = *superset.first().unwrap();
    let max_rot = *superset.last().unwrap();
    let num_coeffs = sets.iter().map(|set| set.rots().len()).sum::<usize>();

    let w = EcPoint::from(data.w_cptr);
    let w_prime = EcPoint::from(data.w_cptr + 2);

    let diff_0 = Word::from(Ptr::memory(0x00));
    let coeffs = sets
        .iter()
        .scan(diff_0.ptr() + 1, |state, set| {
            let ptrs = Word::range(*state).take(set.rots().len()).collect_vec();
            *state = *state + set.rots().len();
            Some(ptrs)
        })
        .collect_vec();

    let first_batch_invert_end = diff_0.ptr() + 1 + num_coeffs;
    let second_batch_invert_end = diff_0.ptr() + sets.len();
    let free_mptr = diff_0.ptr() + 2 * (1 + num_coeffs) + 6;

    let point_mptr = free_mptr;
    let mu_minus_point_mptr = point_mptr + superset.len();
    let vanishing_0_mptr = mu_minus_point_mptr + superset.len();
    let diff_mptr = vanishing_0_mptr + 1;
    let r_eval_mptr = diff_mptr + sets.len();
    let sum_mptr = r_eval_mptr + sets.len();

    let points = izip!(&superset, Word::range(point_mptr)).collect::<BTreeMap<_, _>>();
    let mu_minus_points =
        izip!(&superset, Word::range(mu_minus_point_mptr)).collect::<BTreeMap<_, _>>();
    let vanishing_0 = Word::from(vanishing_0_mptr);
    let diffs = Word::range(diff_mptr).take(sets.len()).collect_vec();
    let r_evals = Word::range(r_eval_mptr).take(sets.len()).collect_vec();
    let sums = Word::range(sum_mptr).take(sets.len()).collect_vec();

    let point_computations: Vec<U256> = {
        let pack_words = |points: Vec<U256>, interm_point: Option<U256>| {
            let mut packed_words: Vec<U256> = vec![U256::from(0)];
            let mut bit_counter = 8;
            let points_len = points.len();
            // assert that points_len is less than 256 bits so that it fits into 1 byte.
            assert!(points_len < 256);
            if let Some(interm_point) = interm_point {
                packed_words[0] |= interm_point;
                packed_words[0] |= U256::from(points_len) << 16;
                bit_counter = 24;
            } else {
                packed_words[0] |= U256::from(points_len);
            }
            let mut last_idx = 0;

            for point in points.iter() {
                let offset = 16;

                let next_bit_counter = bit_counter + offset;
                if next_bit_counter > 256 {
                    last_idx += 1;
                    packed_words.push(U256::from(0));
                    bit_counter = 0;
                }
                packed_words[last_idx] |= *point << bit_counter;
                bit_counter += 16;
            }

            packed_words
        };
        let max_rot_computations = (1..=max_rot)
            .map(|rot| {
                points
                    .get(&rot)
                    .map(|point| U256::from(point.ptr().value().as_usize()))
                    .unwrap_or(U256::from(0))
            })
            .collect_vec();
        let min_rot_computations = (min_rot..0)
            .rev()
            .map(|rot| {
                points
                    .get(&rot)
                    .map(|point| U256::from(point.ptr().value().as_usize()))
                    .unwrap_or(U256::from(0))
            })
            .collect_vec();
        chain!(
            pack_words(max_rot_computations, None).into_iter(),
            pack_words(
                min_rot_computations,
                Some(U256::from(points[&0].ptr().value().as_usize())),
            )
            .into_iter()
        )
        .collect_vec()
    };

    let vanishing_computations: Vec<U256> = {
        let pack_mptrs_and_s_ptrs: Vec<U256> = {
            let mptr = mu_minus_points.first_key_value().unwrap().1.ptr();
            let mptr_word = U256::from(mptr.value().as_usize());
            let mptr_end = mptr + mu_minus_points.len();
            let mptr_end_word = U256::from(mptr_end.value().as_usize());
            let mut last_idx = 0;
            let mut packed_words = vec![U256::from(0)];
            // start packing the mptrs
            packed_words[0] |= mptr_word;
            packed_words[0] |= mptr_end_word << 16;
            packed_words[0] |= U256::from(free_mptr.value().as_usize()) << 32;
            // bit offset length to where the number of words allocated to the s_ptrs will be stored.
            let words_alloc_offset = 48;
            let mut bit_counter = words_alloc_offset + 8;
            // start packing the s_ptrs
            sets[0].rots().iter().for_each(|rot| {
                // panic if offset is exceeds 256
                let next_bit_counter = bit_counter + 16;
                if next_bit_counter > 256 {
                    last_idx += 1;
                    packed_words.push(U256::from(0));
                    bit_counter = 0;
                }
                packed_words[last_idx] |=
                    U256::from(mu_minus_points[rot].ptr().value().as_usize()) << bit_counter;
                bit_counter += 16;
            });
            // store the num words allocated for s_ptrs
            packed_words[0] |= U256::from(last_idx + 1) << words_alloc_offset;
            packed_words
        };
        let pack_vanishing_0_and_sets_len: ruint::Uint<256, 4> = {
            let vanishing_0_word = U256::from(vanishing_0.ptr().value().as_usize());
            let sets_len = U256::from(sets.len());
            let mut packed_word = U256::from(0);
            packed_word |= vanishing_0_word;
            packed_word |= sets_len << 16;
            packed_word
        };
        let pack_set_diffs_words: Vec<ruint::Uint<256, 4>> = {
            sets.iter()
                .map(|set| {
                    let mut packed_word = U256::from(0);
                    let mut offset = 0;
                    set.diffs().iter().for_each(|rot| {
                        packed_word |=
                            U256::from(mu_minus_points[rot].ptr().value().as_usize()) << offset;
                        offset += 16;
                    });
                    if set.diffs.is_empty() {
                        // 0x20 is where 1 is stored in memory in this block
                        packed_word |= U256::from(0x20) << offset;
                        offset += 16;
                    }
                    assert!(
                        offset <= 256,
                        "The offset for packing the set diff word exceeds 256 bits",
                    );
                    packed_word
                })
                .collect_vec()
        };
        chain!(
            pack_mptrs_and_s_ptrs.into_iter(),
            [pack_vanishing_0_and_sets_len],
            pack_set_diffs_words.into_iter()
        )
        .collect_vec()
    };
    let coeff_computations: Vec<U256> = {
        // 1) The first LSG byte of the first word will contain the number of words that are used to store the
        // the set.rots().len(). The rest of the bytes in the word will contain the set.rots().len()
        let coeff_len_words: Vec<U256> = {
            let mut packed_words: Vec<U256> = vec![U256::from(0)];
            let mut bit_counter = 8;
            let mut last_idx = 0;
            for set in sets.iter() {
                let coeff_len = set.rots().len();
                assert!(coeff_len <= 5, "The number of rotations in a set exceeds 5 for the coeff_computations. Can't pack all the coef_data in a single word");
                let offset = 8;
                let next_bit_counter = bit_counter + offset;
                if next_bit_counter > 256 {
                    last_idx += 1;
                    packed_words.push(U256::from(0));
                    bit_counter = 0;
                }
                packed_words[last_idx] |= U256::from(coeff_len) << bit_counter;
                bit_counter += 8;
            }
            let packed_words_len = packed_words.len();
            // Encode the length of the exprs vec in the first word
            packed_words[0] |= U256::from(packed_words_len);
            packed_words
        };
        // The next set of words will contain the points for the set.rots() followed by the mu_minus_points
        // and the coeff.ptr(). Throw if set.rots().len > 5 b/c anything greater than 5 we can't pack all the ptr data into a single word.
        let coeff_data_words: Vec<U256> = izip!(&sets, &coeffs)
            .map(|(set, coeffs)| {
                let mut packed_word = U256::from(0);
                let mut offset = 0;
                if set.rots().len() > 1 {
                    set.rots().iter().for_each(|rot| {
                        packed_word |= U256::from(points[rot].ptr().value().as_usize()) << offset;
                        offset += 16;
                    });
                }
                set.rots().iter().for_each(|rot| {
                    packed_word |=
                        U256::from(mu_minus_points[rot].ptr().value().as_usize()) << offset;
                    offset += 16;
                });
                coeffs.iter().for_each(|coeff| {
                    packed_word |= U256::from(coeff.ptr().value().as_usize()) << offset;
                    offset += 16;
                });
                assert!(
                    offset <= 256,
                    "The offset for packing the coeff computation word exceeds 256 bits",
                );
                packed_word
            })
            .collect_vec();
        chain!(coeff_len_words.into_iter(), coeff_data_words.into_iter()).collect_vec()
    };

    let normalized_coeff_computations: U256 = {
        let mut packed_word = U256::from(0);
        let mut offset = 0;
        packed_word |= U256::from(first_batch_invert_end.value().as_usize()) << offset;
        offset += 16;
        packed_word |= U256::from(diffs[0].ptr().value().as_usize()) << offset;
        offset += 16;
        packed_word |= U256::from(sets.len() * 32) << offset;
        packed_word
    };

    // 1. The LSG byte of the first word will contain the total number of words that contain the set_coeff and the r_eval ptr followed
    // by the packed Vec<evals.rot.len()>.
    // 2. The next set of words will contain the evaluation pointers. The first LSG byte will contain the number of words
    // that contain the packed evaluation pointers. The rest of the bytes will contain the evaluation pointers or evaluation pointers + coeff pointer.
    // depending on if it is a single rotation set or not.
    // 3. Here is how the encoding of the single rotation set will look like:
    // 3a. After the 1 byte that contains the number of words with the packed ptr data for the given set, we encode the coeffs[0] ptr,
    // the first eval ptr of the first group.
    // 3b. Next we encode the number of eval ptrs in the eval_group, encoding the eval ptrs that follow until we reach the end of the eval_group, repeating the process for the next eval_group.
    // 4. Here is how the encoding of the not single rotation set will look like:
    // 4a. After the 1 byte that contains the number of words with the packed ptr data for the given set, the coeffs ptrs,
    // and the eval ptrs.
    // and the coeff.ptr(). Throw if set.rots().len > 5 b/c anything greater than 5 we can't pack all the ptr data into a single word.

    let r_evals_computations: Vec<U256> = {
        let pack_value = |packed_word: &mut U256, value: usize, bit_counter: &mut usize| {
            *packed_word |= U256::from(value) << *bit_counter;
            *bit_counter += 16;
        };
        let encode_coeff_length = |coeff_len: usize, single_rot_set: &mut usize| -> usize {
            if coeff_len == 1 {
                *single_rot_set += 1;
                assert!(
                    *single_rot_set <= 1,
                    "Only one single rotation set in the r_evals_computations"
                );
                coeff_len * 32
            } else {
                assert!(coeff_len != 0, "The number of rotations in a set is 0");
                coeff_len * 32
            }
        };

        let r_evals_meta_data: Vec<U256> = {
            let mut packed_words = vec![U256::from(0)];
            let mut bit_counter = 8;

            pack_value(
                &mut packed_words[0],
                diffs[1].ptr().value().as_usize(),
                &mut bit_counter,
            );
            pack_value(
                &mut packed_words[0],
                r_eval_mptr.value().as_usize(),
                &mut bit_counter,
            );

            let mut last_idx = 0;
            let mut single_rot_set = 0;

            for set in sets.iter() {
                let coeff_len = set.rots().len();
                // if coeff_len is greater than 1 then we scale it by 16.
                let encoded_length = encode_coeff_length(coeff_len, &mut single_rot_set);

                assert!(
                    encoded_length < 256,
                    "The encoded length for r_evals exceeds 256 bits"
                );

                let next_bit_counter = bit_counter + 8;
                if next_bit_counter > 256 {
                    last_idx += 1;
                    packed_words.push(U256::from(0));
                    bit_counter = 0;
                }
                packed_words[last_idx] |= U256::from(encoded_length) << bit_counter;
                bit_counter += 8;
            }

            let packed_words_len = packed_words.len();
            packed_words[0] |= U256::from(packed_words_len);
            packed_words
        };

        let calculate_evals_len_offset = |evals: &[&Word]| -> (usize, usize) {
            if evals.len() < 3 {
                (evals.len(), 8 + (evals.len() * 16))
            } else {
                (0, 8 + 32)
            }
        };

        let pack_evals = |packed_words: &mut Vec<U256>,
                          evals: &[&Word],
                          evals_len: usize,
                          bit_counter: &mut usize,
                          last_idx: usize| {
            if evals_len == 0 {
                let mptr = evals[0].ptr();
                let mptr_end = evals[0].ptr() - evals.len();
                packed_words[last_idx] |= U256::from(mptr.value().as_usize()) << *bit_counter;
                *bit_counter += 16;
                packed_words[last_idx] |= U256::from(mptr_end.value().as_usize()) << *bit_counter;
                *bit_counter += 16;
            } else {
                for eval in evals.iter() {
                    let eval_ptr = eval.ptr();
                    packed_words[last_idx] |=
                        U256::from(eval_ptr.value().as_usize()) << *bit_counter;
                    *bit_counter += 16;
                }
            }
        };

        let process_single_rotation_set =
            |set: &RotationSet,
             packed_words: &mut Vec<U256>,
             bit_counter: &mut usize,
             last_idx: &mut usize| {
                let eval_groups = set.evals().iter().rev().fold(
                    Vec::<Vec<&Word>>::new(),
                    |mut eval_groups, evals| {
                        let eval = &evals[0];
                        if let Some(last_group) = eval_groups.last_mut() {
                            let last_eval = **last_group.last().unwrap();
                            if last_eval.ptr().value().is_integer()
                                && last_eval.ptr() - 1 == eval.ptr()
                            {
                                last_group.push(eval)
                            } else {
                                eval_groups.push(vec![eval])
                            }
                            eval_groups
                        } else {
                            vec![vec![eval]]
                        }
                    },
                );

                let first_eval_ptr = eval_groups[0][0].ptr();
                assert!(
                    eval_groups[1][0].ptr().loc() == Location::Memory,
                    "The second eval group for a single rotation set should be memory but it is not"
                );
                pack_value(
                    &mut packed_words[0],
                    first_eval_ptr.value().as_usize(),
                    bit_counter,
                );

                for evals in eval_groups.iter().skip(2) {
                    let (evals_len, offset) = calculate_evals_len_offset(evals);
                    let next_bit_counter = *bit_counter + offset;

                    if next_bit_counter > 256 {
                        *last_idx += 1;
                        packed_words.push(U256::from(0));
                        *bit_counter = 0;
                    }

                    packed_words[*last_idx] |= U256::from(evals_len) << *bit_counter;
                    *bit_counter += 8;
                    pack_evals(packed_words, evals, evals_len, bit_counter, *last_idx);
                }
            };

        let process_multiple_rotation_set =
            |set: &RotationSet,
             packed_words: &mut Vec<U256>,
             bit_counter: &mut usize,
             last_idx: &mut usize| {
                for evals in set.evals().iter().rev() {
                    let offset = coeffs.len() * 16;
                    let next_bit_counter = *bit_counter + offset;

                    if next_bit_counter > 256 {
                        *last_idx += 1;
                        packed_words.push(U256::from(0));
                        *bit_counter = 0;
                    }
                    for eval in evals.iter() {
                        let eval_ptr = eval.ptr();
                        packed_words[*last_idx] |=
                            U256::from(eval_ptr.value().as_usize()) << *bit_counter;
                        *bit_counter += 16;
                    }
                }
            };

        let r_evals_data: Vec<U256> = sets
            .iter()
            .flat_map(|set| {
                let mut packed_words = vec![U256::from(0)];
                let mut last_idx = 0;
                let mut bit_counter = 8;

                if set.rots().len() == 1 {
                    process_single_rotation_set(
                        set,
                        &mut packed_words,
                        &mut bit_counter,
                        &mut last_idx,
                    );
                } else {
                    process_multiple_rotation_set(
                        set,
                        &mut packed_words,
                        &mut bit_counter,
                        &mut last_idx,
                    );
                }

                let packed_words_len = packed_words.len();
                packed_words[0] |= U256::from(packed_words_len);
                packed_words
            })
            .collect();
        chain!(r_evals_meta_data.into_iter(), r_evals_data.into_iter()).collect_vec()
    };

    let coeff_sums_computation: Vec<U256> = {
        let mut packed_words = vec![U256::from(0)];
        let mut bit_counter = 8;
        let mut last_idx = 0;
        for (coeffs, sum) in izip!(&coeffs, &sums) {
            let offset = 24;
            let next_bit_counter = bit_counter + offset;
            let len = coeffs.len() * 32;
            assert!(len < 256, "The length of the coeffs exceeds 256 bits");
            if next_bit_counter > 256 {
                last_idx += 1;
                packed_words.push(U256::from(0));
                bit_counter = 0;
            }
            packed_words[last_idx] |= U256::from(len) << bit_counter;
            bit_counter += 8;
            packed_words[last_idx] |= U256::from(sum.ptr().value().as_usize()) << bit_counter;
            bit_counter += 16;
        }
        let packed_words_len = packed_words.len();
        packed_words[0] |= U256::from(packed_words_len);
        packed_words
    };

    let r_eval_computations: U256 = {
        let mut packed_word = U256::from(0);
        let mut offset = 0;
        packed_word |= U256::from(second_batch_invert_end.value().as_usize()) << offset;
        offset += 16;
        packed_word |= U256::from(sums[0].ptr().value().as_usize()) << offset;
        offset += 16;
        packed_word |= U256::from(r_evals.last().unwrap().ptr().value().as_usize()) << offset;
        packed_word
    };

    let pairing_input_computations: Vec<U256> = {
        let mut word_lengths = Vec::new();
        let data: Vec<U256> = sets
            .iter()
            .flat_map(|set| {
                let comm_groups = set.comms().iter().rev().skip(1).fold(
                    Vec::<(Location, Vec<&EcPoint>)>::new(),
                    |mut comm_groups, comm| {
                        if let Some(last_group) = comm_groups.last_mut() {
                            let last_comm = **last_group.1.last().unwrap();
                            if last_group.0 == comm.loc()
                                && last_comm.x().ptr().value().is_integer()
                                && last_comm.x().ptr() - 2 == comm.x().ptr()
                            {
                                last_group.1.push(comm)
                            } else {
                                comm_groups.push((comm.loc(), vec![comm]))
                            }
                            comm_groups
                        } else {
                            vec![(comm.loc(), vec![comm])]
                        }
                    },
                );
                let mut packed_words = vec![U256::from(0)];
                let mut bit_counter = 0;
                let mut last_idx = 0;
                let comm = set.comms().last().unwrap();
                packed_words[last_idx] |=
                    U256::from(comm.x().ptr().value().as_usize()) << bit_counter;
                bit_counter += 16;
                packed_words[last_idx] |=
                    U256::from(comm.y().ptr().value().as_usize()) << bit_counter;
                bit_counter += 16;
                for (loc, comms) in comm_groups.iter() {
                    let is_quotient_point = !comms[0].x().ptr().value().is_integer()
                        && !comms[0].y().ptr().value().is_integer();
                    let offset = if comms.len() == 2 { 80 } else if is_quotient_point { 16 } else { 48 } ;
                    let next_bit_counter = bit_counter + offset;
                    if next_bit_counter > 256 {
                        last_idx += 1;
                        packed_words.push(U256::from(0));
                        bit_counter = 0;
                    }
                    let loc_encoded = if is_quotient_point
                    {
                        assert!(
                            comms.len() == 1,
                            "The number of comms in the group containing the quotient points must be 1",
                        );
                        // we encode 0x02 if the comm is a quotient point 
                        0x02
                    } else {
                        // check the location of the comm. If it is memory then we encode 0x00, 0x01 otherwise
                        if *loc == Location::Memory { 0x00 } else { 0x01 }
                    };
                    packed_words[last_idx] |= U256::from(loc_encoded) << bit_counter;
                    bit_counter += 8;
                    let len_encoded = if comms.len() < 3 { comms.len() } else { 0 };
                    packed_words[last_idx] |= U256::from(len_encoded) << bit_counter;
                    bit_counter += 8;
                    if loc_encoded == 0x02 {
                        // we hardcode the location of the quotient points in reusable verifier so we skip encoding them
                        // in the vk 
                        continue;
                    }
                    if comms.len() < 3 {
                        comms.iter().for_each(|comm| {
                            packed_words[last_idx] |=
                                U256::from(comm.x().ptr().value().as_usize()) << bit_counter;
                            bit_counter += 16;
                            packed_words[last_idx] |=
                                U256::from(comm.y().ptr().value().as_usize()) << bit_counter;
                            bit_counter += 16;
                        });
                    } else {
                        let mptr = comms.first().unwrap().x().ptr();
                        let mptr_end = mptr - 2 * comms.len();
                        packed_words[last_idx] |=
                            U256::from(mptr.value().as_usize()) << bit_counter;
                        bit_counter += 16;
                        packed_words[last_idx] |=
                            U256::from(mptr_end.value().as_usize()) << bit_counter;
                        bit_counter += 16;
                    }
                }
                assert!(
                    packed_words.len() * 32 < 256,
                    "The bit counter for the pairing input computations exceeds 256 bits"
                );
                // update the word lengths
                word_lengths.push(packed_words.len() * 32);
                packed_words
            })
            .collect();

        let meta_data: Vec<U256> = {
            let mut packed_words = vec![U256::from(0)];
            let mut bit_counter = 8;
            let mut last_idx = 0;
            packed_words[last_idx] |= U256::from(diffs[1].ptr().value().as_usize()) << bit_counter;
            bit_counter += 16;
            // pack the ec points cptrs
            packed_words[last_idx] |= U256::from(w.x().ptr().value().as_usize()) << bit_counter;
            bit_counter += 16;
            packed_words[last_idx] |= U256::from(w.y().ptr().value().as_usize()) << bit_counter;
            bit_counter += 16;
            packed_words[last_idx] |=
                U256::from(vanishing_0.ptr().value().as_usize()) << bit_counter;
            bit_counter += 16;
            packed_words[last_idx] |=
                U256::from(w_prime.x().ptr().value().as_usize()) << bit_counter;
            bit_counter += 16;
            packed_words[last_idx] |=
                U256::from(w_prime.y().ptr().value().as_usize()) << bit_counter;
            bit_counter += 16;

            // iterate through the word lengths and pack them into the first word
            for len in word_lengths.iter() {
                let next_bit_counter = bit_counter + 8;
                if next_bit_counter > 256 {
                    last_idx += 1;
                    packed_words.push(U256::from(0));
                    bit_counter = 0;
                }
                packed_words[last_idx] |= U256::from(*len) << bit_counter;
                bit_counter += 8;
            }
            let packed_words_len = packed_words.len();
            packed_words[0] |= U256::from(packed_words_len);
            packed_words
        };
        chain!(meta_data.into_iter(), data.into_iter()).collect_vec()
    };

    PcsDataEncoded {
        point_computations,
        vanishing_computations,
        coeff_computations,
        normalized_coeff_computations,
        r_evals_computations,
        coeff_sums_computation,
        r_eval_computations,
        pairing_input_computations,
    }
}
