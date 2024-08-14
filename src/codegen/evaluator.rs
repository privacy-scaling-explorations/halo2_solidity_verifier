#![allow(clippy::useless_format)]

use crate::codegen::util::{code_block, fe_to_u256, ConstraintSystemMeta, Data};
use halo2_proofs::{
    halo2curves::ff::PrimeField,
    plonk::{
        Advice, AdviceQuery, Any, Challenge, ConstraintSystem, Expression, Fixed, FixedQuery, Gate,
        InstanceQuery,
    },
};
use itertools::{chain, izip, Itertools};
use ruint::aliases::U256;
use ruint::Uint;
use std::{cell::RefCell, cmp::Ordering, collections::HashMap, iter};

use super::util::{Ptr, Word};

#[derive(Debug)]
pub(crate) struct EvaluatorStatic<'a, F: PrimeField> {
    cs: &'a ConstraintSystem<F>,
    meta: &'a ConstraintSystemMeta,
    data: &'a Data,
    var_counter: RefCell<usize>,
    var_cache: RefCell<HashMap<String, String>>,
}

impl<'a, F> EvaluatorStatic<'a, F>
where
    F: PrimeField<Repr = [u8; 0x20]>,
{
    pub(crate) fn new(
        cs: &'a ConstraintSystem<F>,
        meta: &'a ConstraintSystemMeta,
        data: &'a Data,
    ) -> Self {
        Self {
            cs,
            meta,
            data,
            var_counter: Default::default(),
            var_cache: Default::default(),
        }
    }

    pub fn gate_computations(&self) -> Vec<(Vec<String>, String)> {
        self.cs
            .gates()
            .iter()
            .flat_map(Gate::polynomials)
            .map(|expression| self.evaluate_and_reset(expression))
            .collect()
    }

    pub fn permutation_computations(&self) -> Vec<(Vec<String>, String)> {
        let Self { meta, data, .. } = self;
        let last_chunk_idx = meta.num_permutation_zs - 1;
        chain![
            data.permutation_z_evals.first().map(|(z, _, _)| {
                vec![
                    format!("let l_0 := mload(L_0_MPTR)"),
                    format!("let eval := addmod(l_0, sub(R, mulmod(l_0, {z}, R)), R)"),
                ]
            }),
            data.permutation_z_evals.last().map(|(z, _, _)| {
                let item = "addmod(mulmod(perm_z_last, perm_z_last, R), sub(R, perm_z_last), R)";
                vec![
                    format!("let perm_z_last := {z}"),
                    format!("let eval := mulmod(mload(L_LAST_MPTR), {item}, R)"),
                ]
            }),
            data.permutation_z_evals.iter().tuple_windows().map(
                |((_, _, z_i_last), (z_j, _, _))| {
                    let item = format!("addmod({z_j}, sub(R, {z_i_last}), R)");
                    vec![format!("let eval := mulmod(mload(L_0_MPTR), {item}, R)")]
                }
            ),
            izip!(
                meta.permutation_columns.chunks(meta.permutation_chunk_len),
                &data.permutation_z_evals,
            )
            .enumerate()
            .map(|(chunk_idx, (columns, evals))| {
                let last_column_idx = columns.len() - 1;
                chain![
                    [
                        format!("let gamma := mload({})", "GAMMA_MPTR"),
                        format!("let beta := mload({})", "BETA_MPTR"),
                        format!("let lhs := {}", evals.1),
                        format!("let rhs := {}", evals.0),
                    ],
                    columns.iter().flat_map(|column| {
                        let perm_eval = &data.permutation_evals[column];
                        let eval = self.eval(*column.column_type(), column.index(), 0);
                        let item = format!("mulmod(beta, {perm_eval}, R)");
                        [format!(
                            "lhs := mulmod(lhs, addmod(addmod({eval}, {item}, R), gamma, R), R)"
                        )]
                    }),
                    (chunk_idx == 0)
                        .then(|| format!("mstore(0x00, mulmod(beta, mload({}), R))", "X_MPTR")),
                    columns.iter().enumerate().flat_map(|(idx, column)| {
                        let eval = self.eval(*column.column_type(), column.index(), 0);
                        let item = format!("addmod(addmod({eval}, mload(0x00), R), gamma, R)");
                        chain![
                            [format!("rhs := mulmod(rhs, {item}, R)")],
                            (!(chunk_idx == last_chunk_idx && idx == last_column_idx))
                                .then(|| "mstore(0x00, mulmod(mload(0x00), DELTA, R))".to_string()),
                        ]
                    }),
                    {
                        let item = format!("addmod(mload(L_LAST_MPTR), mload(L_BLIND_MPTR), R)");
                        let item = format!("sub(R, mulmod(left_sub_right, {item}, R))");
                        [
                            format!("let left_sub_right := addmod(lhs, sub(R, rhs), R)"),
                            format!("let eval := addmod(left_sub_right, {item}, R)"),
                        ]
                    }
                ]
                .collect_vec()
            })
        ]
        .zip(iter::repeat("eval".to_string()))
        .collect()
    }

    #[cfg(feature = "mv-lookup")]
    pub fn lookup_computations(&self) -> Vec<(Vec<String>, String)> {
        let evaluate = |expressions: &Vec<_>| {
            // println!("expressions: {:?}", expressions);
            let (lines, inputs) = expressions
                .iter()
                .map(|expression| self.evaluate(expression))
                .fold((Vec::new(), Vec::new()), |mut acc, result| {
                    acc.0.extend(result.0);
                    acc.1.push(result.1);
                    acc
                });
            self.reset();
            (lines, inputs)
        };

        let inputs_tables = self
            .cs
            .lookups()
            .iter()
            .map(|lookup| {
                let inputs_iter = lookup.input_expressions().iter();
                let inputs = inputs_iter.clone().map(evaluate).collect_vec();
                let table = evaluate(lookup.table_expressions());
                (inputs, table)
            })
            .collect_vec();

        let vec = izip!(inputs_tables, &self.data.lookup_evals)
            .flat_map(|(inputs_tables, evals)| {
                let (inputs, (table_lines, tables)) = inputs_tables.clone();
                let num_inputs = inputs.len();
                let (table_0, rest_tables) = tables.split_first().unwrap();
                let (phi, phi_next, m) = evals;
                [
                    vec![
                        format!("let l_0 := mload(L_0_MPTR)"),
                        format!("let eval := mulmod(l_0, {phi}, R)"),
                    ],
                    vec![
                        format!("let l_last := mload(L_LAST_MPTR)"),
                        format!("let eval := mulmod(l_last, {phi}, R)"),
                    ],
                    chain![
                        [
                            format!("let theta := mload({})", "THETA_MPTR").as_str(),
                            format!("let beta := mload({})", "BETA_MPTR").as_str(),
                            "let table"
                        ]
                        .map(str::to_string),
                        code_block::<1, false>(chain![
                            table_lines,
                            [format!("table := {table_0}")],
                            rest_tables.iter().map(|table| format!(
                                "table := addmod(mulmod(table, theta, R), {table}, R)"
                            )),
                            [format!("table := addmod(table, beta, R)")],
                        ]),
                        izip!(0.., inputs.into_iter()).flat_map(|(idx, (input_lines, inputs))| {
                            let (input_0, rest_inputs) = inputs.split_first().unwrap();
                            let ident = format!("input_{idx}");
                            chain![
                                [format!("let {ident}")],
                                code_block::<1, false>(chain![
                                    input_lines,
                                    [format!("{ident} := {input_0}")],
                                    rest_inputs.iter().map(|input| format!(
                                        "{ident} := addmod(mulmod({ident}, theta, R), {input}, R)"
                                    )),
                                    [format!("{ident} := addmod({ident}, beta, R)")],
                                ]),
                            ]
                        }),
                        [format!("let lhs"), format!("let rhs")],
                        (0..num_inputs).flat_map(|i| {
                            assert_ne!(num_inputs, 0);
                            if num_inputs == 1 {
                                vec![format!("rhs := table")]
                            } else {
                                let idents = (0..num_inputs)
                                    .filter(|j| *j != i)
                                    .map(|idx| format!("input_{idx}"))
                                    .collect_vec();
                                let (ident_0, rest_idents) = idents.split_first().unwrap();
                                code_block::<1, false>(chain![
                                    [format!("let tmp := {ident_0}")],
                                    chain![rest_idents]
                                        .map(|ident| format!("tmp := mulmod(tmp, {ident}, R)")),
                                    [format!("rhs := addmod(rhs, tmp, R)"),],
                                    (i == num_inputs - 1)
                                        .then(|| format!("rhs := mulmod(rhs, table, R)")),
                                ])
                            }
                        }),
                        code_block::<1, false>(chain![
                            [format!("let tmp := input_0")],
                            (1..num_inputs)
                                .map(|idx| format!("tmp := mulmod(tmp, input_{idx}, R)")),
                            [
                                format!("rhs := addmod(rhs, sub(R, mulmod({m}, tmp, R)), R)"),
                                {
                                    let item = format!("addmod({phi_next}, sub(R, {phi}), R)");
                                    format!("lhs := mulmod(mulmod(table, tmp, R), {item}, R)")
                                },
                            ],
                        ]),
                        {
                            let l_inactive =
                                format!("addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)");
                            let l_active = format!("addmod(1, sub(R, {l_inactive}), R)");
                            [format!(
                                "let eval := mulmod({l_active}, addmod(lhs, sub(R, rhs), R), R)"
                            )]
                        },
                    ]
                    .collect_vec(),
                ]
            })
            .zip(iter::repeat("eval".to_string()))
            .collect_vec();
        vec
    }

    #[cfg(not(feature = "mv-lookup"))]
    pub fn lookup_computations(&self) -> Vec<(Vec<String>, String)> {
        let input_tables = self
            .cs
            .lookups()
            .iter()
            .map(|lookup| {
                let [(input_lines, inputs), (table_lines, tables)] =
                    [lookup.input_expressions(), lookup.table_expressions()].map(|expressions| {
                        let (lines, inputs) = expressions
                            .iter()
                            .map(|expression| self.evaluate(expression))
                            .fold((Vec::new(), Vec::new()), |mut acc, result| {
                                acc.0.extend(result.0);
                                acc.1.push(result.1);
                                acc
                            });
                        self.reset();
                        (lines, inputs)
                    });
                (input_lines, inputs, table_lines, tables)
            })
            .collect_vec();
        let vec = izip!(input_tables, &self.data.lookup_evals)
            .flat_map(|(input_table, evals)| {
                let (input_lines, inputs, table_lines, tables) = input_table;
                let (input_0, rest_inputs) = inputs.split_first().unwrap();
                let (table_0, rest_tables) = tables.split_first().unwrap();
                let (z, z_next, p_input, p_input_prev, p_table) = evals;
                [
                    vec![
                        format!("let l_0 := mload(L_0_MPTR)"),
                        format!("let eval := addmod(l_0, mulmod(l_0, sub(r, {z}), r), r)"),
                    ],
                    {
                        let item = format!("addmod(mulmod({z}, {z}, r), sub(r, {z}), r)");
                        vec![
                            format!("let l_last := mload(L_LAST_MPTR)"),
                            format!("let eval := mulmod(l_last, {item}, r)"),
                        ]
                    },
                    chain![
                        ["let theta := mload(THETA_MPTR)", "let input"].map(str::to_string),
                        code_block::<1, false>(chain![
                            input_lines,
                            [format!("input := {input_0}")],
                            rest_inputs.iter().map(|input| format!(
                                "input := addmod(mulmod(input, theta, r), {input}, r)"
                            ))
                        ]),
                        ["let table"].map(str::to_string),
                        code_block::<1, false>(chain![
                            table_lines,
                            [format!("table := {table_0}")],
                            rest_tables.iter().map(|table| format!(
                                "table := addmod(mulmod(table, theta, r), {table}, r)"
                            ))
                        ]),
                        {
                            let lhs = format!("addmod({p_input}, beta, r)");
                            let rhs = format!("addmod({p_table}, gamma, r)");
                            let permuted = format!("mulmod({lhs}, {rhs}, r)");
                            let input =
                                "mulmod(addmod(input, beta, r), addmod(table, gamma, r), r)";
                            [
                                format!("let beta := mload(BETA_MPTR)"),
                                format!("let gamma := mload(GAMMA_MPTR)"),
                                format!("let lhs := mulmod({z_next}, {permuted}, r)"),
                                format!("let rhs := mulmod({z}, {input}, r)"),
                            ]
                        },
                        {
                            let l_inactive = "addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), r)";
                            let l_active = format!("addmod(1, sub(r, {l_inactive}), r)");
                            [format!(
                                "let eval := mulmod({l_active}, addmod(lhs, sub(r, rhs), r), r)"
                            )]
                        },
                    ]
                    .collect_vec(),
                    {
                        let l_0 = "mload(L_0_MPTR)";
                        let item = format!("addmod({p_input}, sub(r, {p_table}), r)");
                        vec![format!("let eval := mulmod({l_0}, {item}, r)")]
                    },
                    {
                        let l_inactive = "addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), r)";
                        let l_active = format!("addmod(1, sub(r, {l_inactive}), r)");
                        let lhs = format!("addmod({p_input}, sub(r, {p_table}), r)");
                        let rhs = format!("addmod({p_input}, sub(r, {p_input_prev}), r)");
                        vec![format!(
                            "let eval := mulmod({l_active}, mulmod({lhs}, {rhs}, r), r)"
                        )]
                    },
                ]
            })
            .zip(iter::repeat("eval".to_string()))
            .collect_vec();
        vec
    }

    fn eval(&self, column_type: impl Into<Any>, column_index: usize, rotation: i32) -> String {
        match column_type.into() {
            Any::Advice(_) => self.data.advice_evals[&(column_index, rotation)].to_string(),
            Any::Fixed => self.data.fixed_evals[&(column_index, rotation)].to_string(),
            Any::Instance => self.data.instance_eval.to_string(),
        }
    }

    fn reset(&self) {
        *self.var_counter.borrow_mut() = Default::default();
        *self.var_cache.borrow_mut() = Default::default();
    }

    fn evaluate_and_reset(&self, expression: &Expression<F>) -> (Vec<String>, String) {
        let result = self.evaluate(expression);
        self.reset();
        result
    }

    fn evaluate(&self, expression: &Expression<F>) -> (Vec<String>, String) {
        evaluate(
            expression,
            &|constant| {
                let constant = u256_string(constant);
                self.init_var(constant, None)
            },
            &|query| {
                self.init_var(
                    self.eval(Fixed, query.column_index(), query.rotation().0),
                    Some(fixed_eval_var(query)),
                )
            },
            &|query| {
                self.init_var(
                    self.eval(Advice::default(), query.column_index(), query.rotation().0),
                    Some(advice_eval_var(query)),
                )
            },
            &|_| self.init_var(self.data.instance_eval, Some("i_eval".to_string())),
            &|challenge| {
                self.init_var(
                    self.data.challenges[challenge.index()],
                    Some(format!("c_{}", challenge.index())),
                )
            },
            &|(mut acc, var)| {
                let (lines, var) = self.init_var(format!("sub(R, {var})"), None);
                acc.extend(lines);
                (acc, var)
            },
            &|(mut lhs_acc, lhs_var), (rhs_acc, rhs_var)| {
                let (lines, var) = self.init_var(format!("addmod({lhs_var}, {rhs_var}, R)"), None);
                lhs_acc.extend(rhs_acc);
                lhs_acc.extend(lines);
                (lhs_acc, var)
            },
            &|(mut lhs_acc, lhs_var), (rhs_acc, rhs_var)| {
                let (lines, var) = self.init_var(format!("mulmod({lhs_var}, {rhs_var}, R)"), None);
                lhs_acc.extend(rhs_acc);
                lhs_acc.extend(lines);
                (lhs_acc, var)
            },
            &|(mut acc, var), scalar| {
                let scalar = u256_string(scalar);
                let (lines, var) = self.init_var(format!("mulmod({var}, {scalar}, R)"), None);
                acc.extend(lines);
                (acc, var)
            },
        )
    }

    fn init_var(&self, value: impl ToString, var: Option<String>) -> (Vec<String>, String) {
        let value = value.to_string();
        if self.var_cache.borrow().contains_key(&value) {
            (vec![], self.var_cache.borrow()[&value].clone())
        } else {
            let var = var.unwrap_or_else(|| self.next_var());
            self.var_cache
                .borrow_mut()
                .insert(value.clone(), var.clone());
            (vec![format!("let {var} := {value}")], var)
        }
    }

    fn next_var(&self) -> String {
        let count = *self.var_counter.borrow();
        *self.var_counter.borrow_mut() += 1;
        format!("var{count}")
    }
}

// Define an enum which catagorizes the operand memory location:
// calldata_mptr
// constant_mptr
// instance_mptr
// chllenge_mptr
// static_memory_ptr
#[derive(Clone, PartialEq, Eq)]
pub enum OperandMem {
    Calldata,
    Constant,
    Instance,
    Challenge,
    StaticMemory,
}

// Holds the encoded data stored in the separate VK
// needed to perform the gate computations of
// the quotient evaluation portion of the reusable verifier.
#[derive(Clone, PartialEq, Eq, Default)]
pub struct GateDataEncoded {
    pub(crate) length: usize,
    pub(crate) packed_expression_words: Vec<U256>,
}

impl GateDataEncoded {
    pub fn len(&self) -> usize {
        if self == &Self::default() {
            0
        } else {
            1 + self.packed_expression_words.len()
        }
    }
}

// Holds the encoded data stored in the separate VK
// needed to perform the permutation computations of
// the quotient evaluation portion of the reusable verifier.
#[derive(Clone, PartialEq, Eq)]
pub struct PermutationDataEncoded {
    pub(crate) permutation_meta_data: U256,
    pub(crate) permutation_data: Vec<U256>,
}

impl Default for PermutationDataEncoded {
    fn default() -> Self {
        PermutationDataEncoded {
            permutation_meta_data: U256::from(0),
            permutation_data: Vec::new(),
        }
    }
}

impl PermutationDataEncoded {
    pub fn len(&self) -> usize {
        if self == &Self::default() {
            0
        } else {
            1 + self.permutation_data.len()
        }
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct InputsEncoded {
    pub(crate) expression: Vec<U256>,
    pub(crate) vars: U256,
    pub(crate) acc: usize,
}

// Holds the encoded data stored in the separate VK
// needed to perform the lookup computations for one lookup table
// in the quotient evaluation portion of the reusable verifier.
#[derive(Clone, PartialEq, Eq)]
pub struct LookupEncoded {
    pub(crate) evals: U256,
    pub(crate) table_lines: Vec<U256>,
    pub(crate) table_inputs: Option<U256>,
    pub(crate) acc: usize,
    pub(crate) inputs: Vec<InputsEncoded>,
}

// For each element of the lookups vector we have a word for:
// 1) the evals (cptr, cptr, cptr),
// 2) table_lines Vec<packed_expressions>
// 3) table_inputs Vec<mptr> packed into a single (throws an error if table_inputs.len() > 16)
// 4) outer_inputs_len (inputs.0.len())
// For each element of the inputs vector in LookupEncoded we have a word for:
// 1) inputs (inputs[i].expressions)
// 2) input_vars Vec<mptr> packed into a single (throws an error if > 16)
// Then we have a word for each step in the expression evaluation. This is the
// sum of the lengths of the inputs.
impl LookupEncoded {
    pub fn len(&self) -> usize {
        let base_len = if self.table_inputs.is_none() {
            1 // Add 2 if table_inputs is none
        } else {
            2 // Add 3 otherwise
        };
        base_len
            + (self.inputs.len())
            + self
                .inputs
                .iter()
                .map(|inputs| inputs.expression.len())
                .sum::<usize>()
            + self.table_lines.len()
    }
}

// Holds the encoded data stored in the separate VK
// needed to perform the lookup computations of all the lookup tables
// needed in the quotient evaluation portion of the reusable verifier.
#[derive(Clone, PartialEq, Eq)]
pub struct LookupsDataEncoded {
    pub(crate) meta_data: U256,
    pub(crate) lookups: Vec<LookupEncoded>,
}

impl Default for LookupsDataEncoded {
    fn default() -> Self {
        LookupsDataEncoded {
            meta_data: U256::from(0),
            lookups: Vec::new(),
        }
    }
}

impl LookupsDataEncoded {
    pub fn len(&self) -> usize {
        if self == &Self::default() {
            1
        } else {
            1 + self.lookups.iter().map(LookupEncoded::len).sum::<usize>()
        }
    }
}

#[derive(Debug)]
pub(crate) struct EvaluatorDynamic<'a, F: PrimeField> {
    cs: &'a ConstraintSystem<F>,
    meta: &'a ConstraintSystemMeta,
    data: &'a Data,
    static_mem_ptr: RefCell<usize>,
    encoded_var_cache: RefCell<HashMap<U256, U256>>,
    const_cache: RefCell<HashMap<ruint::Uint<256, 4>, Ptr>>,
}

impl<'a, F> EvaluatorDynamic<'a, F>
where
    F: PrimeField<Repr = [u8; 0x20]>,
{
    pub(crate) fn new(
        cs: &'a ConstraintSystem<F>,
        meta: &'a ConstraintSystemMeta,
        data: &'a Data,
        const_cache: HashMap<ruint::Uint<256, 4>, Ptr>,
    ) -> Self {
        Self {
            cs,
            meta,
            data,
            static_mem_ptr: RefCell::new(0x00),
            encoded_var_cache: Default::default(),
            const_cache: RefCell::new(const_cache),
        }
    }

    pub fn gate_computations(&self) -> GateDataEncoded {
        let packed_expression_words: Vec<Vec<U256>> = self
            .cs
            .gates()
            .iter()
            .flat_map(Gate::polynomials)
            .map(|expression| self.evaluate_and_reset(expression, true))
            .collect();
        let length = packed_expression_words.len();
        let packed_expression_words_flattened: Vec<U256> =
            packed_expression_words.into_iter().flatten().collect();

        GateDataEncoded {
            length,
            packed_expression_words: packed_expression_words_flattened,
        }
    }

    #[allow(dead_code)]
    fn gate_computation_fsm_usage(&self) -> usize {
        let packed_expression_words: Vec<Vec<U256>> = self
            .cs
            .gates()
            .iter()
            .flat_map(Gate::polynomials)
            .map(|expression| self.evaluate_and_reset(expression, false))
            .collect();
        let gate_computation_longest = chain![packed_expression_words]
            .max_by_key(|x| x.len())
            .unwrap()
            .clone()
            .len();
        gate_computation_longest * 0x20
    }

    pub fn permutation_computations(&self) -> PermutationDataEncoded {
        let Self { meta, data, .. } = self;
        let permutation_z_evals_last_idx = data.permutation_z_evals.len() - 1;
        let permutation_z_evals: Vec<U256> = data
            .permutation_z_evals
            .iter()
            .map(|z| self.encode_triplet_evaluation_word(z))
            .collect();
        let column_evals: Vec<Vec<U256>> = meta
            .permutation_columns
            .chunks(meta.permutation_chunk_len)
            .map(|columns| {
                columns
                    .iter()
                    .map(|column| {
                        let perm_eval =
                            U256::from(data.permutation_evals[column].ptr().value().as_usize());
                        let eval = self.eval_encoded(*column.column_type(), column.index(), 0);
                        eval | (perm_eval << 24)
                    })
                    .collect()
            })
            .collect();
        // num words each set of permutation data will take up (except the last one) scaled by 0x20
        // 48 is the bit offset of the permutation_z_evals and 40 is the bit offset of each column eval.
        let num_words = 1 + ((48 + (meta.permutation_chunk_len) * 40) / 256);
        let perm_meta_data: U256 = {
            let mut packed_word = U256::from(permutation_z_evals_last_idx);
            packed_word |= U256::from(num_words * 0x20) << 8;
            let last_num_words = 1 + ((48 + (column_evals.last().unwrap().len()) * 40) / 256);
            packed_word |= U256::from(last_num_words * 0x20) << 24;
            packed_word
        };
        let perm_data: Vec<U256> = izip!(0.., column_evals)
            .flat_map(|(chunk_idx, column_evals)| {
                let mut packed_words = vec![permutation_z_evals[chunk_idx]];
                let mut last_idx = 0;
                let mut bit_counter = 48;
                for eval in column_evals.iter() {
                    let next_bit_counter = bit_counter + 40;
                    if next_bit_counter > 256 {
                        last_idx += 1;
                        packed_words.push(U256::from(0));
                        bit_counter = 0;
                    }
                    packed_words[last_idx] |= *eval << bit_counter;
                    bit_counter += 40;
                }
                packed_words
            })
            .collect_vec();
        PermutationDataEncoded {
            permutation_meta_data: perm_meta_data,
            permutation_data: perm_data,
        }
    }

    #[cfg(not(feature = "mv-lookup"))]
    pub fn quotient_eval_fsm_usage(&self) -> usize {
        unimplemented!(
            "quotient_eval_fsm_usage function is not implemented for the non mv-lookup version of the verifier"
        );
        // let gate_computation_fsm_usage = self.gate_computation_fsm_usage();

        // let permutation_computation_fsm_usage = (self.data.permutation_z_evals.len() * 0x20) + 0x40;

        // // TODO implement the non mv lookup version of this calculation.
        // let input_expressions_fsm_usage = 0;

        // itertools::max([
        //     gate_computation_fsm_usage,
        //     permutation_computation_fsm_usage,
        //     input_expressions_fsm_usage,
        // ])
        // .unwrap()
    }

    #[cfg(feature = "mv-lookup")]
    pub fn quotient_eval_fsm_usage(&self) -> usize {
        let gate_computation_fsm_usage = self.gate_computation_fsm_usage();

        // 0x40 offset b/c that is where the fsm pointer starts in the permutations computation code block
        let permutation_computation_fsm_usage = (self.data.permutation_z_evals.len() * 0x20) + 0x40;

        let evaluate_fsm_usage = |idx: usize, expressions: &Vec<_>| {
            let offset = 0xa0; // offset to store theta offset ptrs used
                               // in the lookup computations.
            let fsm = (0x20 * idx) + offset;
            self.set_static_mem_ptr(fsm);
            let max_fsm_usage = expressions
                .iter()
                .map(|expression| self.evaluate_encode(expression))
                .fold(fsm, |mut acc, result| {
                    acc += result.0.len() * 0x20;
                    acc
                });
            self.reset();
            max_fsm_usage
        };

        let input_expressions_fsm_usage = self
            .cs
            .lookups()
            .iter()
            .map(|lookup| {
                let inputs_iter = lookup.input_expressions().iter().enumerate();
                let fsm_usages = inputs_iter
                    .clone()
                    .map(|(idx, expressions)| evaluate_fsm_usage(idx, expressions))
                    .collect_vec();
                *fsm_usages.iter().max().unwrap()
            })
            .collect_vec();
        let input_expressions_fsm_usage = *input_expressions_fsm_usage.iter().max().unwrap_or(&0x0);

        itertools::max([
            gate_computation_fsm_usage,
            permutation_computation_fsm_usage,
            input_expressions_fsm_usage,
        ])
        .unwrap()
    }

    #[cfg(feature = "mv-lookup")]
    pub fn lookup_computations(&self, offset: usize) -> LookupsDataEncoded {
        let evaluate_table = |expressions: &Vec<_>| {
            let offset = 0xa0; // offset to store theta offset ptrs used
            self.set_static_mem_ptr(offset); // println!("expressions: {:?}", expressions);
            let (lines, inputs) = expressions
                .iter()
                .map(|expression| self.evaluate_encode(expression))
                .fold((Vec::new(), Vec::new()), |mut acc, result| {
                    acc.0.extend(result.0);
                    acc.1.push(result.1);
                    acc
                });
            assert!(inputs.len() <= 16);
            self.reset();
            let lines_packed = self.encode_pack_expr_operations(lines, 8);
            (lines_packed, inputs)
        };

        let evaluate_inputs = |idx: usize, expressions: &Vec<_>| {
            // println!("expressions: {:?}", expressions);
            let offset = 0xa0; // offset to store theta offset ptrs used
                               // in the lookup computations.
            let fsm = (0x20 * idx) + offset;
            self.set_static_mem_ptr(fsm);
            let (lines, inputs) = expressions
                .iter()
                .map(|expression| self.evaluate_encode(expression))
                .fold((Vec::new(), Vec::new()), |mut acc, result| {
                    acc.0.extend(result.0);
                    acc.1.push(result.1);
                    acc
                });
            self.reset();
            // bit offset to store the number of inputs
            let bit_offset = if idx == 0 { 24 } else { 8 };
            let lines_packed = self.encode_pack_expr_operations(lines, bit_offset);
            (lines_packed, inputs)
        };

        let inputs_tables = self
            .cs
            .lookups()
            .iter()
            .map(|lookup| {
                let inputs_iter = lookup.input_expressions().iter().enumerate();
                // outer inputs of the MV lookup vector scaled by 0x20.
                let outer_inputs_len = lookup.input_expressions().len() * 0x20;
                let inputs = inputs_iter
                    .clone()
                    .map(|(idx, expressions)| {
                        let (mut lines, inputs) = evaluate_inputs(idx, expressions);
                        if idx == 0 {
                            lines[0] |= U256::from(outer_inputs_len);
                        }
                        (lines, inputs)
                    })
                    .collect_vec();
                let table = evaluate_table(lookup.table_expressions());
                (inputs, table)
            })
            .collect_vec();

        let mut accumulator = 0;

        let mut previous_table_lines: Option<Vec<Uint<256, 4>>> = None;

        // Ensure that the number of inputs tables is less than 30 otherwise we won't be able to
        // pack all of the shared input table expressions into the meta data.
        assert!(inputs_tables.len() <= 30);

        // meta_data will encode the subsequence_indices as a bitmask, where each byte will store
        // whether we use the previous table lines or not. If we use the previous table lines then
        // the byte will be 0x0 otherwise it will be 0x1.
        let mut meta_data = U256::from(0);
        let lookups: Vec<LookupEncoded> = izip!(inputs_tables, &self.data.lookup_evals)
            .enumerate() // Add enumeration to track indices
            .map(|(index, (inputs_tables, evals))| {
                let (inputs, (table_lines, table_inputs)) = inputs_tables.clone();
                let evals = self.encode_triplet_evaluation_word(evals);
                let table_inputs = Some(self.encode_pack_ptrs(&table_inputs).unwrap());
                let mut inner_accumulator = 0;
                let inputs: Vec<InputsEncoded> = inputs
                    .iter()
                    .map(|(input_lines, inputs)| {
                        let inputs = self.encode_pack_ptrs(inputs).unwrap();
                        let res = InputsEncoded {
                            expression: input_lines.clone(),
                            vars: inputs,
                            acc: inner_accumulator,
                        };
                        inner_accumulator += input_lines.len() + 1;
                        res
                    })
                    .collect_vec();

                let mut lookup_encoded = LookupEncoded {
                    evals,
                    table_lines: table_lines.clone(),
                    table_inputs,
                    inputs: inputs.clone(),
                    acc: accumulator,
                };

                // bit offset to store the end_ptr
                let offset = 16;

                // Handle subsequence indexing logic
                if let Some(prev_lines) = &previous_table_lines {
                    if *prev_lines != table_lines {
                        meta_data |= U256::from(0x1) << ((index * 8) + offset);
                    } else {
                        lookup_encoded.table_lines = Vec::new();
                        lookup_encoded.table_inputs = None;
                    }
                } else {
                    meta_data |= U256::from(0x1) << ((index * 8) + offset);
                }

                accumulator += lookup_encoded.len();

                previous_table_lines = Some(table_lines);
                lookup_encoded
            })
            .collect_vec();

        let mut data = LookupsDataEncoded { lookups, meta_data };
        // Insert the end_ptr to the beginning of the meta data word.
        data.meta_data |= U256::from((data.len() * 32) + offset);
        data
    }

    #[cfg(not(feature = "mv-lookup"))]
    pub fn lookup_computations(&self, offset: usize) -> LookupsDataEncoded {
        unimplemented!(
            "Lookup_computations function is not implemented for the non mv-lookup version of the verifier"
        );
        // // TODO implement non mv lookup version of this
        // LookupsDataEncoded::default()
    }

    fn eval_encoded(
        &self,
        column_type: impl Into<Any>,
        column_index: usize,
        rotation: i32,
    ) -> U256 {
        match column_type.into() {
            Any::Advice(_) => self.encode_single_operand(
                0_u8,
                U256::from(
                    self.data.advice_evals[&(column_index, rotation)]
                        .ptr()
                        .value()
                        .as_usize(),
                ),
            ),
            Any::Fixed => self.encode_single_operand(
                0_u8,
                U256::from(
                    self.data.fixed_evals[&(column_index, rotation)]
                        .ptr()
                        .value()
                        .as_usize(),
                ),
            ),
            Any::Instance => self.encode_single_operand(1_u8, U256::from(0)), // On the EVM side the 0x0 op here we will inidicate that we need to perform the l_0 mload operation.
        }
    }

    // TODO: optimiize this by maintaing a cache of previous var stored in static memory and if
    // any of the steps require the same var then just return the pointer to the var instead of encoding it again

    fn reset(&self) {
        *self.static_mem_ptr.borrow_mut() = 0x0;
        *self.encoded_var_cache.borrow_mut() = Default::default();
    }

    fn encode_operation(&self, op: u8, lhs_ptr: U256, rhs_ptr: U256) -> U256 {
        U256::from(op) | (lhs_ptr << 8) | (rhs_ptr << 24)
    }

    fn encode_single_operand(&self, op: u8, ptr: U256) -> U256 {
        U256::from(op) | (ptr << 8)
    }

    fn encode_triplet_evaluation_word(&self, value: &(Word, Word, Word)) -> U256 {
        let (z_i, z_j, z_i_last) = value;
        U256::from(z_i.ptr().value().as_usize())
            | U256::from(z_j.ptr().value().as_usize() << 16)
            | U256::from(z_i_last.ptr().value().as_usize() << 32)
    }

    // pack as many as 16 ptrs into a single word
    // throws an error if the number of ptrs is greater than 16
    fn encode_pack_ptrs(&self, ptrs: &[U256]) -> Result<U256, &'static str> {
        if ptrs.len() > 16 {
            return Err("Number of pointers cannot be greater than 16");
        }

        let mut packed = U256::from(0);
        for (i, ptr) in ptrs.iter().enumerate() {
            packed |= *ptr << (i * 16);
        }
        Ok(packed)
    }

    fn encode_pack_expr_operations(&self, exprs: Vec<U256>, mut bit_counter: i32) -> Vec<U256> {
        let mut packed_words: Vec<U256> = vec![U256::from(0)];
        let mut last_idx = 0;
        let initial_offset = bit_counter;

        for expr in exprs.iter() {
            let first_byte = expr.as_limbs()[0] & 0xFF;
            let offset = if first_byte == 0 || first_byte == 1 {
                24
            } else {
                40
            };

            let mut next_bit_counter = bit_counter + offset;
            if next_bit_counter > 256 {
                last_idx += 1;
                packed_words.push(U256::from(0));
                next_bit_counter = offset;
                packed_words[last_idx] = *expr
            } else {
                packed_words[last_idx] |= *expr << bit_counter;
            }
            bit_counter = next_bit_counter;
        }

        let packed_words_len = packed_words.len();

        // Encode the length of the exprs vec in the first word
        let offset = if initial_offset == 24 { 16 } else { 0 };
        packed_words[0] |= U256::from(packed_words_len) << offset;

        packed_words
    }

    fn evaluate_and_reset(&self, expression: &Expression<F>, pack: bool) -> Vec<U256> {
        *self.static_mem_ptr.borrow_mut() = 0x0;
        let result = self.evaluate_encode(expression);
        self.reset();
        let res = result.0;
        if pack {
            self.encode_pack_expr_operations(res, 8)
        } else {
            res
        }
    }

    fn set_static_mem_ptr(&self, value: usize) {
        *self.static_mem_ptr.borrow_mut() = value;
    }

    fn evaluate_encode(&self, expression: &Expression<F>) -> (Vec<U256>, U256) {
        evaluate(
            expression,
            &|constant| self.init_encoded_var(constant, OperandMem::Constant),
            &|query| {
                self.init_encoded_var(
                    self.eval_encoded(Fixed, query.column_index(), query.rotation().0),
                    OperandMem::Calldata,
                )
            },
            &|query| {
                self.init_encoded_var(
                    self.eval_encoded(Advice::default(), query.column_index(), query.rotation().0),
                    OperandMem::Calldata,
                )
            },
            &|_| {
                self.init_encoded_var(
                    // instance eval ptr located 17 words after the theta mptr
                    U256::from((self.data.theta_mptr + 17).value().as_usize()),
                    OperandMem::Instance,
                )
            },
            &|challenge| {
                self.init_encoded_var(
                    U256::from(
                        self.data.challenges[challenge.index()]
                            .ptr()
                            .value()
                            .as_usize(),
                    ),
                    OperandMem::Challenge,
                )
            },
            &|(mut acc, var)| {
                let (lines, var) = self.init_encoded_var(
                    self.encode_single_operand(1_u8, var),
                    OperandMem::StaticMemory,
                );
                acc.extend(lines);
                (acc, var)
            },
            &|(mut lhs_acc, lhs_var), (rhs_acc, rhs_var)| {
                let (lines, var) = self.init_encoded_var(
                    self.encode_operation(2_u8, lhs_var, rhs_var),
                    OperandMem::StaticMemory,
                );
                lhs_acc.extend(rhs_acc);
                lhs_acc.extend(lines);
                (lhs_acc, var)
            },
            &|(mut lhs_acc, lhs_var), (rhs_acc, rhs_var)| {
                let (lines, var) = self.init_encoded_var(
                    self.encode_operation(3_u8, lhs_var, rhs_var),
                    OperandMem::StaticMemory,
                );
                lhs_acc.extend(rhs_acc);
                lhs_acc.extend(lines);
                (lhs_acc, var)
            },
            &|(mut acc, var), scalar| {
                // fetch the scalar pointer from the const cache
                let scalar_ptr = self.const_cache.borrow()[&scalar];
                let (lines, var) = self.init_encoded_var(
                    self.encode_operation(3_u8, var, U256::from(scalar_ptr.value().as_usize())),
                    OperandMem::StaticMemory,
                );
                acc.extend(lines);
                (acc, var)
            },
        )
    }

    // Return the encoded word and the static memory pointer
    fn init_encoded_var(&self, value: U256, var: OperandMem) -> (Vec<U256>, U256) {
        match var {
            OperandMem::Calldata | OperandMem::StaticMemory => {
                if self.encoded_var_cache.borrow().contains_key(&value) {
                    (vec![], self.encoded_var_cache.borrow()[&value])
                } else {
                    let var = self.next_encoded_var();
                    self.encoded_var_cache.borrow_mut().insert(value, var);
                    (vec![value], var)
                }
            }
            OperandMem::Constant => (
                vec![],
                U256::from(self.const_cache.borrow().get(&value).map_or_else(
                    || {
                        println!("Key not found: {}", value);
                        0 // Default value, you can change this if needed
                    },
                    |entry| entry.value().as_usize(),
                )),
            ),
            OperandMem::Instance | OperandMem::Challenge => (vec![], value),
        }
    }

    fn next_encoded_var(&self) -> U256 {
        let count = *self.static_mem_ptr.borrow();
        *self.static_mem_ptr.borrow_mut() += 0x20;
        U256::from(count)
    }
}

fn u256_string(value: U256) -> String {
    if value.bit_len() < 64 {
        format!("0x{:x}", value.as_limbs()[0])
    } else {
        format!("0x{value:x}")
    }
}

fn fixed_eval_var(fixed_query: FixedQuery) -> String {
    column_eval_var("f", fixed_query.column_index(), fixed_query.rotation().0)
}

fn advice_eval_var(advice_query: AdviceQuery) -> String {
    column_eval_var("a", advice_query.column_index(), advice_query.rotation().0)
}

fn column_eval_var(prefix: &'static str, column_index: usize, rotation: i32) -> String {
    match rotation.cmp(&0) {
        Ordering::Less => format!("{prefix}_{column_index}_prev_{}", rotation.abs()),
        Ordering::Equal => format!("{prefix}_{column_index}"),
        Ordering::Greater => format!("{prefix}_{column_index}_next_{rotation}"),
    }
}

#[allow(clippy::too_many_arguments)]
fn evaluate<F, T>(
    expression: &Expression<F>,
    constant: &impl Fn(U256) -> T,
    fixed: &impl Fn(FixedQuery) -> T,
    advice: &impl Fn(AdviceQuery) -> T,
    instance: &impl Fn(InstanceQuery) -> T,
    challenge: &impl Fn(Challenge) -> T,
    negated: &impl Fn(T) -> T,
    sum: &impl Fn(T, T) -> T,
    product: &impl Fn(T, T) -> T,
    scaled: &impl Fn(T, U256) -> T,
) -> T
where
    F: PrimeField<Repr = [u8; 0x20]>,
{
    let evaluate = |expr: &Expression<F>| {
        evaluate(
            expr, constant, fixed, advice, instance, challenge, negated, sum, product, scaled,
        )
    };
    match expression {
        Expression::Constant(scalar) => constant(fe_to_u256(*scalar)),
        Expression::Selector(_) => unreachable!(),
        Expression::Fixed(query) => fixed(*query),
        Expression::Advice(query) => advice(*query),
        Expression::Instance(query) => instance(*query),
        Expression::Challenge(value) => challenge(*value),
        Expression::Negated(value) => negated(evaluate(value)),
        Expression::Sum(lhs, rhs) => sum(evaluate(lhs), evaluate(rhs)),
        Expression::Product(lhs, rhs) => product(evaluate(lhs), evaluate(rhs)),
        Expression::Scaled(value, scalar) => scaled(evaluate(value), fe_to_u256(*scalar)),
    }
}
