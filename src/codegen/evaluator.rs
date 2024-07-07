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
use regex::Regex;
use ruint::aliases::U256;
use std::{cell::RefCell, cmp::Ordering, collections::HashMap, iter};

use super::util::get_memory_ptr;

#[derive(Debug)]
pub(crate) struct Evaluator<'a, F: PrimeField> {
    cs: &'a ConstraintSystem<F>,
    meta: &'a ConstraintSystemMeta,
    data: &'a Data,
    var_counter: RefCell<usize>,
    var_cache: RefCell<HashMap<String, String>>,
}

impl<'a, F> Evaluator<'a, F>
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

    pub fn permutation_computations(&self, separate: bool) -> Vec<(Vec<String>, String)> {
        let Self { meta, data, .. } = self;
        let last_chunk_idx = meta.num_permutation_zs - 1;
        let theta_mptr = "theta_mptr";
        let beta = get_memory_ptr(theta_mptr, 1, &separate);
        let gamma = get_memory_ptr(theta_mptr, 2, &separate);
        let x_mptr = get_memory_ptr(theta_mptr, 4, &separate);
        let l_last = get_memory_ptr(theta_mptr, 14, &separate);
        let l_blind = get_memory_ptr(theta_mptr, 15, &separate);
        let l_0 = get_memory_ptr(theta_mptr, 16, &separate);
        chain![
            data.permutation_z_evals.first().map(|(z, _, _)| {
                vec![
                    format!("let l_0 := mload({l_0})"),
                    format!("let eval := addmod(l_0, sub(r, mulmod(l_0, {z}, r)), r)"),
                ]
            }),
            data.permutation_z_evals.last().map(|(z, _, _)| {
                let item = "addmod(mulmod(perm_z_last, perm_z_last, r), sub(r, perm_z_last), r)";
                vec![
                    format!("let perm_z_last := {z}"),
                    format!("let eval := mulmod(mload({l_last}), {item}, r)"),
                ]
            }),
            data.permutation_z_evals.iter().tuple_windows().map(
                |((_, _, z_i_last), (z_j, _, _))| {
                    let item = format!("addmod({z_j}, sub(r, {z_i_last}), r)");
                    vec![format!("let eval := mulmod(mload({l_0}), {item}, r)")]
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
                        format!("let gamma := mload({})", gamma),
                        format!("let beta := mload({})", beta),
                        format!("let lhs := {}", evals.1),
                        format!("let rhs := {}", evals.0),
                    ],
                    columns.iter().flat_map(|column| {
                        let perm_eval = &data.permutation_evals[column];
                        let eval = self.eval(*column.column_type(), column.index(), 0);
                        let item = format!("mulmod(beta, {perm_eval}, r)");
                        [format!(
                            "lhs := mulmod(lhs, addmod(addmod({eval}, {item}, r), gamma, r), r)"
                        )]
                    }),
                    (chunk_idx == 0)
                        .then(|| format!("mstore(0x00, mulmod(beta, mload({}), r))", x_mptr)),
                    columns.iter().enumerate().flat_map(|(idx, column)| {
                        let eval = self.eval(*column.column_type(), column.index(), 0);
                        let item = format!("addmod(addmod({eval}, mload(0x00), r), gamma, r)");
                        chain![
                            [format!("rhs := mulmod(rhs, {item}, r)")],
                            (!(chunk_idx == last_chunk_idx && idx == last_column_idx))
                                .then(|| "mstore(0x00, mulmod(mload(0x00), DELTA, r))".to_string()),
                        ]
                    }),
                    {
                        let item = format!("addmod(mload({l_last}), mload({l_blind}), r)");
                        let item = format!("sub(r, mulmod(left_sub_right, {item}, r))");
                        [
                            format!("let left_sub_right := addmod(lhs, sub(r, rhs), r)"),
                            format!("let eval := addmod(left_sub_right, {item}, r)"),
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
    pub fn lookup_computations(
        &self,
        vk_lookup_const_table: Option<HashMap<ruint::Uint<256, 4>, super::util::Ptr>>,
        separate: bool,
    ) -> (Vec<(Vec<String>, String)>, Vec<F>) {
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

        let evaluate_lookup_consts = |expressions: &Vec<_>, constants: &mut Vec<F>| {
            expressions.iter().for_each(|expression| {
                self.collect_constants(expression, constants);
            });
        };

        let mut inputs_consts: Vec<F> = Vec::new();
        let inputs_tables = self
            .cs
            .lookups()
            .iter()
            .map(|lookup| {
                let inputs_iter = lookup.input_expressions().iter();
                let inputs = inputs_iter.clone().map(evaluate).collect_vec();
                inputs_iter.for_each(|arg| {
                    evaluate_lookup_consts(arg, &mut inputs_consts);
                });
                let table = evaluate(lookup.table_expressions());
                (inputs, table)
            })
            .collect_vec();
        // Remove duplicates while preserving order
        let mut unique_inputs_consts = Vec::new();
        for const_value in inputs_consts.clone() {
            if !unique_inputs_consts.contains(&const_value) {
                unique_inputs_consts.push(const_value);
            }
        }
        let lookup_const_table = if let Some(vk_lookup_const_table) = vk_lookup_const_table {
            // map all the keys to u256_string
            let vk_lookup_const_table: HashMap<String, super::util::Ptr> = vk_lookup_const_table
                .iter()
                .map(|(key, value)| (u256_string(*key), *value))
                .collect();
            Some(vk_lookup_const_table)
        } else {
            None
        };

        let vec = izip!(inputs_tables, &self.data.lookup_evals)
            .flat_map(|(inputs_tables, evals)| {
                let (inputs, (table_lines, tables)) = inputs_tables.clone();
                let num_inputs = inputs.len();
                let (table_0, rest_tables) = tables.split_first().unwrap();
                let (phi, phi_next, m) = evals;
                // if separate then use the theta_mptr on set on the stack
                // otherwise use the solidity constant
                let theta_mptr = "theta_mptr";
                let theta = get_memory_ptr(theta_mptr, 0, &separate);
                // For all the the other pointers offset from the theta_mptr perfrom relavant add operation
                let beta = get_memory_ptr(theta_mptr, 1, &separate);
                let l_last = get_memory_ptr(theta_mptr, 14, &separate);

                let l_blind = get_memory_ptr(theta_mptr, 15, &separate);

                let l_0 = get_memory_ptr(theta_mptr, 16, &separate);
                // print line the input tables
                [
                    vec![
                        format!("let l_0 := mload({l_0})"),
                        format!("let eval := mulmod(l_0, {phi}, r)"),
                    ],
                    vec![
                        format!("let l_last := mload({l_last})"),
                        format!("let eval := mulmod(l_last, {phi}, r)"),
                    ],
                    chain![
                        [
                            format!("let theta := mload({})", theta).as_str(),
                            format!("let beta := mload({})", beta).as_str(),
                            "let table"
                        ]
                        .map(str::to_string),
                        // TODO: break this into it's own function on the solidity side of things
                        code_block::<1, false>(chain![
                            table_lines,
                            [format!("table := {table_0}")],
                            rest_tables.iter().map(|table| format!(
                                "table := addmod(mulmod(table, theta, r), {table}, r)"
                            )),
                            [format!("table := addmod(table, beta, r)")],
                        ]),
                        // TODO: break this into it's own function on the solidity side of things,
                        // calling it within a for loop.
                        izip!(0.., inputs.into_iter()).flat_map(|(idx, (input_lines, inputs))| {
                            let (input_0, rest_inputs) = inputs.split_first().unwrap();
                            let ident = format!("input_{idx}");
                            let hex_regex = Regex::new(r":= (0x[0-9a-fA-F]+)").unwrap();
                            // use regex to replace hex constants with mload format
                            let input_lines =
                                if let Some(lookup_const_table) = lookup_const_table.clone() {
                                    // println!("lookup_const_table: {:?}", lookup_const_table);
                                    let modified_input_lines: Vec<String> = input_lines
                                        .into_iter()
                                        .map(|line| {
                                            hex_regex
                                                .replace_all(&line, |caps: &regex::Captures| {
                                                    if let Some(hex_str) = caps.get(1) {
                                                        if let Some(ptr) =
                                                            lookup_const_table.get(hex_str.as_str())
                                                        {
                                                            format!(":= mload({ptr})")
                                                        } else {
                                                            hex_str.as_str().to_string()
                                                        }
                                                    } else {
                                                        line.to_string()
                                                    }
                                                })
                                                .to_string()
                                        })
                                        .collect();
                                    modified_input_lines
                                } else {
                                    input_lines
                                };
                            // use regex to
                            chain![
                                [format!("let {ident}")],
                                code_block::<1, false>(chain![
                                    input_lines,
                                    [format!("{ident} := {input_0}")],
                                    rest_inputs.iter().map(|input| format!(
                                        "{ident} := addmod(mulmod({ident}, theta, r), {input}, r)"
                                    )),
                                    [format!("{ident} := addmod({ident}, beta, r)")],
                                ]),
                            ]
                        }),
                        [format!("let lhs"), format!("let rhs")],
                        // TODO: break this into it's own function on the solidity side of things
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
                                        .map(|ident| format!("tmp := mulmod(tmp, {ident}, r)")),
                                    [format!("rhs := addmod(rhs, tmp, r)"),],
                                    (i == num_inputs - 1)
                                        .then(|| format!("rhs := mulmod(rhs, table, r)")),
                                ])
                            }
                        }),
                        // TODO: break this into it's own function on the solidity side of things
                        code_block::<1, false>(chain![
                            [format!("let tmp := input_0")],
                            (1..num_inputs)
                                .map(|idx| format!("tmp := mulmod(tmp, input_{idx}, r)")),
                            [
                                format!("rhs := addmod(rhs, sub(r, mulmod({m}, tmp, r)), r)"),
                                {
                                    let item = format!("addmod({phi_next}, sub(r, {phi}), r)");
                                    format!("lhs := mulmod(mulmod(table, tmp, r), {item}, r)")
                                },
                            ],
                        ]),
                        {
                            let l_inactive =
                                format!("addmod(mload({l_blind}), mload({l_last}), r)");
                            let l_active = format!("addmod(1, sub(r, {l_inactive}), r)");
                            [format!(
                                "let eval := mulmod({l_active}, addmod(lhs, sub(r, rhs), r), r)"
                            )]
                        },
                    ]
                    .collect_vec(),
                ]
            })
            .zip(iter::repeat("eval".to_string()))
            .collect_vec();
        (vec, unique_inputs_consts)
    }

    #[cfg(not(feature = "mv-lookup"))]
    pub fn lookup_computations(
        &self,
        _vk_lookup_const_table: Option<HashMap<ruint::Uint<256, 4>, super::util::Ptr>>,
        _separate: bool,
    ) -> (Vec<(Vec<String>, String)>, Vec<F>) {
        let _ = |expressions: &Vec<_>, constants: &mut Vec<F>| {
            expressions.iter().for_each(|expression| {
                self.collect_constants(expression, constants);
            });
        };
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
        (vec, Vec::new())
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

    #[allow(clippy::only_used_in_recursion)]
    #[allow(dead_code)]
    fn collect_constants(&self, expression: &Expression<F>, constants: &mut Vec<F>) {
        match expression {
            Expression::Constant(constant) => {
                constants.push(*constant);
            }
            Expression::Negated(inner) => {
                self.collect_constants(inner, constants);
            }
            Expression::Sum(lhs, rhs) => {
                self.collect_constants(lhs, constants);
                self.collect_constants(rhs, constants);
            }
            Expression::Product(lhs, rhs) => {
                self.collect_constants(lhs, constants);
                self.collect_constants(rhs, constants);
            }
            Expression::Scaled(inner, _scalar) => {
                self.collect_constants(inner, constants);
            }
            _ => {}
        }
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
                let (lines, var) = self.init_var(format!("sub(r, {var})"), None);
                acc.extend(lines);
                (acc, var)
            },
            &|(mut lhs_acc, lhs_var), (rhs_acc, rhs_var)| {
                let (lines, var) = self.init_var(format!("addmod({lhs_var}, {rhs_var}, r)"), None);
                lhs_acc.extend(rhs_acc);
                lhs_acc.extend(lines);
                (lhs_acc, var)
            },
            &|(mut lhs_acc, lhs_var), (rhs_acc, rhs_var)| {
                let (lines, var) = self.init_var(format!("mulmod({lhs_var}, {rhs_var}, r)"), None);
                lhs_acc.extend(rhs_acc);
                lhs_acc.extend(lines);
                (lhs_acc, var)
            },
            &|(mut acc, var), scalar| {
                let scalar = u256_string(scalar);
                let (lines, var) = self.init_var(format!("mulmod({var}, {scalar}, r)"), None);
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
    let evaluate = |expr| {
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
