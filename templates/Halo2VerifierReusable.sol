// SPDX-License-Identifier: MIT

pragma solidity ^0.8.0;

contract Halo2VerifierReusable {
    uint256 internal constant    PROOF_LEN_CPTR = 0x64;
    uint256 internal constant    PROOF_CPTR = 0x84;
    uint256 internal constant    Q = 21888242871839275222246405745257275088696311157297823662689037894645226208583;
    uint256 internal constant    R = 21888242871839275222246405745257275088548364400416034343698204186575808495617; // BN254 scalar field
    uint256 internal constant    DELTA = 4131629893567559867359510883348571134090853742863529169391034518566172092834;
    uint256 internal constant    PTR_BITMASK = 0xFFFF;
    uint256 internal constant    BYTE_FLAG_BITMASK = 0xFF;



    function verifyProof(
        address vk,
        bytes calldata proof,
        uint256[] calldata instances
    ) public returns (bool) {
        assembly {
            // Read EC point (x, y) at (proof_cptr, proof_cptr + 0x20),
            // and check if the point is on affine plane,
            // and store them in (hash_mptr, hash_mptr + 0x20).
            // Return updated (success, proof_cptr, hash_mptr).
            function read_ec_point(success, proof_cptr, hash_mptr) -> ret0, ret1, ret2 {
                let x := calldataload(proof_cptr)
                let y := calldataload(add(proof_cptr, 0x20))
                ret0 := and(success, lt(x, Q))
                ret0 := and(ret0, lt(y, Q))
                ret0 := and(ret0, eq(mulmod(y, y, Q), addmod(mulmod(x, mulmod(x, x, Q), Q), 3, Q)))
                mstore(hash_mptr, x)
                mstore(add(hash_mptr, 0x20), y)
                ret1 := add(proof_cptr, 0x40)
                ret2 := add(hash_mptr, 0x40)
            }

            // Squeeze challenge by keccak256(memory[0..hash_mptr]),
            // and store hash mod r as challenge in challenge_mptr,
            // and push back hash in 0x00 as the first input for next squeeze.
            // Return updated (challenge_mptr, hash_mptr).
            function squeeze_challenge(challenge_mptr, hash_mptr) -> ret0, ret1 {
                let hash := keccak256(0x00, hash_mptr)
                mstore(challenge_mptr, mod(hash, R))
                mstore(0x00, hash)
                ret0 := add(challenge_mptr, 0x20)
                ret1 := 0x20
            }

            // Squeeze challenge without absorbing new input from calldata,
            // by putting an extra 0x01 in memory[0x240] and squeeze by keccak256(memory[0..21]),
            // and store hash mod r as challenge in challenge_mptr,
            // and push back hash in 0x220 as the first input for next squeeze.
            // Return updated (challenge_mptr).
            function squeeze_challenge_cont(challenge_mptr) -> ret {
                mstore8(0x20, 0x01)
                let hash := keccak256(0x00, 0x21)
                mstore(challenge_mptr, mod(hash, R))
                mstore(0x00, hash)
                ret := add(challenge_mptr, 0x20)
            }

            // Batch invert values in memory[mptr_start..mptr_end] in place.
            // Return updated (success).
            function batch_invert(success, mptr_start, mptr_end) -> ret {
                let gp_mptr := mptr_end
                let gp := mload(mptr_start)
                let mptr := add(mptr_start, 0x20)
                for
                    {}
                    lt(mptr, sub(mptr_end, 0x20))
                    {}
                {
                    gp := mulmod(gp, mload(mptr), R)
                    mstore(gp_mptr, gp)
                    mptr := add(mptr, 0x20)
                    gp_mptr := add(gp_mptr, 0x20)
                }
                gp := mulmod(gp, mload(mptr), R)

                mstore(gp_mptr, 0x20)
                mstore(add(gp_mptr, 0x20), 0x20)
                mstore(add(gp_mptr, 0x40), 0x20)
                mstore(add(gp_mptr, 0x60), gp)
                mstore(add(gp_mptr, 0x80), sub(R, 2))
                mstore(add(gp_mptr, 0xa0), R)
                ret := and(success, staticcall(gas(), 0x05, gp_mptr, 0xc0, gp_mptr, 0x20))
                let all_inv := mload(gp_mptr)

                let first_mptr := mptr_start
                let second_mptr := add(first_mptr, 0x20)
                gp_mptr := sub(gp_mptr, 0x20)
                for
                    {}
                    lt(second_mptr, mptr)
                    {}
                {
                    let inv := mulmod(all_inv, mload(gp_mptr), R)
                    all_inv := mulmod(all_inv, mload(mptr), R)
                    mstore(mptr, inv)
                    mptr := sub(mptr, 0x20)
                    gp_mptr := sub(gp_mptr, 0x20)
                }
                let inv_first := mulmod(all_inv, mload(second_mptr), R)
                let inv_second := mulmod(all_inv, mload(first_mptr), R)
                mstore(first_mptr, inv_first)
                mstore(second_mptr, inv_second)
            }

            // Add (x, y) into point at (0x00, 0x20).
            // Return updated (success).
            function ec_add_acc(success, x, y) -> ret {
                mstore(0x40, x)
                mstore(0x60, y)
                ret := and(success, staticcall(gas(), 0x06, 0x00, 0x80, 0x00, 0x40))
            }

            // Scale point at (0x00, 0x20) by scalar.
            function ec_mul_acc(success, scalar) -> ret {
                mstore(0x40, scalar)
                ret := and(success, staticcall(gas(), 0x07, 0x00, 0x60, 0x00, 0x40))
            }

            // Add (x, y) into point at (0x80, 0xa0).
            // Return updated (success).
            function ec_add_tmp(success, x, y) -> ret {
                mstore(0xc0, x)
                mstore(0xe0, y)
                ret := and(success, staticcall(gas(), 0x06, 0x80, 0x80, 0x80, 0x40))
            }

            // Scale point at (0x80, 0xa0) by scalar.
            // Return updated (success).
            function ec_mul_tmp(success, scalar) -> ret {
                mstore(0xc0, scalar)
                ret := and(success, staticcall(gas(), 0x07, 0x80, 0x60, 0x80, 0x40))
            }

            // Perform pairing check.
            // Return updated (success).
            function ec_pairing(success, vk_mptr, lhs_x, lhs_y, rhs_x, rhs_y) -> ret {
                mstore(0x00, lhs_x)
                mstore(0x20, lhs_y)
                mstore(0x40, mload(add(vk_mptr, {{ vk_const_offsets["g2_x_1"]|hex() }})))
                mstore(0x60, mload(add(vk_mptr, {{ vk_const_offsets["g2_x_2"]|hex() }})))
                mstore(0x80, mload(add(vk_mptr, {{ vk_const_offsets["g2_y_1"]|hex() }})))
                mstore(0xa0, mload(add(vk_mptr, {{ vk_const_offsets["g2_y_2"]|hex() }})))
                mstore(0xc0, rhs_x)
                mstore(0xe0, rhs_y)
                mstore(0x100, mload(add(vk_mptr, {{ vk_const_offsets["neg_s_g2_x_1"]|hex() }})))
                mstore(0x120, mload(add(vk_mptr, {{ vk_const_offsets["neg_s_g2_x_2"]|hex() }})))
                mstore(0x140, mload(add(vk_mptr, {{ vk_const_offsets["neg_s_g2_y_1"]|hex() }})))
                mstore(0x160, mload(add(vk_mptr, {{ vk_const_offsets["neg_s_g2_y_2"]|hex() }})))
                ret := and(success, staticcall(gas(), 0x08, 0x00, 0x180, 0x00, 0x20))
                ret := and(ret, mload(0x00))
            }

            function reposition_challenge_len_data() -> ret0, ret1, ret2 {
                let fsm_challenges := mload({{ vk_const_offsets["fsm_challenges"]|hex() }})
                let challenge_len_ptr := {{ vk_const_offsets["num_advices_user_challenges_0"]|hex() }}
                let challenge_len_data := mload(challenge_len_ptr)
                let num_words := and(challenge_len_data, BYTE_FLAG_BITMASK)
                ret0 := num_words
                num_words := mul(0x20, num_words)
                challenge_len_data := shr(8, challenge_len_data)
                for { let i := 0x20 } lt(i, num_words) { i := add(i, 0x20) } {
                    mstore(add(fsm_challenges, i), mload(add(challenge_len_ptr, i)))
                }
                ret1 := fsm_challenges
                ret2 := challenge_len_data
            }

            // Returns start of computaions ptr and length of SoA layout memory
            // encoding for quotient evaluation data (gate, permutation and lookup computations)
            function soa_layout_metadata(offset, vk_mptr) -> ret0, ret1 {
                let computations_len_ptr := add(vk_mptr, mload(add(vk_mptr, offset)))
                ret0 := add(computations_len_ptr, 0x20)
                ret1 := mload(computations_len_ptr) // Remember this length represented in bytes
            }

            function col_evals(z, num_words, permutation_z_evals_ptr, theta_mptr) {
                let gamma := mload(add(theta_mptr, 0x40))
                let beta := mload(add(theta_mptr, 0x20))
                let x := mload(add(theta_mptr, 0x80))
                let l_last := mload(add(theta_mptr, 0x1c0))
                let l_blind := mload(add(theta_mptr, 0x1e0))
                let i_eval := mload(add(theta_mptr, 0x220))
                // Extract the index 1 and index 0 z evaluations from the z word. 
                let lhs := calldataload(and(shr(16,z), PTR_BITMASK)) 
                let rhs := calldataload(and(z, PTR_BITMASK)) 
                z := shr(48, z)  
                // loop through the word_len_chunk
                for { let j := 0 } lt(j, num_words) { j := add(j, 0x20) } {
                    for { } z { } {
                        let eval := i_eval
                        if eq(and(z, BYTE_FLAG_BITMASK), 0x00) {
                            eval := calldataload(and(shr(8, z), PTR_BITMASK))
                        }
                        lhs := mulmod(lhs, addmod(addmod(eval, mulmod(beta, calldataload(and(shr(24, z), PTR_BITMASK)), R), R), gamma, R), R)
                        rhs := mulmod(rhs, addmod(addmod(eval, mload(0x00), R), gamma, R), R)
                        z := shr(40, z)
                        mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    }
                    z := mload(add(permutation_z_evals_ptr, add(j, 0x20)))
                }
                let left_sub_right := addmod(lhs, sub(R, rhs), R)
                let fsm_ptr := mload(0x20)
                mstore(fsm_ptr, addmod(left_sub_right, sub(R, mulmod(left_sub_right, addmod(l_last, l_blind, R), R)), R))
                mstore(0x20, add(fsm_ptr,0x20))
            }

            function z_evals(z, num_words_packed, perm_z_last_ptr, permutation_z_evals_ptr, theta_mptr, l_0, y, quotient_eval_numer) -> ret {
                let num_words := and(num_words_packed, PTR_BITMASK)
                // Initialize the free static memory pointer to store the column evals.
                mstore(0x20, 0x40)
                // Iterate through the tuple window length ( permutation_z_evals_len.len() - 1 ) offset by one word.
                for { } lt(permutation_z_evals_ptr, perm_z_last_ptr) { } {
                    let next_z_ptr := add(permutation_z_evals_ptr, num_words)
                    let z_j := mload(next_z_ptr)
                    quotient_eval_numer := addmod(
                        mulmod(quotient_eval_numer, y, R),
                        mulmod(l_0, addmod(calldataload(and(z_j, PTR_BITMASK)), sub(R, calldataload(and(shr(32,z), PTR_BITMASK))), R), R), 
                        R
                    )
                    col_evals(z, num_words, permutation_z_evals_ptr, theta_mptr)
                    permutation_z_evals_ptr := next_z_ptr
                    z := z_j
                } 
                // Due to the fact that permutation_columns.len() in H2 might not be divisible by permutation_chunk_len, the last column length might be less than permutation_chunk_len
                // We store this length in the last 16 bits of the num_words_packed word.
                num_words := and(shr(16, num_words_packed), PTR_BITMASK)
                col_evals(z, num_words, permutation_z_evals_ptr, theta_mptr)
                // iterate through col_evals to update the quotient_eval_numer accumulator
                let end_ptr := mload(0x20)
                for { let j := 0x40 } lt(j, end_ptr) { j := add(j, 0x20) } {
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, R), mload(j), R)
                }
                ret := quotient_eval_numer
            }

            function lookup_input_accum(expressions_word, fsmp, i, code_ptr) -> ret0, ret1, ret2 {
                expressions_word := shr(8, expressions_word)
                // Number of words the mptr vars for the accumulator evaluations shifted up by one
                let num_words_vars := mul(0x20, and(expressions_word, BYTE_FLAG_BITMASK))
                expressions_word := shr(8, expressions_word)
                // initlaize the accumulator with the first value in the vars
                let a := mload(and(expressions_word, PTR_BITMASK))
                expressions_word := shr(16, expressions_word)
                let theta := mload(0x60) 
                for { let j } lt(j, num_words_vars) { j := add(j, 0x20) } {
                    for {  } expressions_word { } {
                        a := addmod(
                            mulmod(a, theta, R),
                            mload(and(expressions_word, PTR_BITMASK)),
                            R
                        )
                        expressions_word := shr(16, expressions_word)
                    }
                    ret0 := add(code_ptr, add(i, j))
                    expressions_word := mload(ret0)
                }
                ret1 := expressions_word
                ret2 := a
            }

            function expression_evals_packed(fsmp, code_ptr, expressions_word) -> ret0, ret1, ret2 {
                // Load in the least significant byte of the `expressions_word` word to get the total number of words we will need to load in.
                let num_words_shift_up_one := add(mul(0x20, and(expressions_word, BYTE_FLAG_BITMASK)), 0x20)
                // start of the expression encodings
                expressions_word := shr(8, expressions_word)
                let acc 
                for { let i := 0x20 } lt(i, num_words_shift_up_one) { i := add(i, 0x20) } {
                    for {  } expressions_word { } {
                        let mstore_ptr := add(fsmp, acc)
                        // Load in the least significant byte of the `expression` word to get the operation type 
                        // Then determine which operation to peform and then store the result in the next available memory slot.
                        switch and(expressions_word, BYTE_FLAG_BITMASK)
                        // 0x00 => Advice/Fixed expression
                        case 0x00 {
                            expressions_word := shr(8, expressions_word)
                            // Load the calldata ptr from the expression, which come from the 2nd and 3rd least significant bytes.
                            mstore(mstore_ptr, calldataload(and(expressions_word, PTR_BITMASK)))
                            // Move to the next expression
                            expressions_word := shr(16, expressions_word)
                        } 
                        // 0x01 => Negated expression
                        case 0x01 {
                            expressions_word := shr(8, expressions_word)
                            // Load the memory ptr from the expression, which come from the 2nd and 3rd least significant bytes
                            mstore(mstore_ptr, sub(R, mload(and(expressions_word, PTR_BITMASK))))
                            // Move to the next expression
                            expressions_word := shr(16, expressions_word)
                        }
                        // 0x02 => Sum expression
                        case 0x02 {
                            expressions_word := shr(8, expressions_word)
                            // Load the lhs operand memory ptr from the expression, which comes from the 2nd and 3rd least significant bytes
                            // Load the rhs operand memory ptr from the expression, which comes from the 4th and 5th least significant bytes
                            mstore(mstore_ptr, addmod(mload(and(expressions_word, PTR_BITMASK)), mload(and(shr(16, expressions_word), PTR_BITMASK)),R))
                            // Move to the next expression
                            expressions_word := shr(32, expressions_word)
                        }
                        // 0x03 => Product/scalar expression
                        case 0x03 {
                            expressions_word := shr(8, expressions_word)
                            // Load the lhs operand memory ptr from the expression, which comes from the 2nd and 3rd least significant bytes
                            // Load the rhs operand memory ptr from the expression, which comes from the 4th and 5th least significant bytes
                            mstore(mstore_ptr, mulmod(mload(and(expressions_word, PTR_BITMASK)),mload(and(shr(16, expressions_word), PTR_BITMASK)),R))
                            // Move to the next expression
                            expressions_word := shr(32, expressions_word)
                        } 
                        // 0x04 => (For lookup expressions) Start accumulator evaluations for the lookup (table or input)
                        // Will always occur at the end of the last word of the lookup expression.
                        case 0x04 {
                            ret0, ret1, ret2 := lookup_input_accum(expressions_word, fsmp, i, code_ptr)
                            leave
                        }
                        acc := add(acc, 0x20)
                    }
                    ret0 := add(code_ptr, i)
                    expressions_word := mload(ret0)
                }
                ret1 := expressions_word
                ret2 := sub(acc, 0x20)
            }

            function lookup_expr_evals_packed(fsmp, code_ptr, expressions_word, mv) -> ret0, ret1, ret2 {
                // expression evaluation.
                ret0, ret1, ret2 := expression_evals_packed(fsmp, code_ptr, expressions_word)
                if mv {
                    // add the beta accum addmod if mv lookup
                    ret2 := addmod(ret2, mload(0x80), R)
                }
            }

            function mv_lookup_evals(table, evals_ptr, quotient_eval_numer, y) -> ret0, ret1, ret2 {
                // iterate through the input_tables_len
                let evals := mload(evals_ptr)
                // We store a boolean flag in the first LSG byte of the evals ptr to determine if we need to load in a new table or reuse the previous table.
                let new_table := and(evals, BYTE_FLAG_BITMASK)
                evals := shr(8, evals)
                let phi := and(evals, PTR_BITMASK)
                quotient_eval_numer := addmod(
                    mulmod(quotient_eval_numer, y, R), 
                    mulmod(mload(0x20),calldataload(phi), R), 
                    R
                )
                quotient_eval_numer := addmod(
                    mulmod(quotient_eval_numer, y, R),
                    mulmod(mload(0x00), calldataload(phi), R), 
                    R
                )
                // load in the lookup_table_lines from the evals_ptr
                evals_ptr := add(evals_ptr, 0x20)
                // Due to the fact that lookups can share the previous table, we can cache it for reuse.
                let input_expression := mload(evals_ptr)
                if new_table {
                    evals_ptr, input_expression, table := lookup_expr_evals_packed(0xa0, evals_ptr, mload(evals_ptr), 0x1)
                } 
                // outer inputs len, stored in the first input expression word
                let outer_inputs_len := and(input_expression, PTR_BITMASK)
                input_expression := shr(16, input_expression)
                // shift up the inputs iterator by the free static memory offset of 0xa0
                for { let j := 0xa0 } lt(j, add(outer_inputs_len, 0xa0)) { j := add(j, 0x20) } {
                    // call the expression_evals function to evaluate the input_lines
                    let ident
                    evals_ptr, input_expression, ident := lookup_expr_evals_packed(j, evals_ptr, input_expression, 0x1)
                    // store ident in free static memory
                    mstore(j, ident)
                }
                let lhs
                let rhs
                switch eq(outer_inputs_len, 0x20)
                case 1 {
                    rhs := table
                } default {
                    // iterate through the outer_inputs_len
                    let last_idx := sub(outer_inputs_len, 0x20)
                    for { let i := 0 } lt(i, outer_inputs_len) { i := add(i, 0x20) } {
                        let tmp := mload(0xa0)
                        let j := 0x20
                        if eq(i, 0){
                            tmp := mload(0xc0)
                            j := 0x40
                        }
                        for { } lt(j, outer_inputs_len) { j := add(j, 0x20) } {
                            if eq(i, j) {
                                continue
                            }
                            tmp := mulmod(tmp, mload(add(j, 0xa0)), R)
                            
                        }
                        rhs := addmod(rhs, tmp, R)
                        if eq(i, last_idx) {
                            rhs := mulmod(rhs, table, R)
                        } 
                    }
                }
                let tmp := mload(0xa0)
                for { let j := 0x20 } lt(j, outer_inputs_len) { j := add(j, 0x20) } {
                    tmp := mulmod(tmp, mload(add(j, 0xa0)), R)
                }
                rhs := addmod(
                    rhs, 
                    sub(R, mulmod(calldataload(and(shr(32, evals), PTR_BITMASK)), tmp, R)),
                    R
                )
                lhs := mulmod(
                    mulmod(table, tmp, R),
                    addmod(calldataload(and(shr(16, evals), PTR_BITMASK)), sub(R, calldataload(phi)), R), 
                    R
                )
                quotient_eval_numer := addmod(
                    mulmod(quotient_eval_numer, y, R),
                    mulmod(
                        addmod(
                            1, 
                            sub(R, addmod(mload(0x40), mload(0x00), R)),
                            R
                        ), 
                        addmod(lhs, sub(R, rhs), R),
                        R
                    ), 
                    R
                )
                ret0 := evals_ptr
                ret1 := table
                ret2 := quotient_eval_numer
            }

            function lookup_evals(table, evals_ptr, quotient_eval_numer, y) -> ret0, ret1, ret2 {
                // iterate through the input_tables_len
                let evals := mload(evals_ptr)
                // We store a boolean flag in the first LSG byte of the evals ptr to determine if we need to load in a new table or reuse the previous table.
                let new_table := and(evals, BYTE_FLAG_BITMASK)
                evals := shr(8, evals)
                let z := and(evals, PTR_BITMASK)
                evals := shr(16, evals)
                quotient_eval_numer := addmod(
                    mulmod(quotient_eval_numer, y, R), 
                    addmod(
                        mload(0x20), 
                        mulmod(
                            mload(0x20), 
                            sub(R, calldataload(z)), 
                            R
                        ),
                        R
                    ), 
                    R
                )
                quotient_eval_numer := addmod(
                    mulmod(quotient_eval_numer, y, R),
                    mulmod(
                        mload(0x00), 
                        addmod(
                            mulmod(calldataload(z), calldataload(z), R), 
                            sub(R, calldataload(z)), 
                            R
                        ),
                        R
                    ), 
                    R
                )
                // load in the lookup_table_lines from the evals_ptr
                evals_ptr := add(evals_ptr, 0x20)
                // Due to the fact that lookups can share the previous table, we can cache it for reuse.
                let input_expression := mload(evals_ptr)
                if new_table {
                    evals_ptr, input_expression, table := lookup_expr_evals_packed(0xc0, evals_ptr, mload(evals_ptr), 0x0)
                } 
                // call the expression_evals function to evaluate the input_lines
                let input
                evals_ptr, input_expression, input := lookup_expr_evals_packed(0xc0, evals_ptr, input_expression, 0x0)
                let p_input := and(shr(16, evals), PTR_BITMASK)
                let p_table := and(shr(48, evals), PTR_BITMASK)
                quotient_eval_numer := addmod(
                    mulmod(quotient_eval_numer, y, R), 
                    mulmod(
                        addmod(
                            1, 
                            sub(R, addmod(mload(0x40), mload(0x0), R)),
                            R
                        ), 
                        addmod(
                            mulmod(
                                calldataload(and(evals, PTR_BITMASK)), 
                                mulmod(
                                    addmod(calldataload(p_input), mload(0x80), R), 
                                    addmod(calldataload(p_table), mload(0xa0), R), 
                                    R
                                ),
                                R
                            ), 
                            sub(
                                R, 
                                mulmod(
                                    calldataload(z), 
                                    mulmod(addmod(input, mload(0x80), R), addmod(table, mload(0xa0), R), R), 
                                    R
                                )
                            ),
                            R
                        ), 
                        R
                    ), 
                    R
                )
                quotient_eval_numer := addmod(
                    mulmod(quotient_eval_numer, y, R),
                    mulmod(mload(0x20), addmod(calldataload(p_input), sub(R, calldataload(p_table)), R), R),
                    R
                )
                quotient_eval_numer := addmod(
                    mulmod(quotient_eval_numer, y, R),
                    mulmod(
                        addmod(
                            1, 
                            sub(R, addmod(mload(0x40), mload(0x0), R)), R), 
                            mulmod(
                                addmod(calldataload(p_input), sub(R, calldataload(p_table)), R),
                                addmod(calldataload(p_input), sub(R, calldataload(and(shr(32, evals), PTR_BITMASK))), R),
                                R
                            ),
                        R
                    ),
                    R
                )
                ret0 := evals_ptr
                ret1 := table
                ret2 := quotient_eval_numer
            }

            function point_rots(pcs_computations, pcs_ptr, word_shift, x_pow_of_omega, omega) -> ret0, ret1 {
                // Extract the 32 LSG bits (4 bytes) from the pcs_computations word to get the max rot
                let values_max_rot := and(pcs_computations, BYTE_FLAG_BITMASK)
                pcs_computations := shr(8, pcs_computations)
                for { let i := 0 } lt(i, values_max_rot) { i := add(i, 1) } {
                    let value := and(pcs_computations, PTR_BITMASK)
                    if not(eq(value, 0)) {
                        mstore(value, x_pow_of_omega)
                    }
                    if eq(i, sub(values_max_rot, 1)) {
                        break
                    }
                    x_pow_of_omega := mulmod(x_pow_of_omega, omega, R)
                    word_shift := add(word_shift, 16)
                    pcs_computations := shr(16, pcs_computations)
                    if eq(word_shift, 256) {
                        word_shift := 0
                        pcs_ptr := add(pcs_ptr, 0x20)
                        pcs_computations := mload(pcs_ptr)
                    }
                }
                ret0 := x_pow_of_omega
                ret1 := pcs_ptr 
            }

            function coeff_computations(coeff_len_data, coeff_data) -> ret {
                let coeff_len := and(coeff_len_data, BYTE_FLAG_BITMASK)
                ret := shr(8, coeff_len_data)
                switch coeff_len
                case 0x01 {
                    // We only encode the points if the coeff length is greater than 1.
                    // Otherwise we just encode the mu_minus_point and coeff ptr. 
                    mstore(and(shr(16, coeff_data), PTR_BITMASK), mod(mload(and(coeff_data, PTR_BITMASK)), R))
                }
                default {
                    let coeff
                    let offset_aggr := mul(coeff_len, 16)
                    for { let i := 0 } lt(i, coeff_len) { i := add(i, 1) } {
                        let first := 0x01
                        let offset_base := mul(i, 16)
                        let point_i := mload(and(shr(offset_base, coeff_data), PTR_BITMASK))
                        for { let j:= 0 } lt(j, coeff_len) { j := add(j, 1) } {
                            if eq(j, i) {
                                continue
                            } 
                            if first {
                                coeff := addmod(point_i, sub(R, mload(and(shr(mul(j, 16), coeff_data), PTR_BITMASK))), R)
                                first := 0
                                continue
                            } 
                            coeff := mulmod(coeff, addmod(point_i, sub(R, mload(and(shr(mul(j, 16), coeff_data), PTR_BITMASK))), R), R)
                        }
                        offset_base := add(offset_base, offset_aggr)
                        coeff := mulmod(coeff, mload(and(shr(offset_base, coeff_data), PTR_BITMASK)), R)
                        offset_base := add(offset_base, offset_aggr)
                        mstore(and(shr(offset_base, coeff_data), PTR_BITMASK), coeff)
                    }
                }
            }

            function single_rot_set(r_evals_data, ptr, num_words, zeta, quotient_eval, coeff_ptr) -> ret0, ret1 {
                let coeff := mload(coeff_ptr)
                let r_eval
                r_eval := addmod(r_eval, mulmod(coeff, calldataload(and(r_evals_data, PTR_BITMASK)), R), R)
                r_evals_data := shr(16, r_evals_data)
                r_eval := mulmod(r_eval, zeta, R)
                r_eval := addmod(r_eval, mulmod(coeff, quotient_eval, R), R)
                for { let i := 0 } lt(i, num_words) { i := add(i, 1) } {
                    for { } r_evals_data { } {
                        let eval_group_len := and(r_evals_data, BYTE_FLAG_BITMASK)
                        r_evals_data := shr(8, r_evals_data)
                        switch eq(eval_group_len, 0x0)
                        case 0x0 {
                            for { let j := 0 } lt(j, eval_group_len) { j := add(j, 1) } {
                                r_eval := addmod(mulmod(r_eval, zeta, R), mulmod(coeff, calldataload(and(r_evals_data, PTR_BITMASK)), R), R)
                                r_evals_data := shr(16, r_evals_data)
                            }
                        } default {
                            for
                                {
                                    let mptr := and(r_evals_data, PTR_BITMASK)
                                    r_evals_data := shr(16, r_evals_data)
                                    let mptr_end := and(r_evals_data, PTR_BITMASK)
                                }
                                lt(mptr_end, mptr)
                                { mptr := sub(mptr, 0x20) }
                            {
                                r_eval := addmod(mulmod(r_eval, zeta, R), mulmod(coeff, calldataload(mptr), R), R)
                            }
                            r_evals_data := shr(16, r_evals_data)
                        }
                    }
                    ptr := add(ptr, 0x20)
                    r_evals_data := mload(ptr)
                }
                ret0 := r_eval
                ret1 := ptr
            }

            function multi_rot_set(r_evals_data, ptr, num_words, rot_len, zeta, coeff_ptr) -> ret0, ret1 {
                let r_eval := 0
                for { let i := 0 } lt(i, num_words) { i := add(i, 1) } {
                    for { } r_evals_data { } {
                        for { let j := 0 } lt(j, rot_len) { j := add(j, 0x20) } {
                            r_eval := addmod(r_eval, mulmod(mload(add(coeff_ptr, j)), calldataload(and(r_evals_data, PTR_BITMASK)), R), R)
                            r_evals_data := shr(16, r_evals_data)
                        }
                        // Only on the last index do we NOT execute this if block.
                        if or(r_evals_data, lt(i, sub(num_words, 1))) {
                            r_eval := mulmod(r_eval, zeta, R)
                        }
                    }
                    ptr := add(ptr, 0x20)
                    r_evals_data := mload(ptr)
                }
                ret0 := r_eval
                ret1 := ptr
            }

            function r_evals_computation(rot_len, r_evals_data_ptr, zeta, quotient_eval, coeff_ptr) -> ret0, ret1 {
                let r_evals_data := mload(r_evals_data_ptr)
                // number of words to encode the data needed for this set in the r_evals computation.
                let num_words := and(r_evals_data, BYTE_FLAG_BITMASK)
                r_evals_data := shr(8, r_evals_data)
                switch rot_len
                case 0x20 {
                    ret0, ret1 := single_rot_set(r_evals_data, r_evals_data_ptr, num_words, zeta, quotient_eval, coeff_ptr)
                } default {
                    ret0, ret1 := multi_rot_set(r_evals_data, r_evals_data_ptr, num_words, rot_len, zeta, coeff_ptr)
                }
            }

            function pairing_input_computations_first(len, pcs_ptr, data, theta_mptr, success) -> ret {
                mstore(0x00, calldataload(and(data, PTR_BITMASK)))
                data := shr(16, data)
                mstore(0x20, calldataload(and(data, PTR_BITMASK)))
                data := shr(16, data)
                for { let i := 0 } lt(i, len) { i := add(i, 0x20) } {
                    for { } data { } {
                        let ptr_loc := and(data, BYTE_FLAG_BITMASK)
                        data := shr(8, data)
                        let comm_len := and(data, BYTE_FLAG_BITMASK)
                        data := shr(8, data)
                        switch comm_len
                        case 0x0 {
                            switch ptr_loc 
                            case 0x00 {
                                for
                                    {
                                        let mptr := and(data, PTR_BITMASK)
                                        data := shr(16, data)
                                        let mptr_end := and(data, PTR_BITMASK)
                                    }
                                    lt(mptr_end, mptr)
                                    { mptr := sub(mptr, 0x40) }
                                {                      
                                    success := ec_mul_acc(success, mload(add(theta_mptr, 0xA0)))
                                    success := ec_add_acc(success, mload(mptr), mload(add(mptr, 0x20)))
                                }
                            } 
                            case 0x01 {
                                for
                                    {
                                        let mptr := and(data, PTR_BITMASK)
                                        data := shr(16, data)
                                        let mptr_end := and(data, PTR_BITMASK)
                                    }
                                    lt(mptr_end, mptr)
                                    { mptr := sub(mptr, 0x40) }
                                {                      
                                    success := ec_mul_acc(success, mload(add(theta_mptr, 0xA0)))
                                    success := ec_add_acc(success, calldataload(mptr), calldataload(add(mptr, 0x20)))
                                }
                            }
                            data := shr(16, data)
                        } default {
                            switch ptr_loc                        
                            case 0x00 {
                                success := ec_mul_acc(success, mload(add(theta_mptr, 0xA0)))
                                success := ec_add_acc(success, mload(and(data, PTR_BITMASK)), mload(and(shr(16,data), PTR_BITMASK)))
                                if eq(comm_len, 0x02) {
                                    data := shr(32, data)
                                    success := ec_mul_acc(success, mload(add(theta_mptr, 0xA0)))
                                    success := ec_add_acc(success, mload(and(data, PTR_BITMASK)), mload(and(shr(16,data), PTR_BITMASK)))
                                }
                                data := shr(32, data)
                            }
                            case 0x01 {
                                success := ec_mul_acc(success, mload(add(theta_mptr, 0xA0)))
                                success := ec_add_acc(success, calldataload(and(data, PTR_BITMASK)), calldataload(and(shr(16,data), PTR_BITMASK)))
                                if eq(comm_len, 0x02) {
                                    data := shr(32, data)
                                    success := ec_mul_acc(success, mload(add(theta_mptr, 0xA0)))
                                    success := ec_add_acc(success, calldataload(and(data, PTR_BITMASK)), calldataload(and(shr(16,data), PTR_BITMASK)))
                                }
                                data := shr(32, data)
                            }
                            // Quotient eval x and y points
                            case 0x02 {
                                success := ec_mul_acc(success, mload(add(theta_mptr, 0xA0)))
                                success := ec_add_acc(success, mload(add(theta_mptr, 0x260)), mload(add(theta_mptr, 0x280)))
                            }
                        }
                    }
                    pcs_ptr := add(pcs_ptr, 0x20)
                    data := mload(pcs_ptr)
                }
                ret := success
            }

            function pairing_input_computations(len, pcs_ptr, data, theta_mptr, success) -> ret {
                mstore(0x80, calldataload(and(data, PTR_BITMASK)))
                data := shr(16, data)
                mstore(0xa0, calldataload(and(data, PTR_BITMASK)))
                data := shr(16, data)
                for { let i := 0 } lt(i, len) { i := add(i, 0x20) } {
                    for { } data { } {
                        let ptr_loc := and(data, BYTE_FLAG_BITMASK)
                        data := shr(8, data)
                        let comm_len := and(data, BYTE_FLAG_BITMASK)
                        data := shr(8, data)
                        switch comm_len
                        case 0x0 {
                            switch ptr_loc 
                            case 0x00 {
                                for
                                    {
                                        let mptr := and(data, PTR_BITMASK)
                                        data := shr(16, data)
                                        let mptr_end := and(data, PTR_BITMASK)
                                    }
                                    lt(mptr_end, mptr)
                                    { mptr := sub(mptr, 0x40) }
                                {                      
                                    success := ec_mul_tmp(success, mload(add(theta_mptr, 0xA0)))
                                    success := ec_add_tmp(success, mload(mptr), mload(add(mptr, 0x20)))
                                }
                            } 
                            case 0x01 {
                                for
                                    {
                                        let mptr := and(data, PTR_BITMASK)
                                        data := shr(16, data)
                                        let mptr_end := and(data, PTR_BITMASK)
                                    }
                                    lt(mptr_end, mptr)
                                    { mptr := sub(mptr, 0x40) }
                                {                      
                                    success := ec_mul_tmp(success, mload(add(theta_mptr, 0xA0)))
                                    success := ec_add_tmp(success, calldataload(mptr), calldataload(add(mptr, 0x20)))
                                }
                            }
                            data := shr(16, data)
                        } default {
                            switch ptr_loc                        
                            case 0x00 {
                                success := ec_mul_tmp(success, mload(add(theta_mptr, 0xA0)))
                                success := ec_add_tmp(success, mload(and(data, PTR_BITMASK)), mload(and(shr(16,data), PTR_BITMASK)))
                                if eq(comm_len, 0x2) {
                                    data := shr(32, data)
                                    success := ec_mul_tmp(success, mload(add(theta_mptr, 0xA0)))
                                    success := ec_add_tmp(success, mload(and(data, PTR_BITMASK)), mload(and(shr(16,data), PTR_BITMASK)))
                                }
                                data := shr(32, data)
                            }
                            case 0x01 {
                                success := ec_mul_tmp(success, mload(add(theta_mptr, 0xA0)))
                                success := ec_add_tmp(success, calldataload(and(data, PTR_BITMASK)), calldataload(and(shr(16,data), PTR_BITMASK)))
                                if eq(comm_len, 0x2) {
                                    data := shr(32, data)
                                    success := ec_mul_tmp(success, mload(add(theta_mptr, 0xA0)))
                                    success := ec_add_tmp(success, calldataload(and(data, PTR_BITMASK)), calldataload(and(shr(16,data), PTR_BITMASK)))
                                }
                                data := shr(32, data)
                            }
                            // Quotient eval x and y points
                            case 0x02 {
                                success := ec_mul_tmp(success, mload(add(theta_mptr, 0xA0)))
                                success := ec_add_tmp(success, mload(add(theta_mptr, 0x260)), mload(add(theta_mptr, 0x280)))
                            }
                        }
                    }
                    pcs_ptr := add(pcs_ptr, 0x20)
                    data := mload(pcs_ptr)
                }
                ret := success
            }

            // Initialize success as true
            let success := true
            // Initialize vk_mptr as 0x0 on the stack
            let vk_mptr := 0x0
            // Initialize theta_mptr as 0x0 on the stack
            let theta_mptr := 0x0
            {
                // Load in the vk_digest, vk_mptr and vk_len and the rest of the constants needed for the 
                // challenge data generation process.
                extcodecopy(vk, 0x0, 0x00, 0x240)
                // Set the vk_mptr 
                vk_mptr := mload(0x20)
                let vk_len := mload(0x40)

                let instance_cptr := mload({{ vk_const_offsets["instance_cptr"]|hex() }})

                // Check valid length of proof
                success := and(success, eq(sub(instance_cptr, 0xa4), calldataload(PROOF_LEN_CPTR)))

                // Check valid length of instances
                let num_instances := mload({{ vk_const_offsets["num_instances"]|hex() }})
                success := and(success, eq(num_instances, calldataload(sub(instance_cptr,0x20))))


                // Read instances and witness commitments and generate challenges
                let hash_mptr := 0x20

                let proof_cptr := PROOF_CPTR
                let challenge_mptr := add(vk_mptr, vk_len) // challenge_mptr is at the end of vk in memory
                // Set the theta_mptr (vk_mptr + vk_len + challenges_length)
                theta_mptr := add(challenge_mptr, mload({{ vk_const_offsets["challenges_offset"]|hex() }}))

                // Move the challenge length data to the free static memory location for the challenge data generation process.
                let num_words, challenge_len_ptr, challenge_len_data := reposition_challenge_len_data()
                
                let num_evals := mul(0x20, mload({{ vk_const_offsets["num_evals"]|hex() }}))

                for
                    { let instance_cptr_end := add(instance_cptr, mul(0x20, num_instances)) }
                    lt(instance_cptr, instance_cptr_end)
                    {}
                {
                    let instance := calldataload(instance_cptr)
                    success := and(success, lt(instance, R))
                    mstore(hash_mptr, instance)
                    instance_cptr := add(instance_cptr, 0x20)
                    hash_mptr := add(hash_mptr, 0x20)
                }
                
                for { let i := 0 } lt(i, num_words) { i := add(i, 1) } {
                    challenge_len_ptr := add(challenge_len_ptr, 0x20)
                    for { } challenge_len_data { } {
                        // add proof_cpt to num advices len
                        let proof_cptr_end := add(proof_cptr, and(challenge_len_data, PTR_BITMASK))
                        challenge_len_data := shr(16, challenge_len_data)
                        // Phase loop
                        for { } lt(proof_cptr, proof_cptr_end) { } {
                            success, proof_cptr, hash_mptr := read_ec_point(success, proof_cptr, hash_mptr)
                        }
                        // Generate challenges
                        challenge_mptr, hash_mptr := squeeze_challenge(challenge_mptr, hash_mptr)

                        // Continue squeezing challenges based on num_challenges
                        let num_challenges := and(challenge_len_data, BYTE_FLAG_BITMASK)
                        challenge_len_data := shr(8, challenge_len_data)
                        for { let c := 1 } lt(c, num_challenges) { c := add(c, 1) } { 
                            challenge_mptr := squeeze_challenge_cont(challenge_mptr)
                        }
                    }
                    challenge_len_data := mload(challenge_len_ptr)
                }

                // Read evaluations
                for
                    { let proof_cptr_end := add(proof_cptr, num_evals) } // num_evals
                    lt(proof_cptr, proof_cptr_end)
                    {}
                {
                    let eval := calldataload(proof_cptr)
                    success := and(success, lt(eval, R))
                    mstore(hash_mptr, eval)
                    proof_cptr := add(proof_cptr, 0x20)
                    hash_mptr := add(hash_mptr, 0x20)
                }

                // Read batch opening proof and generate challenges
                {%- match scheme %}
                {%- when Bdfg21 %}
                challenge_mptr, hash_mptr := squeeze_challenge(challenge_mptr, hash_mptr)       // zeta
                challenge_mptr := squeeze_challenge_cont(challenge_mptr)                        // nu

                success, proof_cptr, hash_mptr := read_ec_point(success, proof_cptr, hash_mptr) // W

                challenge_mptr, hash_mptr := squeeze_challenge(challenge_mptr, hash_mptr)       // mu

                success, proof_cptr, hash_mptr := read_ec_point(success, proof_cptr, hash_mptr) // W'
                {%- when Gwc19 %}
                // TODO
                {%- endmatch %}

                // Copy full vk into memory (some parts were overwritten during the challenge generation)
                extcodecopy(vk, vk_mptr, 0x00, vk_len)

                // Read accumulator from instances
                if mload(add(vk_mptr, {{ vk_const_offsets["has_accumulator"]|hex() }})) {
                    let num_limbs := mload(add(vk_mptr, {{ vk_const_offsets["num_acc_limbs"]|hex() }}))
                    let num_limb_bits := mload(add(vk_mptr, {{ vk_const_offsets["num_acc_limb_bits"]|hex() }}))

                    let cptr := add(mload(add(vk_mptr, {{ vk_const_offsets["instance_cptr"]|hex() }})), mul(mload(add(vk_mptr, {{ vk_const_offsets["acc_offset"]|hex() }})), 0x20))
                    let lhs_y_off := mul(num_limbs, 0x20)
                    let rhs_x_off := mul(lhs_y_off, 2)
                    let rhs_y_off := mul(lhs_y_off, 3)
                    let lhs_x := calldataload(cptr)
                    let lhs_y := calldataload(add(cptr, lhs_y_off))
                    let rhs_x := calldataload(add(cptr, rhs_x_off))
                    let rhs_y := calldataload(add(cptr, rhs_y_off))
                    for
                        {
                            let cptr_end := add(cptr, mul(0x20, num_limbs))
                            let shift := num_limb_bits
                        }
                        lt(cptr, cptr_end)
                        {}
                    {
                        cptr := add(cptr, 0x20)
                        lhs_x := add(lhs_x, shl(shift, calldataload(cptr)))
                        lhs_y := add(lhs_y, shl(shift, calldataload(add(cptr, lhs_y_off))))
                        rhs_x := add(rhs_x, shl(shift, calldataload(add(cptr, rhs_x_off))))
                        rhs_y := add(rhs_y, shl(shift, calldataload(add(cptr, rhs_y_off))))
                        shift := add(shift, num_limb_bits)
                    }

                    success := and(success, eq(mulmod(lhs_y, lhs_y, Q), addmod(mulmod(lhs_x, mulmod(lhs_x, lhs_x, Q), Q), 3, Q)))
                    success := and(success, eq(mulmod(rhs_y, rhs_y, Q), addmod(mulmod(rhs_x, mulmod(rhs_x, rhs_x, Q), Q), 3, Q)))

                    mstore(add(theta_mptr, 0x100), lhs_x)
                    mstore(add(theta_mptr, 0x120), lhs_y)
                    mstore(add(theta_mptr, 0x140), rhs_x)
                    mstore(add(theta_mptr, 0x160), rhs_y)
                }

            }

            // Revert earlier if anything from calldata is invalid
            if iszero(success) {
                revert(0, 0)
            }


            // Compute lagrange evaluations and instance evaluation
            {
                let k := mload(add(vk_mptr, {{ vk_const_offsets["k"]|hex() }}))
                let x := mload(add(theta_mptr, 0x80))
                let x_n := x
                for
                    { let idx := 0 }
                    lt(idx, k)
                    { idx := add(idx, 1) }
                {
                    x_n := mulmod(x_n, x_n, R)
                }

                let omega := mload(add(vk_mptr, {{ vk_const_offsets["omega"]|hex() }}))
                let x_n_mptr := add(theta_mptr, 0x180)
                let mptr := x_n_mptr
                let num_instances := mload(add(vk_mptr, {{ vk_const_offsets["num_instances"]|hex() }}))
                let num_neg_lagranges := mload(add(vk_mptr, {{ vk_const_offsets["num_neg_lagranges"]|hex() }}))
                let mptr_end := add(mptr, mul(0x20, add(num_instances, num_neg_lagranges)))
                if iszero(num_instances) {
                    mptr_end := add(mptr_end, 0x20)
                }
                for
                    { let pow_of_omega := mload(add(vk_mptr, {{ vk_const_offsets["omega_inv_to_l"]|hex() }})) }
                    lt(mptr, mptr_end)
                    { mptr := add(mptr, 0x20) }
                {
                    mstore(mptr, addmod(x, sub(R, pow_of_omega),R))
                    pow_of_omega := mulmod(pow_of_omega, omega,R)
                }
                let x_n_minus_1 := addmod(x_n, sub(R, 1),R)
                mstore(mptr_end, x_n_minus_1)
                success := batch_invert(success, x_n_mptr, add(mptr_end, 0x20))

                mptr := x_n_mptr
                let l_i_common := mulmod(x_n_minus_1, mload(add(vk_mptr, {{ vk_const_offsets["n_inv"]|hex() }})),R)
                for
                    { let pow_of_omega := mload(add(vk_mptr, {{ vk_const_offsets["omega_inv_to_l"]|hex() }})) }
                    lt(mptr, mptr_end)
                    { mptr := add(mptr, 0x20) }
                {
                    mstore(mptr, mulmod(l_i_common, mulmod(mload(mptr), pow_of_omega,R),R))
                    pow_of_omega := mulmod(pow_of_omega, omega,R)
                }

                let l_blind := mload(add(x_n_mptr, 0x20))
                let l_i_cptr := add(x_n_mptr, 0x40)
                for
                    { let l_i_cptr_end := add(x_n_mptr, mul(0x20, num_neg_lagranges)) }
                    lt(l_i_cptr, l_i_cptr_end)
                    { l_i_cptr := add(l_i_cptr, 0x20) }
                {
                    l_blind := addmod(l_blind, mload(l_i_cptr),R)
                }

                let instance_eval := 0
                for
                    {
                        let instance_cptr := mload(add(vk_mptr, {{ vk_const_offsets["instance_cptr"]|hex() }}))
                        let instance_cptr_end := add(instance_cptr, mul(0x20, num_instances))
                    }
                    lt(instance_cptr, instance_cptr_end)
                    {
                        instance_cptr := add(instance_cptr, 0x20)
                        l_i_cptr := add(l_i_cptr, 0x20)
                    }
                {
                    instance_eval := addmod(instance_eval, mulmod(mload(l_i_cptr), calldataload(instance_cptr),R),R)
                }

                let x_n_minus_1_inv := mload(mptr_end)
                let l_last := mload(x_n_mptr)
                let l_0 := mload(add(x_n_mptr, mul(0x20, num_neg_lagranges)))

                mstore(x_n_mptr, x_n)
                mstore(add(theta_mptr, 0x1a0), x_n_minus_1_inv)
                mstore(add(theta_mptr, 0x1c0), l_last)
                mstore(add(theta_mptr, 0x1e0), l_blind)
                mstore(add(theta_mptr, 0x200), l_0)
                mstore(add(theta_mptr, 0x220), instance_eval)
            }


            // Compute quotient evaluation
            {
                let quotient_eval_numer
                let y := mload(add(theta_mptr, 0x60))
                {
                    // Gate computations / expression evaluations.
                    let computations_ptr, computations_len := soa_layout_metadata({{ vk_const_offsets["gate_computations_len_offset"]|hex() }}, vk_mptr)
                    let expressions_word := mload(computations_ptr) 
                    let last_idx
                    // Load in the total number of code blocks from the vk constants, right after the number challenges
                    for { let code_block := 0 } lt(code_block, computations_len) { code_block := add(code_block, 0x20) } {
                        // call expression_evals to evaluate the expressions in the code block
                        computations_ptr, expressions_word, last_idx := expression_evals_packed(0x00, computations_ptr, expressions_word)

                        // at the end of each code block we update `quotient_eval_numer`
                        // If this is the first code block, we set `quotient_eval_numer` to the last var in the code block
                        switch eq(code_block, 0)
                        case 1 {
                            quotient_eval_numer := mload(last_idx)
                        }
                        case 0 {
                            // Otherwise we add the last var in the code block to `quotient_eval_numer` mod r
                            quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, R), mload(last_idx), R)
                        }
                    }
                }
                {
                    // Permutation computations
                    let permutation_z_evals_ptr := add(vk_mptr, mload(add(vk_mptr, {{ vk_const_offsets["permutation_computations_len_offset"]|hex() }})))
                    let permutation_z_evals := mload(permutation_z_evals_ptr)
                    // Last idx of permutation evals == permutation_evals.len() - 1
                    let last_idx := and(permutation_z_evals, BYTE_FLAG_BITMASK)
                    permutation_z_evals := shr(8, permutation_z_evals)
                    // Num of words scaled by 0x20 that take up each permutation eval (permutation_z_eval + column evals)
                    // first and second LSG bytes contain the number of words for all of the permutation evals except the last.
                    // The third and fourth LSG bytes contain the number of words for the last permutation eval
                    let num_words := and(permutation_z_evals, 0xFFFFFFFF)
                    permutation_z_evals := shr(32, permutation_z_evals)
                    permutation_z_evals_ptr := add(permutation_z_evals_ptr, 0x20)
                    permutation_z_evals := mload(permutation_z_evals_ptr)
                    let l_0 := mload(add(theta_mptr, 0x200))
                    {            
                        // Get the first and second LSG bytes from the first permutation_z_evals word to load in (z, _, _)
                        let eval := addmod(l_0, sub(R, mulmod(l_0, calldataload(and(permutation_z_evals, PTR_BITMASK)), R)), R)
                        quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, R), eval, R)
                    }

                    {   
                        // Load in the last permutation_z_evals word
                        let perm_z_last_ptr := add(mul(last_idx, and(num_words, PTR_BITMASK)), permutation_z_evals_ptr)
                        let perm_z_last := calldataload(and(mload(perm_z_last_ptr), PTR_BITMASK))
                        quotient_eval_numer := addmod(
                            mulmod(quotient_eval_numer, y, R), 
                            mulmod(
                                mload(add(theta_mptr, 0x1C0)), 
                                addmod(
                                    mulmod(perm_z_last, perm_z_last, R), 
                                    sub(R, perm_z_last), 
                                    R
                                ), 
                                R
                            ), 
                            R
                        )

                        mstore(0x00, mulmod(mload(add(theta_mptr, 0x20)), mload(add(theta_mptr, 0x80)), R))

                        quotient_eval_numer := z_evals(
                            permutation_z_evals, 
                            num_words, 
                            perm_z_last_ptr, 
                            permutation_z_evals_ptr, 
                            theta_mptr,
                            l_0,
                            y, 
                            quotient_eval_numer
                        )
                    }
                }
                {
                    // MV lookup computations 
                    mstore(0x0, mload(add(theta_mptr, 0x1C0))) // l_last
                    mstore(0x20, mload(add(theta_mptr, 0x200))) // l_0
                    mstore(0x40, mload(add(theta_mptr, 0x1E0))) // l_blind
                    mstore(0x60, mload(theta_mptr)) // theta
                    mstore(0x80, mload(add(theta_mptr, 0x20))) // beta
                    let evals_ptr, meta_data := soa_layout_metadata({{ 
                        vk_const_offsets["lookup_computations_len_offset"]|hex()
                    }}, vk_mptr)
                    // lookup meta data contains 32 byte flags for indicating if we need to do a lookup table lines 
                    // expression evaluation or we can use the previous one cached in the table var. 
                    if meta_data {
                        let table
                        let end_ptr := and(meta_data, PTR_BITMASK)
                        let mv := and(shr(16, meta_data), BYTE_FLAG_BITMASK)
                        switch mv
                        case 0x0 {
                            for { } lt(evals_ptr, end_ptr) { } {
                                evals_ptr, table, quotient_eval_numer := mv_lookup_evals(table, evals_ptr, quotient_eval_numer, y)
                            }
                        } 
                        case 0x1 {
                            mstore(0xA0, mload(add(theta_mptr, 0x40))) // gamma
                            for { } lt(evals_ptr, end_ptr) { } {
                                evals_ptr, table, quotient_eval_numer := lookup_evals(table, evals_ptr, quotient_eval_numer, y)
                            }
                        }
                    }
                }

                pop(y)

                mstore(add(theta_mptr, 0x240), mulmod(quotient_eval_numer, mload(add(theta_mptr, 0x1a0)), R))

            }

            // Compute quotient commitment
            {
                mstore(0x00, calldataload(mload(add(vk_mptr, {{ vk_const_offsets["last_quotient_x_cptr"]|hex() }}))))
                mstore(0x20, calldataload(add(mload(add(vk_mptr, {{ vk_const_offsets["last_quotient_x_cptr"]|hex() }})), 0x20)))
                let x_n := mload(add(theta_mptr, 0x180))
                for
                    {
                        let cptr := sub(mload(add(vk_mptr, {{ vk_const_offsets["last_quotient_x_cptr"]|hex() }})), 0x40)
                        let cptr_end := sub(mload(add(vk_mptr, {{ vk_const_offsets["first_quotient_x_cptr"]|hex() }})), 0x40)
                    }
                    lt(cptr_end, cptr)
                    {}
                {
                    success := ec_mul_acc(success, x_n)
                    success := ec_add_acc(success, calldataload(cptr), calldataload(add(cptr, 0x20)))
                    cptr := sub(cptr, 0x40)
                }
                mstore(add(theta_mptr, 0x260), mload(0x00))
                mstore(add(theta_mptr, 0x280), mload(0x20))
            }

            // Compute pairing lhs and rhs
            {
                // point_computations 
                let pcs_ptr := add(vk_mptr, mload(add(vk_mptr, {{ vk_const_offsets["pcs_computations_len_offset"]|hex() }})))
                {
                    let point_computations := mload(pcs_ptr)
                    let x := mload(add(theta_mptr, 0x80))
                    let omega := mload(add(vk_mptr, {{ vk_const_offsets["omega"]|hex() }}))
                    let omega_inv := mload(add(vk_mptr, {{ vk_const_offsets["omega_inv"]|hex() }}))
                    let x_pow_of_omega := mulmod(x, omega, R)
                    x_pow_of_omega, pcs_ptr := point_rots(point_computations, pcs_ptr, 8, x_pow_of_omega, omega)
                    pcs_ptr := add(pcs_ptr, 0x20)
                    point_computations := mload(pcs_ptr)
                    // Store interm point
                    mstore(and(point_computations, PTR_BITMASK), x)
                    x_pow_of_omega := mulmod(x, omega_inv, R)
                    point_computations := shr(16, point_computations)
                    x_pow_of_omega, pcs_ptr := point_rots(point_computations, pcs_ptr, 24, x_pow_of_omega, omega_inv)
                    pcs_ptr := add(pcs_ptr, 0x20)
                    pop(x_pow_of_omega)
                }

                // vanishing_computations 
                {
                    let mu := mload(add(theta_mptr, 0xE0))
                    let vanishing_computations := mload(pcs_ptr)
                    mstore(0x20, 1)
                    for
                        {
                            let mptr := and(vanishing_computations, PTR_BITMASK)
                            vanishing_computations := shr(16, vanishing_computations)
                            let mptr_end := and(vanishing_computations, PTR_BITMASK)
                            vanishing_computations := shr(16, vanishing_computations)
                            let point_mptr := and(vanishing_computations, PTR_BITMASK)
                        }
                        lt(mptr, mptr_end)
                        {
                            mptr := add(mptr, 0x20)
                            point_mptr := add(point_mptr, 0x20)
                        }
                    {
                        mstore(mptr, addmod(mu, sub(R, mload(point_mptr)), R))
                    }
                    pop(mu)
                    vanishing_computations := shr(16, vanishing_computations)
                    let num_words := and(vanishing_computations, BYTE_FLAG_BITMASK)
                    vanishing_computations := shr(8, vanishing_computations)
                    let s := mload(and(vanishing_computations, PTR_BITMASK))
                    vanishing_computations := shr(16, vanishing_computations)
                    for { let i } lt(i, num_words) { i := add(i, 1) } {
                        for {  } vanishing_computations {  } {
                            s := mulmod(s, mload(and(vanishing_computations, PTR_BITMASK)), R)
                            vanishing_computations := shr(16, vanishing_computations)
                        }    
                        pcs_ptr := add(pcs_ptr, 0x20)
                        vanishing_computations := mload(pcs_ptr)
                    }
                    let diff_ptr := and(vanishing_computations, PTR_BITMASK)
                    mstore(diff_ptr, s)
                    vanishing_computations := shr(16, vanishing_computations)
                    let diff
                    let sets_len := and(vanishing_computations, PTR_BITMASK)
                    pcs_ptr := add(pcs_ptr, 0x20)
                    vanishing_computations := mload(pcs_ptr)
                    for { let i := 0 } lt(i, sets_len) { i := add(i, 1) } {
                        diff := mload(and(vanishing_computations, PTR_BITMASK))
                        vanishing_computations := shr(16, vanishing_computations)
                        for { } vanishing_computations { } {
                            diff := mulmod(diff, mload(and(vanishing_computations, PTR_BITMASK)), R)
                            vanishing_computations := shr(16, vanishing_computations)
                        }
                        diff_ptr := add(0x20, diff_ptr)
                        mstore(diff_ptr, diff)
                        if eq(i, 0) {
                            mstore(0x00, diff)
                        }
                        pcs_ptr := add(pcs_ptr, 0x20)
                        vanishing_computations := mload(pcs_ptr)
                    }
                }
                // coeff_computations
                {
                    let coeff_len_data := mload(pcs_ptr)
                    // Load in the least significant byte of the `coeff_len_data` word to get the total number of words we will need to load in
                    // that contains the packed Vec<set.rots().len()>. 
                    let end_ptr_packed_lens := add(pcs_ptr, mul(0x20, and(coeff_len_data, BYTE_FLAG_BITMASK)))
                    coeff_len_data := shr(8, coeff_len_data)
                    let i := pcs_ptr
                    pcs_ptr := end_ptr_packed_lens
                    for {  } lt(i, end_ptr_packed_lens) { i := add(i, 0x20) } {
                        for {  } coeff_len_data { } {
                            coeff_len_data := coeff_computations(coeff_len_data, mload(pcs_ptr))
                            pcs_ptr := add(pcs_ptr, 0x20)
                        }
                        coeff_len_data := mload(add(i, 0x20))
                    }
                }
                // normalized_coeff_computations
                {
                    let norm_coeff_data := mload(pcs_ptr)
                    success := batch_invert(success, 0, and(norm_coeff_data, PTR_BITMASK))
                    norm_coeff_data := shr(16, norm_coeff_data)
                    let diff_0_inv := mload(0x00)
                    let mptr0 := and(norm_coeff_data, PTR_BITMASK)
                    norm_coeff_data := shr(16, norm_coeff_data)
                    mstore(mptr0, diff_0_inv)
                    for
                        {
                            let mptr := add(mptr0, 0x20)
                            let mptr_end := add(mptr0, and(norm_coeff_data, PTR_BITMASK))
                        }
                        lt(mptr, mptr_end)
                        { mptr := add(mptr, 0x20) }
                    {
                        mstore(mptr, mulmod(mload(mptr), diff_0_inv, R))
                    }
                    pcs_ptr := add(pcs_ptr, 0x20)
                }
                let coeff_ptr := 0x20
                // r_evals_computations
                {
                    let r_evals_meta_data := mload(pcs_ptr)
                    let end_ptr_packed_lens := add(pcs_ptr, mul(0x20, and(r_evals_meta_data, BYTE_FLAG_BITMASK)))
                    r_evals_meta_data := shr(8, r_evals_meta_data)
                    let set_coeff := and(r_evals_meta_data, PTR_BITMASK)
                    r_evals_meta_data := shr(16, r_evals_meta_data)
                    let r_eval_mptr := and(r_evals_meta_data, PTR_BITMASK)
                    r_evals_meta_data := shr(16, r_evals_meta_data)
                    let i := pcs_ptr
                    pcs_ptr := end_ptr_packed_lens
                    let zeta := mload(add(theta_mptr, 0xA0))
                    let quotient_eval := mload(add(theta_mptr, 0x240))
                    let not_first
                    let r_eval
                    for {  } lt(i, end_ptr_packed_lens) { i := add(i, 0x20) } {
                        for {  } r_evals_meta_data { } {
                            r_eval, pcs_ptr := r_evals_computation(and(r_evals_meta_data, BYTE_FLAG_BITMASK), pcs_ptr, zeta, quotient_eval, coeff_ptr)
                            coeff_ptr := add(coeff_ptr, and(r_evals_meta_data, BYTE_FLAG_BITMASK))
                            r_evals_meta_data := shr(8, r_evals_meta_data)
                            if not_first {
                                r_eval := mulmod(r_eval, mload(set_coeff), R)
                                set_coeff := add(set_coeff, 0x20)
                            }
                            not_first := 1
                            mstore(r_eval_mptr, r_eval)
                            r_eval_mptr := add(r_eval_mptr, 0x20)
                        }
                        r_evals_meta_data := mload(add(i, 0x20))
                    }
                }
                // coeff_sums_computation
                {
                    let coeff_sums_data := mload(pcs_ptr)
                    let end_ptr_packed_lens := add(pcs_ptr, mul(0x20, and(coeff_sums_data, BYTE_FLAG_BITMASK)))
                    coeff_sums_data := shr(8, coeff_sums_data)
                    coeff_ptr := 0x20
                    let i := pcs_ptr
                    pcs_ptr := end_ptr_packed_lens
                    for {  } lt(i, end_ptr_packed_lens) { i := add(i, 0x20) } {
                        for {  } coeff_sums_data { } {
                            let sum := mload(coeff_ptr) 
                            let len := and(coeff_sums_data, BYTE_FLAG_BITMASK)
                            coeff_sums_data := shr(8, coeff_sums_data)
                            for { let j := 0x20 } lt(j, len) { j := add(j, 0x20) } {
                                sum := addmod(sum, mload(add(coeff_ptr, j)), R)
                            }
                            coeff_ptr := add(coeff_ptr, len)
                            mstore(and(coeff_sums_data, PTR_BITMASK), sum)
                            coeff_sums_data := shr(16, coeff_sums_data)
                        }
                        coeff_sums_data := mload(add(i, 0x20))
                    }

                }
                // r_eval_computation
                {
                    let r_eval_data := mload(pcs_ptr)
                    let mptr_end := and(r_eval_data, PTR_BITMASK)                    
                    for
                        {
                            let mptr := 0x00
                            r_eval_data := shr(16, r_eval_data)
                            let sum_mptr := and(r_eval_data, PTR_BITMASK)
                        }
                        lt(mptr, mptr_end)
                        {
                            mptr := add(mptr, 0x20)
                            sum_mptr := add(sum_mptr, 0x20)
                        }
                    {
                        mstore(mptr, mload(sum_mptr))
                    }
                    r_eval_data := shr(16, r_eval_data)
                    success := batch_invert(success, 0, mptr_end)
                    let r_eval_ptr := and(r_eval_data, PTR_BITMASK)
                    let r_eval := mulmod(mload(sub(mptr_end, 0x20)), mload(r_eval_ptr), R)
                    r_eval_data := shr(16, r_eval_data)
                    for
                        {
                            let sum_inv_mptr := sub(mptr_end, 0x40)
                            let sum_inv_mptr_end := mptr_end
                            let r_eval_mptr := sub(r_eval_ptr, 0x20)
                        }
                        lt(sum_inv_mptr, sum_inv_mptr_end)
                        {
                            sum_inv_mptr := sub(sum_inv_mptr, 0x20)
                            r_eval_mptr := sub(r_eval_mptr, 0x20)
                        }
                    {
                        r_eval := mulmod(r_eval, mload(add(theta_mptr, 0xC0)), R)
                        r_eval := addmod(r_eval, mulmod(mload(sum_inv_mptr), mload(r_eval_mptr), R), R)
                    }
                    mstore(add(theta_mptr, 0x2A0), r_eval)
                    pcs_ptr := add(pcs_ptr, 0x20)
                }
                // pairing_input_computations
                let nu := mload(add(theta_mptr, 0xC0))
                {
                    let pairing_input_meta_data := mload(pcs_ptr)
                    let end_ptr_packed_lens := add(pcs_ptr, mul(0x20, and(pairing_input_meta_data, BYTE_FLAG_BITMASK)))
                    pairing_input_meta_data := shr(8, pairing_input_meta_data)
                    let set_coeff := and(pairing_input_meta_data, PTR_BITMASK)
                    pairing_input_meta_data := shr(16, pairing_input_meta_data)
                    let ec_points_cptr_packed := and(pairing_input_meta_data, 0xFFFFFFFFFFFFFFFFFFFF)
                    pairing_input_meta_data := shr(80, pairing_input_meta_data)
                    let i := pcs_ptr
                    pcs_ptr := end_ptr_packed_lens
                    let first := 1
                    for {  } lt(i, end_ptr_packed_lens) { i := add(i, 0x20) } {
                        for {  } pairing_input_meta_data { } {
                            let len := and(pairing_input_meta_data, BYTE_FLAG_BITMASK)
                            pairing_input_meta_data := shr(8, pairing_input_meta_data)
                            if first {
                                first := 0
                                success := pairing_input_computations_first(len, pcs_ptr, mload(pcs_ptr), theta_mptr, success)
                                pcs_ptr := add(pcs_ptr, len)
                                continue
                            }
                            success := pairing_input_computations(len, pcs_ptr, mload(pcs_ptr), theta_mptr, success)
                            pcs_ptr := add(pcs_ptr, len)
                            success := ec_mul_tmp(success, mulmod(nu, mload(set_coeff), R))
                            set_coeff := add(set_coeff, 0x20)
                            success := ec_add_acc(success, mload(0x80), mload(0xa0))
                            // execute this if statement if not the last set
                            if or(0x1, lt(i, sub(end_ptr_packed_lens, 0x20))) {
                                nu := mulmod(nu, mload(add(theta_mptr, 0xC0)), R)
                            }
                        }
                        pairing_input_meta_data := mload(add(i, 0x20))
                    }
                    mstore(0x80, mload(add(vk_mptr, {{ vk_const_offsets["g1_x"]|hex() }})))
                    mstore(0xa0, mload(add(vk_mptr, {{ vk_const_offsets["g1_y"]|hex() }})))
                    success := ec_mul_tmp(success, sub(R, mload(add(theta_mptr, 0x2A0))))
                    success := ec_add_acc(success, mload(0x80), mload(0xa0))
                    mstore(0x80, calldataload(and(ec_points_cptr_packed, PTR_BITMASK)))
                    ec_points_cptr_packed := shr(16, ec_points_cptr_packed)
                    mstore(0xa0, calldataload(and(ec_points_cptr_packed, PTR_BITMASK)))
                    ec_points_cptr_packed := shr(16, ec_points_cptr_packed)
                    success := ec_mul_tmp(success, sub(R, mload(and(ec_points_cptr_packed, PTR_BITMASK))))
                    ec_points_cptr_packed := shr(16, ec_points_cptr_packed)
                    success := ec_add_acc(success, mload(0x80), mload(0xa0))
                    let w_prime_x := calldataload(and(ec_points_cptr_packed, PTR_BITMASK))
                    ec_points_cptr_packed := shr(16, ec_points_cptr_packed)
                    let w_prime_y := calldataload(and(ec_points_cptr_packed, PTR_BITMASK))
                    mstore(0x80, w_prime_x)
                    mstore(0xa0, w_prime_y)
                    success := ec_mul_tmp(success, mload(add(theta_mptr, 0xE0)))
                    success := ec_add_acc(success, mload(0x80), mload(0xa0))
                    mstore(add(theta_mptr, 0x2C0), mload(0x00))
                    mstore(add(theta_mptr, 0x2E0), mload(0x20))
                    mstore(add(theta_mptr, 0x300), w_prime_x)
                    mstore(add(theta_mptr, 0x320), w_prime_y)
                }
            }

            // Random linear combine with accumulator
            if mload(add(vk_mptr, {{ vk_const_offsets["has_accumulator"]|hex() }})) {
                mstore(0x00, mload(add(theta_mptr, 0x100)))
                mstore(0x20, mload(add(theta_mptr, 0x120)))
                mstore(0x40, mload(add(theta_mptr, 0x140)))
                mstore(0x60, mload(add(theta_mptr, 0x160)))
                mstore(0x80, mload(add(theta_mptr, 0x2c0)))
                mstore(0xa0, mload(add(theta_mptr, 0x2e0)))
                mstore(0xc0, mload(add(theta_mptr, 0x300)))
                mstore(0xe0, mload(add(theta_mptr, 0x320)))
                let challenge := mod(keccak256(0x00, 0x100), R)

                // [pairing_lhs] += challenge * [acc_lhs]
                success := ec_mul_acc(success, challenge)
                success := ec_add_acc(success, mload(add(theta_mptr, 0x2c0)), mload(add(theta_mptr, 0x2e0)))
                mstore(add(theta_mptr, 0x2c0), mload(0x00))
                mstore(add(theta_mptr, 0x2e0), mload(0x20))

                // [pairing_rhs] += challenge * [acc_rhs]
                mstore(0x00, mload(add(theta_mptr, 0x140)))
                mstore(0x20, mload(add(theta_mptr, 0x160)))
                success := ec_mul_acc(success, challenge)
                success := ec_add_acc(success, mload(add(theta_mptr, 0x300)), mload(add(theta_mptr, 0x320)))
                mstore(add(theta_mptr, 0x300), mload(0x00))
                mstore(add(theta_mptr, 0x320), mload(0x20))
            }

            // Perform pairing
            success := ec_pairing(
                success,
                vk_mptr,
                mload(add(theta_mptr, 0x2c0)),
                mload(add(theta_mptr, 0x2e0)),
                mload(add(theta_mptr, 0x300)),
                mload(add(theta_mptr, 0x320))
            )

            // Revert if anything fails
            if iszero(success) {
                revert(0x00, 0x00)
            }

            // Return 1 as result if everything succeeds
            mstore(0x00, 1)
            return(0x00, 0x20)
        }
    }
}
