// SPDX-License-Identifier: MIT

pragma solidity ^0.8.0;

contract Halo2Verifier {
    uint256 internal constant    PROOF_LEN_CPTR = 0x64;
    uint256 internal constant    PROOF_CPTR = 0x84;
    uint256 internal constant    Q = 21888242871839275222246405745257275088696311157297823662689037894645226208583;
    uint256 internal constant    DELTA = 4131629893567559867359510883348571134090853742863529169391034518566172092834;



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
            function squeeze_challenge(challenge_mptr, hash_mptr, r) -> ret0, ret1 {
                let hash := keccak256(0x00, hash_mptr)
                mstore(challenge_mptr, mod(hash, r))
                mstore(0x00, hash)
                ret0 := add(challenge_mptr, 0x20)
                ret1 := 0x20
            }

            // Squeeze challenge without absorbing new input from calldata,
            // by putting an extra 0x01 in memory[0x20] and squeeze by keccak256(memory[0..21]),
            // and store hash mod r as challenge in challenge_mptr,
            // and push back hash in 0x00 as the first input for next squeeze.
            // Return updated (challenge_mptr).
            function squeeze_challenge_cont(challenge_mptr, r) -> ret {
                mstore8(0x20, 0x01)
                let hash := keccak256(0x00, 0x21)
                mstore(challenge_mptr, mod(hash, r))
                mstore(0x00, hash)
                ret := add(challenge_mptr, 0x20)
            }

            // Batch invert values in memory[mptr_start..mptr_end] in place.
            // Return updated (success).
            function batch_invert(success, mptr_start, mptr_end, r) -> ret {
                let gp_mptr := mptr_end
                let gp := mload(mptr_start)
                let mptr := add(mptr_start, 0x20)
                for
                    {}
                    lt(mptr, sub(mptr_end, 0x20))
                    {}
                {
                    gp := mulmod(gp, mload(mptr), r)
                    mstore(gp_mptr, gp)
                    mptr := add(mptr, 0x20)
                    gp_mptr := add(gp_mptr, 0x20)
                }
                gp := mulmod(gp, mload(mptr), r)

                mstore(gp_mptr, 0x20)
                mstore(add(gp_mptr, 0x20), 0x20)
                mstore(add(gp_mptr, 0x40), 0x20)
                mstore(add(gp_mptr, 0x60), gp)
                mstore(add(gp_mptr, 0x80), sub(r, 2))
                mstore(add(gp_mptr, 0xa0), r)
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
                    let inv := mulmod(all_inv, mload(gp_mptr), r)
                    all_inv := mulmod(all_inv, mload(mptr), r)
                    mstore(mptr, inv)
                    mptr := sub(mptr, 0x20)
                    gp_mptr := sub(gp_mptr, 0x20)
                }
                let inv_first := mulmod(all_inv, mload(second_mptr), r)
                let inv_second := mulmod(all_inv, mload(first_mptr), r)
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
                mstore(0x40, mload(add(vk_mptr, 0x0260)))
                mstore(0x60, mload(add(vk_mptr, 0x0280)))
                mstore(0x80, mload(add(vk_mptr, 0x02a0)))
                mstore(0xa0, mload(add(vk_mptr, 0x02c0)))
                mstore(0xc0, rhs_x)
                mstore(0xe0, rhs_y)
                mstore(0x100, mload(add(vk_mptr, 0x02e0)))
                mstore(0x120, mload(add(vk_mptr, 0x0300)))
                mstore(0x140, mload(add(vk_mptr, 0x0320)))
                mstore(0x160, mload(add(vk_mptr, 0x0340)))
                ret := and(success, staticcall(gas(), 0x08, 0x00, 0x180, 0x00, 0x20))
                ret := and(ret, mload(0x00))
            }

            // Modulus
            let r := 21888242871839275222246405745257275088548364400416034343698204186575808495617 // BN254 scalar field

            // Initialize success as true
            let success := true
            // Initialize vk_mptr as 0x0 on the stack
            let vk_mptr := 0x0
            // Initialize theta_mptr as 0x0 on the stack
            let theta_mptr := 0x0
            {
                // Load in the vk_digest, vk_mptr and vk_len
                extcodecopy(vk, 0x0, 0x00, 0x60)
                // Set the vk_mptr 
                vk_mptr := mload(0x20)
                let vk_len := mload(0x40)
                // Copy full vk into memory
                extcodecopy(vk, vk_mptr, 0x00, vk_len)

                let instance_cptr := mload(add(vk_mptr, 0xe0))

                // Check valid length of proof
                success := and(success, eq(sub(instance_cptr, 0xa4), calldataload(PROOF_LEN_CPTR)))

                // Check valid length of instances
                let num_instances := mload(add(vk_mptr,0x60))
                success := and(success, eq(num_instances, calldataload(sub(instance_cptr,0x20))))

                // Read instances and witness commitments and generate challenges
                let hash_mptr := 0x20
                for
                    { let instance_cptr_end := add(instance_cptr, mul(0x20, num_instances)) }
                    lt(instance_cptr, instance_cptr_end)
                    {}
                {
                    let instance := calldataload(instance_cptr)
                    success := and(success, lt(instance, r))
                    mstore(hash_mptr, instance)
                    instance_cptr := add(instance_cptr, 0x20)
                    hash_mptr := add(hash_mptr, 0x20)
                }

                let proof_cptr := PROOF_CPTR
                let challenge_mptr := add(vk_mptr, vk_len) // challenge_mptr is at the end of vk in memory
                // Set the theta_mptr (vk_mptr + vk_len + challenges_length)
                theta_mptr := add(challenge_mptr, mload(add(vk_mptr, 0x0360)))
                let num_advices_ptr := add(vk_mptr, mload(add(vk_mptr, 0x80)))
                let num_advices_len := mload(num_advices_ptr)
                let advices_ptr := add(num_advices_ptr, 0x20) // start of advices
                let challenges_ptr := add(advices_ptr, 0x20) // start of challenges

                // Iterate over phases using the loaded num_advices and num_challenges
                for { let phase := 0 } lt(phase, num_advices_len) { phase := add(phase, 1) } {
                    // Calculate proof_cptr_end based on num_advices
                    let proof_cptr_end := add(proof_cptr, mul(0x40, mload(add(advices_ptr, mul(phase, 0x40))))) // We use 0x40 because each advice is followed by the corresponding challenge

                    // Phase loop
                    for { } lt(proof_cptr, proof_cptr_end) { } {
                        success, proof_cptr, hash_mptr := read_ec_point(success, proof_cptr, hash_mptr)
                    }

                    // Generate challenges
                    challenge_mptr, hash_mptr := squeeze_challenge(challenge_mptr, hash_mptr, r)

                    // Continue squeezing challenges based on num_challenges
                    for { let c := 1 } lt(c, mload(add(challenges_ptr, mul(phase, 0x40)))) { c := add(c, 1) } { // We 
                        challenge_mptr := squeeze_challenge_cont(challenge_mptr, r)
                    }
                }

                // Read evaluations
                for
                    { let proof_cptr_end := add(proof_cptr, {{ (32 * num_evals)|hex() }}) }
                    lt(proof_cptr, proof_cptr_end)
                    {}
                {
                    let eval := calldataload(proof_cptr)
                    success := and(success, lt(eval, r))
                    mstore(hash_mptr, eval)
                    proof_cptr := add(proof_cptr, 0x20)
                    hash_mptr := add(hash_mptr, 0x20)
                }

                // Read batch opening proof and generate challenges
                {%- match scheme %}
                {%- when Bdfg21 %}
                challenge_mptr, hash_mptr := squeeze_challenge(challenge_mptr, hash_mptr, r)       // zeta
                challenge_mptr := squeeze_challenge_cont(challenge_mptr, r)                        // nu

                success, proof_cptr, hash_mptr := read_ec_point(success, proof_cptr, hash_mptr) // W

                challenge_mptr, hash_mptr := squeeze_challenge(challenge_mptr, hash_mptr, r)       // mu

                success, proof_cptr, hash_mptr := read_ec_point(success, proof_cptr, hash_mptr) // W'
                {%- when Gwc19 %}
                // TODO
                {%- endmatch %}

                // Copy full vk into memory
                extcodecopy(vk, vk_mptr, 0x00, vk_len)

                // Read accumulator from instances
                if mload(add(vk_mptr, 0x01a0)) {
                    let num_limbs := mload(add(vk_mptr, 0x01e0))
                    let num_limb_bits := mload(add(vk_mptr, 0x0200))

                    let cptr := add(mload(add(vk_mptr, 0xe0)), mul(mload(add(vk_mptr, 0x01c0)), 0x20))
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
                let k := mload(add(vk_mptr, 0x100))
                let x := mload(add(theta_mptr, 0x80))
                let x_n := x
                for
                    { let idx := 0 }
                    lt(idx, k)
                    { idx := add(idx, 1) }
                {
                    x_n := mulmod(x_n, x_n, r)
                }

                let omega := mload(add(vk_mptr, 0x140))
                let x_n_mptr := add(theta_mptr, 0x180)
                let mptr := x_n_mptr
                let num_instances := mload(add(vk_mptr,0x60))
                let mptr_end := add(mptr, mul(0x20, add(num_instances, {{ num_neg_lagranges }})))
                if iszero(num_instances) {
                    mptr_end := add(mptr_end, 0x20)
                }
                for
                    { let pow_of_omega := mload(add(vk_mptr, 0x180)) }
                    lt(mptr, mptr_end)
                    { mptr := add(mptr, 0x20) }
                {
                    mstore(mptr, addmod(x, sub(r, pow_of_omega), r))
                    pow_of_omega := mulmod(pow_of_omega, omega, r)
                }
                let x_n_minus_1 := addmod(x_n, sub(r, 1), r)
                mstore(mptr_end, x_n_minus_1)
                success := batch_invert(success, x_n_mptr, add(mptr_end, 0x20), r)

                mptr := x_n_mptr
                let l_i_common := mulmod(x_n_minus_1, mload(add(vk_mptr, 0x120)), r)
                for
                    { let pow_of_omega := mload(add(vk_mptr, 0x180)) }
                    lt(mptr, mptr_end)
                    { mptr := add(mptr, 0x20) }
                {
                    mstore(mptr, mulmod(l_i_common, mulmod(mload(mptr), pow_of_omega, r), r))
                    pow_of_omega := mulmod(pow_of_omega, omega, r)
                }

                let l_blind := mload(add(x_n_mptr, 0x20))
                let l_i_cptr := add(x_n_mptr, 0x40)
                for
                    { let l_i_cptr_end := add(x_n_mptr, {{ (num_neg_lagranges * 32)|hex() }}) }
                    lt(l_i_cptr, l_i_cptr_end)
                    { l_i_cptr := add(l_i_cptr, 0x20) }
                {
                    l_blind := addmod(l_blind, mload(l_i_cptr), r)
                }

                let instance_eval := 0
                for
                    {
                        let instance_cptr := mload(add(vk_mptr, 0xe0))
                        let instance_cptr_end := add(instance_cptr, mul(0x20, num_instances))
                    }
                    lt(instance_cptr, instance_cptr_end)
                    {
                        instance_cptr := add(instance_cptr, 0x20)
                        l_i_cptr := add(l_i_cptr, 0x20)
                    }
                {
                    instance_eval := addmod(instance_eval, mulmod(mload(l_i_cptr), calldataload(instance_cptr), r), r)
                }

                let x_n_minus_1_inv := mload(mptr_end)
                let l_last := mload(x_n_mptr)
                let l_0 := mload(add(x_n_mptr, {{ (num_neg_lagranges * 32)|hex() }}))

                mstore(x_n_mptr, x_n)
                mstore(add(theta_mptr, 0x1a0), x_n_minus_1_inv)
                mstore(add(theta_mptr, 0x1c0), l_last)
                mstore(add(theta_mptr, 0x1e0), l_blind)
                mstore(add(theta_mptr, 0x200), l_0)
                mstore(add(theta_mptr, 0x220), instance_eval)
            }

            // Compute quotient evavluation
            {
                let quotient_eval_numer
                let y := mload(add(theta_mptr, 0x60))

                {%- for code_block in quotient_eval_numer_computations %}
                {
                    {%- for line in code_block %}
                    {{ line }}
                    {%- endfor %}
                }
                {%- endfor %}

                pop(y)

                let quotient_eval := mulmod(quotient_eval_numer, mload(add(theta_mptr, 0x1a0)), r)
                mstore(add(theta_mptr, 0x240), quotient_eval)
            }

            // // Compute quotient evavluation
            // // TODO:
            // // [X] Gate computations
            // // [ ] Permutation computations
            // // [ ] Lookup computations
            // {
            //     let quotient_eval_numer
            //     let y := mload(add(theta_mptr, 0x60))
            //     let code_blocks_offset_ptr := add(vk_mptr,(add(vk_mptr, 0x380)))
            //     let code_blocks_lens_len := mload(code_blocks_offset_ptr) // Remember this length represented in bytes
            //     let code_blocks_len_offset := mload(add(code_blocks_lens_len, 0x20)) 
            //     let expressions_ptr := add(vk_mptr, EXPRESSIONS_OFFSET) // TODO fill in the correct offset
            //     let expression := 0x0 // Initialize this to 0. Will set it later in the loop
            //     let experssion_words_counter := 0
            //     let free_static_memory_ptr := 0x20 // Initialize at 0x20 b/c 0x00 to store vars that need to persist across certain code blocks
            //     let constants_ptr := add(vk_mptr, CONSTANTS_OFFSET) // TODO fill in the correct offset
            //     // Load in the total number of code blocks from the vk constants, right after the number challenges
            //     for { let code_block := 0 } lt(code_block, code_blocks_lens_len) { code_block := add(code_block, 0x20) } {
            //         // Shift the code_len by the free_static_memory_ptr
            //         let code_len := add(mload(add(code_blocks_len_offset, code_block)), free_static_memory_ptr)
            //         // loop through code len
            //         for { let i := free_static_memory_ptr } lt(i, code_len) { i := add(i, 0x20) } {
            //             /// @dev Note we can optimize the amount of space the expressions take up by packing 32/5 == 6 expressions into a single word
            //             expression := mload(add(expressions_ptr, experssion_words_counter))
            //             experssion_words_counter := add(experssion_words_counter, 0x20)
            //             // Load in the least significant byte located of the `expression` word to get the operation type
            //             let byte := and(expression, 0xFF)
                        
            //             // Determine which operation to peform and then store the result in the next available memory slot.

            //             // 0x00 => Advice/Fixed expression
            //             if (eq(byte, 0x00)) {
            //                 // Load the calldata ptr from the expression, which come from the 2nd and 3rd least significant bytes.
            //                 mstore(i,calldataload(and(shr(8, expressions), 0xFFFF)))
            //             } 
            //             // 0x01 => Negated expression
            //             else if (eq(byte, 0x01)) {
            //                 // Load the memory ptr from the expression, which come from the 2nd and 3rd least significant bytes
            //                 mstore(i,sub(r, mload(and(shr(8, expressions), 0xFFFF))))
            //             }
            //             // 0x02 => Sum expression
            //             else if (eq(byte, 0x02)) {
            //                 // Load the lhs operand memory ptr from the expression, which comes from the 2nd and 3rd least significant bytes
            //                 // Load the rhs operand memory ptr from the expression, which comes from the 4th and 5th least significant bytes
            //                 mstore(i,addmod(mload(and(shr(24, expressions), 0xFFFF)),mload(and(shr(8, expressions), 0xFFFF)),r))
            //             }
            //             // 0x03 => Product/scalar expression
            //             else if (eq(byte, 0x03)) {
            //                 // Load the lhs operand memory ptr from the expression, which comes from the 2nd and 3rd least significant bytes
            //                 // Load the rhs operand memory ptr from the expression, which comes from the 4th and 5th least significant bytes
            //                 mstore(i,mulmod(mload(and(shr(24, expressions), 0xFFFF)),mload(and(shr(8, expressions), 0xFFFF)),r))
            //             }
            //         }
            //         // at the end of each code block we update `quotient_eval_numer`
            //         if (eq(code_block, 0x00)) {
            //             // If this is the first code block, we set `quotient_eval_numer` to the last var in the code block
            //             quotient_eval_numer := mload(code_len)
            //         } else {
            //             // Otherwise we add the last var in the code block to `quotient_eval_numer` mod r
            //             quotient_eval_numer := addmod(quotient_eval_numer, mload(code_len), r)
            //         }
            //     }

            //     pop(y)

            //     let quotient_eval := mulmod(quotient_eval_numer, mload(add(theta_mptr, 0x1a0)), r)
            //     mstore(add(theta_mptr, 0x240), quotient_eval)
            //     // Check that the quotient evaluation is correct
            //     success := and(success, eq(quotient_eval, mload(add(theta_mptr, 0x240)))
            // }

            // Compute quotient commitment
            {
                mstore(0x00, calldataload(mload(add(vk_mptr, 0xa0))))
                mstore(0x20, calldataload(add(mload(add(vk_mptr, 0xa0)), 0x20)))
                let x_n := mload(add(theta_mptr, 0x180))
                for
                    {
                        let cptr := sub(mload(add(vk_mptr, 0xa0)), 0x40)
                        let cptr_end := sub(mload(add(vk_mptr, 0xc0)), 0x40)
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
                {%- for code_block in pcs_computations %}
                {
                    {%- for line in code_block %}
                    {{ line }}
                    {%- endfor %}
                }
                {%- endfor %}
            }

            // Random linear combine with accumulator
            if mload(add(vk_mptr, 0x01a0)) {
                mstore(0x00, mload(add(theta_mptr, 0x100)))
                mstore(0x20, mload(add(theta_mptr, 0x120)))
                mstore(0x40, mload(add(theta_mptr, 0x140)))
                mstore(0x60, mload(add(theta_mptr, 0x160)))
                mstore(0x80, mload(add(theta_mptr, 0x2c0)))
                mstore(0xa0, mload(add(theta_mptr, 0x2e0)))
                mstore(0xc0, mload(add(theta_mptr, 0x300)))
                mstore(0xe0, mload(add(theta_mptr, 0x320)))
                let challenge := mod(keccak256(0x00, 0x100), r)

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

            // // Perform pairing
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
