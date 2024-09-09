// SPDX-License-Identifier: MIT

pragma solidity ^0.8.0;

contract Halo2VerifyingArtifact {
    constructor() {
        assembly {
            {%- for (name, chunk) in constants %}
            mstore({{ (32 * loop.index0)|hex_padded(4) }}, {{ chunk|hex_padded(64) }}) // {{ name }}
            {%- endfor %}
            {%- let offset_0 = constants.len() %}
            {%- for (x, y) in fixed_comms %}
            mstore({{ (32 * (offset_0 + 2 * loop.index0))|hex_padded(4) }}, {{ x|hex_padded(64) }}) // fixed_comms[{{ loop.index0 }}].x
            mstore({{ (32 * (offset_0 + 2 * loop.index0 + 1))|hex_padded(4) }}, {{ y|hex_padded(64) }}) // fixed_comms[{{ loop.index0 }}].y
            {%- endfor %}
            {%- let offset_1 = offset_0 + 2 * fixed_comms.len() %}
            {%- for (x, y) in permutation_comms %}
            mstore({{ (32 * (offset_1 + 2 * loop.index0))|hex_padded(4) }}, {{ x|hex_padded(64) }}) // permutation_comms[{{ loop.index0 }}].x
            mstore({{ (32 * (offset_1 + 2 * loop.index0 + 1))|hex_padded(4) }}, {{ y|hex_padded(64) }}) // permutation_comms[{{ loop.index0 }}].y
            {%- endfor %}
            {%- let offset_2 = offset_1 + 2 * permutation_comms.len() %}
            {%- for const in const_expressions %}
            mstore({{ (32 * (offset_2 + loop.index0))|hex_padded(4) }}, {{ const|hex_padded(64) }}) // const_expressions[{{ loop.index0 }}]
            {%- endfor %}
            {%- let offset_4 = offset_2 + const_expressions.len() %}
            mstore({{ (32 * offset_4)|hex_padded(4) }}, {{ (32 * gate_computations.length)|hex_padded(64) }}) // gate_computations length
            {%- let offset_5 = offset_4 + 1 %}
            {%- for packed_expression_word in gate_computations.packed_expression_words %}
            {%- let offset = offset_5 + loop.index0 %}
            mstore({{ (32 * offset)|hex_padded(4) }}, {{ packed_expression_word|hex_padded(64) }}) // packed_expression_word [{{ loop.index0 }}]
            {%- endfor %}
            {%- let offset_6 = offset_4 + gate_computations.len() %}
            mstore({{ (32 * offset_6)|hex_padded(4) }}, {{ permutation_computations.permutation_meta_data|hex_padded(64) }}) // permutation_meta_data
            {%- for word in permutation_computations.permutation_data %}
            {%- let offset = offset_6 + 1 + loop.index0 %}
            mstore({{ (32 * offset)|hex_padded(4) }}, {{ word|hex_padded(64) }}) // permutation_data [{{ loop.index0 }}]
            {%- endfor %}
            {%- let offset_7 = offset_6 + permutation_computations.len() %}
            mstore({{ (32 * offset_7)|hex_padded(4) }}, {{ lookup_computations.meta_data|hex_padded(64) }}) // meta_data of lookup_computations
            {%- let base_offset = offset_7 + 1 %}
            {%- for lookup in lookup_computations.lookups %}
            {%- let offset = base_offset + lookup.acc %}
            mstore({{ (32 * offset)|hex_padded(4) }}, {{ lookup.evals|hex_padded(64) }}) // lookup_evals[{{ loop.index0 }}]
            {%- for table_line in lookup.table_lines %}
            mstore({{ (32 * (offset + 1 + loop.index0))|hex_padded(4) }}, {{ table_line|hex_padded(64) }}) // lookup_table_line [{{ loop.index0 }}]
            {%- endfor %}
            {%- for input in lookup.inputs %}
            {%- let offset = offset + 1 + lookup.table_lines.len() + input.acc %}
            {%- for expression in input.expression %}
            mstore({{ (32 * (offset + loop.index0))|hex_padded(4) }}, {{ expression|hex_padded(64) }}) // input_expression [{{ loop.index0 }}]
            {%- endfor %}
            {%- endfor %}
            {%- endfor %}
            {%- let offset_8 = offset_7 + lookup_computations.len() %}
            {%- for point_word in pcs_computations.point_computations %}
            mstore({{ (32 * (offset_8 + loop.index0))|hex_padded(4) }}, {{ point_word|hex_padded(64) }}) // point_computations[{{ loop.index0 }}]
            {%- endfor %}
            {%- let offset_9 = offset_8 + pcs_computations.point_computations.len() %}
            {%- for vanishing_word in pcs_computations.vanishing_computations %}
            mstore({{ (32 * (offset_9 + loop.index0))|hex_padded(4) }}, {{ vanishing_word|hex_padded(64) }}) // vanishing_computations[{{ loop.index0 }}]
            {%- endfor %}
            {%- let offset_10 = offset_9 + pcs_computations.vanishing_computations.len() %}
            {%- for coeff_word in pcs_computations.coeff_computations %}
            mstore({{ (32 * (offset_10 + loop.index0))|hex_padded(4) }}, {{ coeff_word|hex_padded(64) }}) // coeff_computations[{{ loop.index0 }}]
            {%- endfor %}
            {%- let offset_11 = offset_10 + pcs_computations.coeff_computations.len() %}
            mstore({{ (32 * offset_11)|hex_padded(4) }}, {{ pcs_computations.normalized_coeff_computations|hex_padded(64) }}) // normalized_coeff_computations
            {%- let offset_12 = offset_11 + 1 %}
            {%- for r_eval_word in pcs_computations.r_evals_computations %}
            mstore({{ (32 * (offset_12 + loop.index0))|hex_padded(4) }}, {{ r_eval_word|hex_padded(64) }}) // r_evals_computations[{{ loop.index0 }}]
            {%- endfor %}
            {%- let offset_13 = offset_12 + pcs_computations.r_evals_computations.len() %}
            {%- for coeff_sum_word in pcs_computations.coeff_sums_computation %}
            mstore({{ (32 * (offset_13 + loop.index0))|hex_padded(4) }}, {{ coeff_sum_word|hex_padded(64) }}) // coeff_sums_computations[{{ loop.index0 }}]
            {%- endfor %}
            {%- let offset_14 = offset_13 + pcs_computations.coeff_sums_computation.len() %}
            mstore({{ (32 * offset_14)|hex_padded(4) }}, {{ pcs_computations.r_eval_computations|hex_padded(64) }}) // r_eval_computations
            {%- let offset_15 = offset_14 + 1 %}
            {%- for pairing_input_word in pcs_computations.pairing_input_computations %}
            mstore({{ (32 * (offset_15 + loop.index0))|hex_padded(4) }}, {{ pairing_input_word|hex_padded(64) }}) // pairing_input_computations[{{ loop.index0 }}]
            {%- endfor %}
            return(0, {{ (32 * (offset_8 + pcs_computations.len()))|hex() }})
        }
    }
}
