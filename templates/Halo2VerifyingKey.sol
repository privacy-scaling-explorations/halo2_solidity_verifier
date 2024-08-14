// SPDX-License-Identifier: MIT

pragma solidity ^0.8.0;

contract Halo2VerifyingKey {
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
            return(0, {{ (32 * (offset_1 + 2 * permutation_comms.len()))|hex() }})
        }
    }
}
