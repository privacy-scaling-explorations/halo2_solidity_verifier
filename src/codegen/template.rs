use crate::codegen::{
    pcs::BatchOpenScheme::{self, Bdfg21, Gwc19},
    util::Ptr,
};
use askama::{Error, Template};
use ruint::aliases::U256;
use std::fmt;

#[derive(Template)]
#[template(path = "Halo2VerifyingKey.sol")]
pub(crate) struct Halo2VerifyingKey {
    pub(crate) constants: Vec<(&'static str, U256)>,
    pub(crate) num_advices_user_challenges: Vec<(U256, U256)>,
    pub(crate) fixed_comms: Vec<(U256, U256)>,
    pub(crate) permutation_comms: Vec<(U256, U256)>,
    pub(crate) const_expressions: Vec<U256>,
    pub(crate) gate_computations: Vec<(Vec<U256>,usize)>,
    pub(crate) gate_computations_total_length: usize
}

impl Halo2VerifyingKey {
    pub(crate) fn len(&self) -> usize {
        (self.constants.len() * 0x20)
            + (self.fixed_comms.len() + self.permutation_comms.len()) * 0x40
            + (self.const_expressions.len() * 0x20)
            + ((self.num_advices_user_challenges.len() * 0x40) + 0x20)
            // The length words of the inner vector + length word of the outer vector
            + (self.gate_computations.len() * 0x20 + 0x20) 
            // Sum up the lengths of al the nested vectors
            + (self.gate_computations_total_length * 0x20)
    }
}

#[derive(Template)]
#[template(path = "Halo2Verifier.sol")]
pub(crate) struct Halo2Verifier {
    pub(crate) scheme: BatchOpenScheme,
    pub(crate) embedded_vk: Halo2VerifyingKey,
    pub(crate) proof_len: usize,
    pub(crate) vk_mptr: Ptr,
    pub(crate) challenge_mptr: Ptr,
    pub(crate) theta_mptr: Ptr,
    pub(crate) proof_cptr: Ptr,
    pub(crate) proof_len_cptr: Ptr,
    pub(crate) quotient_comm_cptr: Ptr,
    pub(crate) num_neg_lagranges: usize,
    pub(crate) num_advices: Vec<usize>,
    pub(crate) num_challenges: Vec<usize>,
    pub(crate) num_evals: usize,
    pub(crate) num_quotients: usize,
    pub(crate) quotient_eval_numer_computations: Vec<Vec<String>>,
    pub(crate) pcs_computations: Vec<Vec<String>>,
}

#[derive(Template)]
#[template(path = "Halo2VerifierReusable.sol")]
pub(crate) struct Halo2VerifierReusable {
    pub(crate) scheme: BatchOpenScheme,
    pub(crate) num_neg_lagranges: usize,
    pub(crate) num_evals: usize,
    pub(crate) quotient_eval_numer_computations: Vec<Vec<String>>,
    pub(crate) pcs_computations: Vec<Vec<String>>,
}

impl Halo2VerifyingKey {
    pub(crate) fn render(&self, writer: &mut impl fmt::Write) -> Result<(), fmt::Error> {
        self.render_into(writer).map_err(|err| match err {
            Error::Fmt(err) => err,
            _ => unreachable!(),
        })
    }
}

impl Halo2Verifier {
    pub(crate) fn render(&self, writer: &mut impl fmt::Write) -> Result<(), fmt::Error> {
        self.render_into(writer).map_err(|err| match err {
            Error::Fmt(err) => err,
            _ => unreachable!(),
        })
    }
}

impl Halo2VerifierReusable {
    pub(crate) fn render(&self, writer: &mut impl fmt::Write) -> Result<(), fmt::Error> {
        self.render_into(writer).map_err(|err| match err {
            Error::Fmt(err) => err,
            _ => unreachable!(),
        })
    }
}

mod filters {
    use std::fmt::LowerHex;

    pub fn hex(value: impl LowerHex) -> ::askama::Result<String> {
        let value = format!("{value:x}");
        Ok(if value.len() % 2 == 1 {
            format!("0x0{value}")
        } else {
            format!("0x{value}")
        })
    }

    pub fn hex_padded(value: impl LowerHex, pad: usize) -> ::askama::Result<String> {
        let string = format!("0x{value:0pad$x}");
        if string == "0x0" {
            Ok(format!("0x{}", "0".repeat(pad)))
        } else {
            Ok(string)
        }
    }
}
