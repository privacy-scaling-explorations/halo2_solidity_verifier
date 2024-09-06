use crate::codegen::{
    pcs::BatchOpenScheme::{self, Bdfg21, Gwc19},
    util::Ptr,
};
use askama::{Error, Template};
use ruint::aliases::U256;
use std::collections::HashMap;
use std::fmt;

use super::{
    evaluator::{GateDataEncoded, LookupsDataEncoded, PermutationDataEncoded},
    pcs::PcsDataEncoded,
};
#[derive(Template)]
#[template(path = "Halo2VerifyingKey.sol")]
pub(crate) struct Halo2VerifyingKey {
    pub(crate) constants: Vec<(&'static str, U256)>,
    pub(crate) fixed_comms: Vec<(U256, U256)>,
    pub(crate) permutation_comms: Vec<(U256, U256)>,
}

impl Halo2VerifyingKey {
    pub(crate) fn len(&self, scaled: bool) -> usize {
        let len =
            self.constants.len() + (self.fixed_comms.len() + self.permutation_comms.len()) * 2;
        if scaled {
            len * 0x20
        } else {
            len
        }
    }
}

#[derive(Template)]
#[template(path = "Halo2VerifyingArtifact.sol")]
pub(crate) struct Halo2VerifyingArtifact {
    pub(crate) constants: Vec<(&'static str, U256)>,
    pub(crate) fixed_comms: Vec<(U256, U256)>,
    pub(crate) permutation_comms: Vec<(U256, U256)>,
    pub(crate) const_expressions: Vec<U256>,
    pub(crate) gate_computations: GateDataEncoded,
    pub(crate) permutation_computations: PermutationDataEncoded,
    pub(crate) lookup_computations: LookupsDataEncoded,
    pub(crate) pcs_computations: PcsDataEncoded,
}

impl Halo2VerifyingArtifact {
    pub(crate) fn len(&self, scaled: bool) -> usize {
        let len = self.constants.len()
            + (self.fixed_comms.len() + self.permutation_comms.len()) * 2
            + self.const_expressions.len()
            + self.gate_computations.len()
            + self.permutation_computations.len()
            + self.lookup_computations.len()
            + self.pcs_computations.len();
        if scaled {
            len * 0x20
        } else {
            len
        }
    }
}

// Enum for handling both VerifyingKey and VerifyingArtifact
pub(crate) enum VerifyingCache<'a> {
    Key(&'a Halo2VerifyingKey),
    Artifact(&'a Halo2VerifyingArtifact),
}

impl VerifyingCache<'_> {
    pub(crate) fn len(&self, scaled: bool) -> usize {
        match self {
            VerifyingCache::Key(key) => key.len(scaled),
            VerifyingCache::Artifact(artifact) => artifact.len(scaled),
        }
    }

    pub(crate) fn constants(&self) -> &Vec<(&'static str, U256)> {
        match self {
            VerifyingCache::Key(key) => &key.constants,
            VerifyingCache::Artifact(artifact) => &artifact.constants,
        }
    }

    pub(crate) fn fixed_comms(&self) -> &Vec<(U256, U256)> {
        match self {
            VerifyingCache::Key(key) => &key.fixed_comms,
            VerifyingCache::Artifact(artifact) => &artifact.fixed_comms,
        }
    }
}

// Halo2Verifier struct and implementation
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
    pub(crate) vk_const_offsets: HashMap<&'static str, U256>,
}

impl Halo2VerifyingArtifact {
    pub(crate) fn render(&self, writer: &mut (impl fmt::Write + ?Sized)) -> Result<(), fmt::Error> {
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
