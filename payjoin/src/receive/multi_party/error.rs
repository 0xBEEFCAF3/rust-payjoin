use core::fmt;
use std::error;

use crate::psbt;
#[derive(Debug)]
pub struct MultiPartyError(InternalMultiPartyError);

#[derive(Debug)]
pub(crate) enum InternalMultiPartyError {
    /// Failed to merge proposals
    FailedToMergeProposals(Vec<psbt::merge::MergePsbtError>),
    /// Not enough proposals
    NotEnoughProposals,
    /// Proposal version not supported
    ProposalVersionNotSupported(usize),
    /// Optimistic merge not supported
    OptimisticMergeNotSupported,
    /// Bitcoin Internal Error
    BitcoinExtractTxError(bitcoin::psbt::ExtractTxError),
    /// Input in Finalized Proposal is missing witness or script_sig
    InputMissingWitnessOrScriptSig,
    /// Failed to combine psbts
    FailedToCombinePsbts(bitcoin::psbt::Error),
}

impl From<InternalMultiPartyError> for MultiPartyError {
    fn from(e: InternalMultiPartyError) -> Self { MultiPartyError(e) }
}

impl fmt::Display for MultiPartyError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match &self.0 {
            InternalMultiPartyError::FailedToMergeProposals(e) =>
                write!(f, "Failed to merge proposals: {:?}", e),
            InternalMultiPartyError::NotEnoughProposals => write!(f, "Not enough proposals"),
            InternalMultiPartyError::ProposalVersionNotSupported(v) =>
                write!(f, "Proposal version not supported: {}", v),
            InternalMultiPartyError::OptimisticMergeNotSupported =>
                write!(f, "Optimistic merge not supported"),
            InternalMultiPartyError::BitcoinExtractTxError(e) =>
                write!(f, "Bitcoin extract tx error: {:?}", e),
            InternalMultiPartyError::InputMissingWitnessOrScriptSig =>
                write!(f, "Input in Finalized Proposal is missing witness or script_sig"),
            InternalMultiPartyError::FailedToCombinePsbts(e) =>
                write!(f, "Failed to combine psbts: {:?}", e),
        }
    }
}

impl error::Error for MultiPartyError {
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        match &self.0 {
            InternalMultiPartyError::FailedToMergeProposals(_) => None, // Vec<MergePsbtError> doesn't implement Error
            InternalMultiPartyError::NotEnoughProposals => None,
            InternalMultiPartyError::ProposalVersionNotSupported(_) => None,
            InternalMultiPartyError::OptimisticMergeNotSupported => None,
            InternalMultiPartyError::BitcoinExtractTxError(e) => Some(e),
            InternalMultiPartyError::InputMissingWitnessOrScriptSig => None,
            InternalMultiPartyError::FailedToCombinePsbts(e) => Some(e),
        }
    }
}
