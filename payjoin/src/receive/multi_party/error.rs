use std::error;
use core::fmt;


use crate::{psbt, receive::RequestError};

#[derive(Debug)]
pub struct MultiPartyError(InternalMultiPartyError);

#[derive(Debug)]
pub(crate) enum InternalMultiPartyError {
    /// Failed to merge proposals
    FailedToMergeProposals(psbt::MergePsbtError),

    /// Bad Request
    BadRequest(RequestError),
}

impl From<InternalMultiPartyError> for MultiPartyError {
    fn from(e: InternalMultiPartyError) -> Self {
        MultiPartyError(e)
    }
}

impl fmt::Display for MultiPartyError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match &self.0 {
            InternalMultiPartyError::FailedToMergeProposals(e) => write!(f, "Failed to merge proposals: {}", e),
            InternalMultiPartyError::BadRequest(e) => write!(f, "Bad Request: {}", e),
        }
    }
}

impl error::Error for MultiPartyError {
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        match &self.0 {
            InternalMultiPartyError::FailedToMergeProposals(e) => Some(e),
            InternalMultiPartyError::BadRequest(e) => Some(e),
        }
    }
}
