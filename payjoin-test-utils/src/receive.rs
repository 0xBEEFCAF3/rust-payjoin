use std::str::FromStr;

use bitcoin::{Address, Network};
use payjoin::receive::v1::{
    Headers, MaybeInputsOwned, MaybeInputsSeen, OutputsUnknown, PayjoinProposal,
    ProvisionalProposal, UncheckedProposal, WantsInputs, WantsOutputs,
};

use crate::{ORIGINAL_PSBT, PARSED_ORIGINAL_PSBT, PARSED_ORIGINAL_REQUEST, QUERY_PARAMS};

#[derive(Debug, Clone)]
pub struct MockHeaders {
    length: String,
}

impl MockHeaders {
    pub fn new(length: u64) -> MockHeaders { MockHeaders { length: length.to_string() } }
}

impl Headers for MockHeaders {
    fn get_header(&self, key: &str) -> Option<&str> {
        match key {
            "content-length" => Some(&self.length),
            "content-type" => Some("text/plain"),
            _ => None,
        }
    }
}

pub fn unchecked_proposal_from_test_vector() -> UncheckedProposal {
    let body = ORIGINAL_PSBT.as_bytes();
    let headers = MockHeaders::new(body.len() as u64);
    UncheckedProposal::from_request(PARSED_ORIGINAL_REQUEST.as_slice(), QUERY_PARAMS, headers)
        .expect("Test vector request should not fail")
}

pub fn maybe_inputs_owned_from_test_vector() -> MaybeInputsOwned {
    let proposal = unchecked_proposal_from_test_vector();
    proposal
        .check_broadcast_suitability(None, |_| Ok(true))
        .expect("Broadcast suitability check should not fail")
}

pub fn maybe_inputs_seen_from_test_vector() -> MaybeInputsSeen {
    let maybe_inputs_owned = maybe_inputs_owned_from_test_vector();
    maybe_inputs_owned.check_inputs_not_owned(|_| Ok(false)).expect("No inputs should be owned")
}

pub fn outputs_unknown_from_test_vector() -> OutputsUnknown {
    let maybe_inputs_seen = maybe_inputs_seen_from_test_vector();
    maybe_inputs_seen
        .check_no_inputs_seen_before(|_| Ok(false))
        .expect("No inputs should be seen before")
}

pub fn wants_outputs_from_test_vector(proposal: UncheckedProposal) -> WantsOutputs {
    proposal
        .assume_interactive_receiver()
        .check_inputs_not_owned(|_| Ok(false))
        .expect("No inputs should be owned")
        .check_no_inputs_seen_before(|_| Ok(false))
        .expect("No inputs should be seen before")
        .identify_receiver_outputs(|script| {
            let network = Network::Bitcoin;
            Ok(Address::from_script(script, network).unwrap()
                == Address::from_str("3CZZi7aWFugaCdUCS15dgrUUViupmB8bVM")
                    .unwrap()
                    .require_network(network)
                    .unwrap())
        })
        .expect("Receiver output should be identified")
}

pub fn wants_inputs_from_test_vector() -> WantsInputs {
    let proposal = unchecked_proposal_from_test_vector();
    wants_outputs_from_test_vector(proposal).commit_outputs()
}

pub fn provisional_proposal_from_test_vector(proposal: UncheckedProposal) -> ProvisionalProposal {
    wants_outputs_from_test_vector(proposal).commit_outputs().commit_inputs()
}

pub fn payjoin_proposal_from_test_vector(proposal: UncheckedProposal) -> PayjoinProposal {
    provisional_proposal_from_test_vector(proposal)
        .finalize_proposal(|_| Ok(PARSED_ORIGINAL_PSBT.clone()), None, None)
        .expect("finalize_proposal should not fail")
}
