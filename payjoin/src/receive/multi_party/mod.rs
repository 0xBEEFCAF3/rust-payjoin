use bitcoin::{FeeRate, Psbt};
use error::{InternalMultiPartyError, MultiPartyError};

use super::error::InputContributionError;
use super::{v1, v2, Error, InputPair};
use crate::psbt::merge::MergePsbtExt;
use crate::receive::v2::SessionContext;

pub(crate) mod error;

const SUPPORTED_VERSIONS: &[usize] = &[2];

pub struct UncheckedProposalBuilder {
    proposals: Vec<v2::UncheckedProposal>,
}

impl Default for UncheckedProposalBuilder {
    fn default() -> Self { Self::new() }
}

impl UncheckedProposalBuilder {
    pub fn new() -> Self { Self { proposals: vec![] } }

    pub fn try_add(
        &mut self,
        proposal: v2::UncheckedProposal,
    ) -> Result<&mut Self, MultiPartyError> {
        self.check_proposal_suitability(&proposal)?;
        self.proposals.push(proposal);
        Ok(self)
    }

    fn check_proposal_suitability(
        &self,
        proposal: &v2::UncheckedProposal,
    ) -> Result<(), MultiPartyError> {
        let params = proposal.v1.params.clone();
        if !SUPPORTED_VERSIONS.contains(&params.v) {
            return Err(InternalMultiPartyError::ProposalVersionNotSupported(params.v).into());
        }

        if !params.optimistic_merge {
            return Err(InternalMultiPartyError::OptimisticMergeNotSupported.into());
        }
        Ok(())
    }

    pub fn try_build(&self) -> Result<UncheckedProposal, MultiPartyError> {
        if self.proposals.len() < 2 {
            return Err(InternalMultiPartyError::NotEnoughProposals.into());
        }

        let mut agg_psbt = self.proposals.first().expect("checked above").v1.psbt.clone();
        agg_psbt.dangerous_clear_signatures();
        let agg_psbt = self
            .proposals
            .iter()
            .skip(1) // Skip first since we already have it as agg_psbt
            .map(|p| p.v1.psbt.clone())
            .try_fold(agg_psbt, |mut acc, other| {
                let mut other = other.clone();
                other.dangerous_clear_signatures();
                acc.merge_unsigned_tx(other)
                    .map_err(InternalMultiPartyError::FailedToMergeProposals)?;
                Ok::<_, InternalMultiPartyError>(acc)
            })?;

        let unchecked_proposal = v1::UncheckedProposal {
            psbt: agg_psbt,
            params: self.proposals.first().expect("checked above").v1.params.clone(),
        };
        let sender_contexts = self.proposals.iter().map(|p| p.context.clone()).collect();
        Ok(UncheckedProposal { v1: unchecked_proposal, sender_contexts })
    }
}

/// A multi-party proposal that has been merged by the receiver
pub struct UncheckedProposal {
    v1: v1::UncheckedProposal,
    sender_contexts: Vec<SessionContext>,
}

impl UncheckedProposal {
    pub fn check_broadcast_suitability(
        self,
        min_fee_rate: Option<FeeRate>,
        can_broadcast: impl Fn(&bitcoin::Transaction) -> Result<bool, Error>,
    ) -> Result<MaybeInputsOwned, Error> {
        let inner = self.v1.check_broadcast_suitability(min_fee_rate, can_broadcast)?;
        Ok(MaybeInputsOwned { v1: inner, sender_contexts: self.sender_contexts })
    }
}

pub struct MaybeInputsOwned {
    v1: v1::MaybeInputsOwned,
    sender_contexts: Vec<SessionContext>,
}

impl MaybeInputsOwned {
    pub fn check_inputs_not_owned(
        self,
        is_owned: impl Fn(&bitcoin::Script) -> Result<bool, Error>,
    ) -> Result<MaybeInputsSeen, Error> {
        let inner = self.v1.check_inputs_not_owned(is_owned)?;
        Ok(MaybeInputsSeen { v1: inner, sender_contexts: self.sender_contexts })
    }
}

pub struct MaybeInputsSeen {
    v1: v1::MaybeInputsSeen,
    sender_contexts: Vec<SessionContext>,
}

impl MaybeInputsSeen {
    pub fn check_no_inputs_seen_before(
        self,
        is_seen: impl Fn(&bitcoin::OutPoint) -> Result<bool, Error>,
    ) -> Result<OutputsUnknown, Error> {
        let inner = self.v1.check_no_inputs_seen_before(is_seen)?;
        Ok(OutputsUnknown { v1: inner, sender_contexts: self.sender_contexts })
    }
}

pub struct OutputsUnknown {
    v1: v1::OutputsUnknown,
    sender_contexts: Vec<SessionContext>,
}

impl OutputsUnknown {
    pub fn identify_receiver_outputs(
        self,
        is_receiver_output: impl Fn(&bitcoin::Script) -> Result<bool, Error>,
    ) -> Result<WantsOutputs, Error> {
        let inner = self.v1.identify_receiver_outputs(is_receiver_output)?;
        Ok(WantsOutputs { v1: inner, sender_contexts: self.sender_contexts })
    }
}

pub struct WantsOutputs {
    v1: v1::WantsOutputs,
    sender_contexts: Vec<SessionContext>,
}

impl WantsOutputs {
    pub fn commit_outputs(self) -> WantsInputs {
        let inner = self.v1.commit_outputs();
        WantsInputs { v1: inner, sender_contexts: self.sender_contexts }
    }
}

pub struct WantsInputs {
    v1: v1::WantsInputs,
    sender_contexts: Vec<SessionContext>,
}

impl WantsInputs {
    /// Add the provided list of inputs to the transaction.
    /// Any excess input amount is added to the change_vout output indicated previously.
    pub fn contribute_inputs(
        self,
        inputs: impl IntoIterator<Item = InputPair>,
    ) -> Result<WantsInputs, InputContributionError> {
        let inner = self.v1.contribute_inputs(inputs)?;
        Ok(WantsInputs { v1: inner, sender_contexts: self.sender_contexts })
    }

    /// Proceed to the proposal finalization step.
    /// Inputs cannot be modified after this function is called.
    pub fn commit_inputs(self) -> ProvisionalProposal {
        let inner = self.v1.commit_inputs();
        ProvisionalProposal { v1: inner, sender_contexts: self.sender_contexts }
    }
}

pub struct ProvisionalProposal {
    v1: v1::ProvisionalProposal,
    sender_contexts: Vec<SessionContext>,
}

impl ProvisionalProposal {
    pub fn finalize_proposal(
        self,
        wallet_process_psbt: impl Fn(&Psbt) -> Result<Psbt, Error>,
        min_feerate_sat_per_vb: Option<FeeRate>,
        max_feerate_sat_per_vb: FeeRate,
    ) -> Result<PayjoinProposal, Error> {
        let inner = self.v1.finalize_proposal(
            wallet_process_psbt,
            min_feerate_sat_per_vb,
            Some(max_feerate_sat_per_vb),
        )?;
        Ok(PayjoinProposal { v1: inner, sender_contexts: self.sender_contexts })
    }
}

pub struct PayjoinProposal {
    v1: v1::PayjoinProposal,
    sender_contexts: Vec<SessionContext>,
}

impl PayjoinProposal {
    pub fn sender_iter(&self) -> impl Iterator<Item = v2::PayjoinProposal> {
        self.sender_contexts
            .iter()
            .map(|ctx| v2::PayjoinProposal::new(self.v1.clone(), ctx.clone()))
            .collect::<Vec<_>>()
            .into_iter()
    }

    pub fn proposal(&self) -> &v1::PayjoinProposal { &self.v1 }
}

pub struct FinalizedProposal {
    v2_proposals: Vec<v2::UncheckedProposal>,
}

impl Default for FinalizedProposal {
    fn default() -> Self { Self::new() }
}

impl FinalizedProposal {
    pub fn new() -> Self { Self { v2_proposals: vec![] } }

    pub fn add(&mut self, proposal: v2::UncheckedProposal) -> Result<(), MultiPartyError> {
        self.check_proposal_suitability(&proposal)?;
        self.v2_proposals.push(proposal);
        Ok(())
    }

    fn check_proposal_suitability(
        &self,
        proposal: &v2::UncheckedProposal,
    ) -> Result<(), MultiPartyError> {
        if !SUPPORTED_VERSIONS.contains(&proposal.v1.params.v) {
            return Err(
                InternalMultiPartyError::ProposalVersionNotSupported(proposal.v1.params.v).into()
            );
        }
        Ok(())
    }

    pub fn combine(self) -> Result<Psbt, MultiPartyError> {
        if self.v2_proposals.len() < 2 {
            return Err(InternalMultiPartyError::NotEnoughProposals.into());
        }

        let mut agg_psbt = self.v2_proposals.first().expect("checked above").v1.psbt.clone();
        for proposal in self.v2_proposals.iter().skip(1) {
            agg_psbt
                .combine(proposal.v1.psbt.clone())
                .map_err(InternalMultiPartyError::FailedToCombinePsbts)?;
        }

        // We explicitly call extract_tx to do some fee sanity checks
        // Otherwise you can just read the inputs from the unsigned_tx of the psbt
        let tx = agg_psbt
            .clone()
            .extract_tx()
            .map_err(InternalMultiPartyError::BitcoinExtractTxError)?;
        if tx.input.iter().any(|input| input.witness.is_empty() && input.script_sig.is_empty()) {
            return Err(InternalMultiPartyError::InputMissingWitnessOrScriptSig.into());
        }

        Ok(agg_psbt)
    }

    pub fn v2(&self) -> &[v2::UncheckedProposal] { &self.v2_proposals }
}