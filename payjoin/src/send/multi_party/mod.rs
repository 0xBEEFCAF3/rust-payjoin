use serde::{Deserialize, Serialize};

use super::{clear_unneeded_fields, v1, v2, BuildSenderError};

#[derive(Clone)]
pub struct SenderBuilder<'a> (v2::SenderBuilder<'a>);

impl<'a> SenderBuilder<'a> {
    /// Build a sender with optimistic merge enabled
    /// TODO(armins) this is pretty much skipping all the validating and checks
    pub fn build_with_optimistic_merge(self) -> Result<Sender, BuildSenderError> {
        let mut psbt = self.0.0.psbt.clone();
        clear_unneeded_fields(&mut psbt);
        let v2 = v2::SenderBuilder::new(psbt, self.0.0.uri).build_recommended(self.0.0.min_fee_rate)?;
        Ok(Sender { v2, opt_in_to_optimistic_merge: true })
    }
}

#[derive(Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Sender {
    v2: v2::Sender,
    opt_in_to_optimistic_merge: bool,
}

impl Sender {
    pub fn extract_v2(self, ohttp_relay: Url) -> Result<(Request, V2PostContext), CreateRequestError> {
        self.v2.extract_v2(ohttp_relay)
    }
}