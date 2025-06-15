use std::sync::{Arc, Mutex};

use anyhow::{anyhow, Context, Result};
use payjoin::bitcoin::consensus::encode::serialize_hex;
use payjoin::bitcoin::psbt::Psbt;
use payjoin::bitcoin::{Amount, FeeRate};
use payjoin::persist::OptionalTransitionOutcome;
use payjoin::receive::v2::{
    process_err_res, replay_receiver_event_log, MaybeInputsOwned, MaybeInputsSeen, OutputsUnknown,
    PayjoinProposal, ProvisionalProposal, Receiver, ReceiverTypeState, SessionHistory,
    UncheckedProposal, WantsInputs, WantsOutputs, WithContext,
};
use payjoin::send::v2::{Sender, SenderBuilder, WithReplyKey};
use payjoin::Uri;
use tokio::sync::watch;

use super::config::Config;
use super::wallet::BitcoindWallet;
use super::App as AppTrait;
use crate::app::v2::ohttp::{unwrap_ohttp_keys_or_else_fetch, RelayManager};
use crate::app::{handle_interrupt, http_agent};
use crate::db::v2::{ReceiverPersister, SenderPersister};
use crate::db::Database;

mod ohttp;

#[derive(Clone)]
pub(crate) struct App {
    config: Config,
    db: Arc<Database>,
    wallet: BitcoindWallet,
    interrupt: watch::Receiver<()>,
    relay_manager: Arc<Mutex<RelayManager>>,
}

#[async_trait::async_trait]
impl AppTrait for App {
    fn new(config: Config) -> Result<Self> {
        let db = Arc::new(Database::create(&config.db_path)?);
        let relay_manager = Arc::new(Mutex::new(RelayManager::new()));
        let (interrupt_tx, interrupt_rx) = watch::channel(());
        tokio::spawn(handle_interrupt(interrupt_tx));
        let wallet = BitcoindWallet::new(&config.bitcoind)?;
        let app = Self { config, db, wallet, interrupt: interrupt_rx, relay_manager };
        app.wallet()
            .network()
            .context("Failed to connect to bitcoind. Check config RPC connection.")?;
        Ok(app)
    }

    fn wallet(&self) -> BitcoindWallet { self.wallet.clone() }

    async fn send_payjoin(&self, bip21: &str, fee_rate: FeeRate) -> Result<()> {
        use payjoin::UriExt;
        let uri =
            Uri::try_from(bip21).map_err(|e| anyhow!("Failed to create URI from BIP21: {}", e))?;
        let uri = uri.assume_checked();
        let uri = uri.check_pj_supported().map_err(|_| anyhow!("URI does not support Payjoin"))?;
        let url = uri.extras.endpoint();
        // match bip21 to send_session public_key
        let req_ctx = match self.db.get_send_session(url)? {
            Some(send_session) => send_session,
            None => {
                let psbt = self.create_original_psbt(&uri, fee_rate)?;
                let mut persister = SenderPersister::new(self.db.clone());
                let new_sender = SenderBuilder::new(psbt, uri.clone())
                    .build_recommended(fee_rate)
                    .with_context(|| "Failed to build payjoin request")?;
                let storage_token = new_sender
                    .persist(&mut persister)
                    .map_err(|e| anyhow!("Failed to persist sender: {}", e))?;
                Sender::load(storage_token, &persister)
                    .map_err(|e| anyhow!("Failed to load sender: {}", e))?
            }
        };
        self.spawn_payjoin_sender(req_ctx).await
    }

    async fn receive_payjoin(&self, amount: Amount) -> Result<()> {
        let address = self.wallet().get_new_address()?;
        let ohttp_keys =
            unwrap_ohttp_keys_or_else_fetch(&self.config, None, self.relay_manager.clone())
                .await?
                .ohttp_keys;
        let persister = ReceiverPersister::new(self.db.clone())?;
        let session = Receiver::create_session(
            address,
            self.config.v2()?.pj_directory.clone(),
            ohttp_keys,
            None,
            persister.clone(),
        )?;
        println!("Receive session established");
        let mut pj_uri = session.pj_uri();
        pj_uri.amount = Some(amount);
        println!("Request Payjoin by sharing this Payjoin Uri:");
        println!("{}", pj_uri);

        self.process_receiver_session(ReceiverTypeState::WithContext(session.clone()), &persister)
            .await?;
        Ok(())
    }

    #[allow(clippy::incompatible_msrv)]
    async fn resume_payjoins(&self) -> Result<()> {
        let recv_session_ids = self.db.get_recv_session_ids()?;
        let send_sessions = self.db.get_send_sessions()?;

        if recv_session_ids.is_empty() && send_sessions.is_empty() {
            println!("No sessions to resume.");
            return Ok(());
        }

        let mut tasks = Vec::new();

        for session_id in recv_session_ids {
            let self_clone = self.clone();
            let recv_persister = ReceiverPersister::from_id(self.db.clone(), session_id)?;
            let receiver_state = replay_receiver_event_log(&recv_persister)
                .map_err(|e| anyhow!("Failed to replay receiver event log: {:?}", e))?
                .0;
            tasks.push(tokio::spawn(async move {
                self_clone.process_receiver_session(receiver_state, &recv_persister).await
            }));
        }

        for session in send_sessions {
            let self_clone = self.clone();
            tasks.push(tokio::spawn(async move { self_clone.spawn_payjoin_sender(session).await }));
        }

        let mut interrupt = self.interrupt.clone();
        tokio::select! {
            _ = async {
                for task in tasks {
                    let _ = task.await;
                }
            } => {
                println!("All resumed sessions completed.");
            }
            _ = interrupt.changed() => {
                println!("Resumed sessions were interrupted.");
            }
        }
        Ok(())
    }
}

impl App {
    #[allow(clippy::incompatible_msrv)]
    async fn spawn_payjoin_sender(&self, mut req_ctx: Sender<WithReplyKey>) -> Result<()> {
        let mut interrupt = self.interrupt.clone();
        tokio::select! {
            res = self.long_poll_post(&mut req_ctx) => {
                self.process_pj_response(res?)?;
                self.db.clear_send_session(req_ctx.endpoint())?;
            }
            _ = interrupt.changed() => {
                println!("Interrupted. Call `send` with the same arguments to resume this session or `resume` to resume all sessions.");
            }
        }
        Ok(())
    }

    async fn long_poll_post(&self, req_ctx: &mut Sender<WithReplyKey>) -> Result<Psbt> {
        let ohttp_relay = self.unwrap_relay_or_else_fetch(Some(req_ctx.endpoint().clone())).await?;

        match req_ctx.extract_v2(ohttp_relay.clone()) {
            Ok((req, ctx)) => {
                println!("Posting Original PSBT Payload request...");
                let response = post_request(req).await?;
                println!("Sent fallback transaction");
                let v2_ctx = Arc::new(ctx.process_response(&response.bytes().await?)?);
                loop {
                    let (req, ohttp_ctx) = v2_ctx.extract_req(&ohttp_relay)?;
                    let response = post_request(req).await?;
                    match v2_ctx.process_response(&response.bytes().await?, ohttp_ctx) {
                        Ok(Some(psbt)) => return Ok(psbt),
                        Ok(None) => {
                            println!("No response yet.");
                        }
                        Err(re) => {
                            println!("{re}");
                            log::debug!("{re:?}");
                            return Err(anyhow!("Response error").context(re));
                        }
                    }
                }
            }
            Err(_) => {
                let (req, v1_ctx) = req_ctx.extract_v1();
                println!("Posting Original PSBT Payload request...");
                let response = post_request(req).await?;
                println!("Sent fallback transaction");
                match v1_ctx.process_response(&response.bytes().await?) {
                    Ok(psbt) => Ok(psbt),
                    Err(re) => {
                        println!("{re}");
                        log::debug!("{re:?}");
                        Err(anyhow!("Response error").context(re))
                    }
                }
            }
        }
    }

    async fn long_poll_fallback(
        &self,
        session: Receiver<WithContext, ReceiverPersister>,
    ) -> Result<Receiver<UncheckedProposal, ReceiverPersister>> {
        let ohttp_relay = self
            .unwrap_relay_or_else_fetch(Some(session.pj_uri().extras.endpoint().clone()))
            .await?;

        let mut session = session;
        loop {
            let (req, context) = session.extract_req(&ohttp_relay)?;
            println!("Polling receive request...");
            let ohttp_response = post_request(req).await?;
            let state_transition =
                session.process_res(ohttp_response.bytes().await?.to_vec().as_slice(), context);
            match state_transition {
                Ok(OptionalTransitionOutcome::Progress(next_state)) => {
                    println!("Got a request from the sender. Responding with a Payjoin proposal.");
                    return Ok(next_state);
                }
                Ok(OptionalTransitionOutcome::Stasis(current_state)) => {
                    session = current_state;
                    continue;
                }
                Err(e) => return Err(e.into()),
            }
        }
    }

    async fn process_receiver_session(
        &self,
        session: ReceiverTypeState<ReceiverPersister>,
        persister: &ReceiverPersister,
    ) -> Result<()> {
        let res = {
            match session {
                ReceiverTypeState::WithContext(proposal) =>
                    self.read_from_directory(proposal).await,
                ReceiverTypeState::UncheckedProposal(proposal) =>
                    self.check_proposal(proposal).await,
                ReceiverTypeState::MaybeInputsOwned(proposal) =>
                    self.check_inputs_not_owned(proposal).await,
                ReceiverTypeState::MaybeInputsSeen(proposal) =>
                    self.check_no_inputs_seen_before(proposal).await,
                ReceiverTypeState::OutputsUnknown(proposal) =>
                    self.identify_receiver_outputs(proposal).await,
                ReceiverTypeState::WantsOutputs(proposal) => self.commit_outputs(proposal).await,
                ReceiverTypeState::WantsInputs(proposal) => self.contribute_inputs(proposal).await,
                ReceiverTypeState::ProvisionalProposal(proposal) =>
                    self.finalize_proposal(proposal).await,
                ReceiverTypeState::PayjoinProposal(proposal) =>
                    self.send_payjoin_proposal(proposal).await,
                ReceiverTypeState::Uninitialized(_) =>
                    return Err(anyhow!("Uninitialized receiver session")),
                ReceiverTypeState::TerminalState =>
                    return Err(anyhow!("Terminal receiver session")),
            }
        };

        match res {
            Ok(_) => Ok(()),
            Err(e) => {
                let (_, session_history) = replay_receiver_event_log(persister)?;
                let pj_uri = match session_history.pj_uri() {
                    Some(uri) => Some(uri.extras.endpoint().clone()),
                    None => None,
                };
                let ohttp_relay = self.unwrap_relay_or_else_fetch(pj_uri).await?;
                handle_recoverable_error(&ohttp_relay, &session_history).await?;

                Err(e)
            }
        }
    }

    #[allow(clippy::incompatible_msrv)]
    async fn read_from_directory(
        &self,
        session: Receiver<WithContext, ReceiverPersister>,
    ) -> Result<()> {
        let mut interrupt = self.interrupt.clone();
        let receiver = tokio::select! {
            res = self.long_poll_fallback(session) => res,
            _ = interrupt.changed() => {
                println!("Interrupted. Call the `resume` command to resume all sessions.");
                return Err(anyhow!("Interrupted"));
            }
        }?;
        println!("Fallback transaction received. Consider broadcasting this to get paid if the Payjoin fails:");
        println!("{}", serialize_hex(&receiver.extract_tx_to_schedule_broadcast()));
        self.check_proposal(receiver).await
    }

    async fn check_proposal(
        &self,
        proposal: Receiver<UncheckedProposal, ReceiverPersister>,
    ) -> Result<()> {
        let wallet = self.wallet();
        let proposal =
            proposal.check_broadcast_suitability(None, |tx| Ok(wallet.can_broadcast(tx)?))?;

        self.check_inputs_not_owned(proposal).await
    }

    async fn check_inputs_not_owned(
        &self,
        proposal: Receiver<MaybeInputsOwned, ReceiverPersister>,
    ) -> Result<()> {
        let wallet = self.wallet();
        let proposal = proposal.check_inputs_not_owned(|input| Ok(wallet.is_mine(input)?))?;
        self.check_no_inputs_seen_before(proposal).await
    }

    async fn check_no_inputs_seen_before(
        &self,
        proposal: Receiver<MaybeInputsSeen, ReceiverPersister>,
    ) -> Result<()> {
        let proposal = proposal
            .check_no_inputs_seen_before(|input| Ok(self.db.insert_input_seen_before(*input)?))?;
        self.identify_receiver_outputs(proposal).await
    }

    async fn identify_receiver_outputs(
        &self,
        proposal: Receiver<OutputsUnknown, ReceiverPersister>,
    ) -> Result<()> {
        let wallet = self.wallet();
        let proposal = proposal
            .identify_receiver_outputs(|output_script| Ok(wallet.is_mine(output_script)?))?;
        self.commit_outputs(proposal).await
    }

    async fn commit_outputs(
        &self,
        proposal: Receiver<WantsOutputs, ReceiverPersister>,
    ) -> Result<()> {
        let proposal = proposal.commit_outputs()?;
        self.contribute_inputs(proposal).await
    }

    async fn contribute_inputs(
        &self,
        proposal: Receiver<WantsInputs, ReceiverPersister>,
    ) -> Result<()> {
        let wallet = self.wallet();
        let candidate_inputs = wallet.list_unspent()?;

        let selected_input = proposal.try_preserving_privacy(candidate_inputs)?;
        let proposal = proposal.contribute_inputs(vec![selected_input])?.commit_inputs()?;
        self.finalize_proposal(proposal).await
    }

    async fn finalize_proposal(
        &self,
        proposal: Receiver<ProvisionalProposal, ReceiverPersister>,
    ) -> Result<()> {
        let wallet = self.wallet();
        let proposal = proposal.finalize_proposal(
            |psbt| Ok(wallet.process_psbt(psbt)?),
            None,
            self.config.max_fee_rate,
        )?;
        self.send_payjoin_proposal(proposal).await
    }

    async fn send_payjoin_proposal(
        &self,
        mut proposal: Receiver<PayjoinProposal, ReceiverPersister>,
    ) -> Result<()> {
        let (req, ohttp_ctx) = proposal
            .extract_req(&self.unwrap_relay_or_else_fetch(None).await?)
            .map_err(|e| anyhow!("v2 req extraction failed {}", e))?;
        let res = post_request(req).await?;
        let payjoin_psbt = proposal.psbt().clone();
        proposal.process_res(&res.bytes().await?, ohttp_ctx)?;
        println!(
            "Response successful. Watch mempool for successful Payjoin. TXID: {}",
            payjoin_psbt.extract_tx_unchecked_fee_rate().clone().compute_txid()
        );
        Ok(())
    }

    async fn unwrap_relay_or_else_fetch(
        &self,
        directory: Option<payjoin::Url>,
    ) -> Result<payjoin::Url> {
        let selected_relay =
            self.relay_manager.lock().expect("Lock should not be poisoned").get_selected_relay();
        let ohttp_relay = match selected_relay {
            Some(relay) => relay,
            None =>
                unwrap_ohttp_keys_or_else_fetch(&self.config, directory, self.relay_manager.clone())
                    .await?
                    .relay_url,
        };
        Ok(ohttp_relay)
    }
}

/// Handle request error by sending an error response over the directory
async fn handle_recoverable_error(
    ohttp_relay: &payjoin::Url,
    session_history: &SessionHistory,
) -> Result<()> {
    let e = match session_history.terminal_error() {
        Some((_, Some(e))) => e,
        _ => return Ok(()),
    };
    let (err_req, err_ctx) = session_history
        .extract_err_req(ohttp_relay)?
        .expect("If JsonReply is Some, then err_req and err_ctx should be Some");
    let to_return = anyhow!("Replied with error: {}", e.to_json().to_string());

    let err_response = match post_request(err_req).await {
        Ok(response) => response,
        Err(e) => return Err(anyhow!("Failed to post error request: {}", e)),
    };

    let err_bytes = match err_response.bytes().await {
        Ok(bytes) => bytes,
        Err(e) => return Err(anyhow!("Failed to get error response bytes: {}", e)),
    };

    if let Err(e) = process_err_res(&err_bytes, err_ctx) {
        return Err(anyhow!("Failed to process error response: {}", e));
    }

    Err(to_return)
}

async fn post_request(req: payjoin::Request) -> Result<reqwest::Response> {
    let http = http_agent()?;
    http.post(req.url)
        .header("Content-Type", req.content_type)
        .body(req.body)
        .send()
        .await
        .map_err(map_reqwest_err)
}

fn map_reqwest_err(e: reqwest::Error) -> anyhow::Error {
    match e.status() {
        Some(status_code) => anyhow!("HTTP request failed: {} {}", status_code, e),
        None => anyhow!("No HTTP response: {}", e),
    }
}
