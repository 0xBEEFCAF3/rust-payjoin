//! Utilities for merging unique v0 PSBTs

use std::fmt;

use bitcoin::absolute::LockTime;
use bitcoin::transaction::Version;
use bitcoin::{OutPoint, Psbt, Transaction};

const SUPPORTED_TX_VERSIONS: [i32; 1] = [2];

/// Error type for merging two unique unsigned PSBTs
#[derive(Debug)]
pub(crate) enum MergePsbtError {
    /// Input from other PSBT already exists in this PSBT
    InputAlreadyExists(OutPoint),
    /// Input is already signed
    InputIsSigned(OutPoint),
    /// Tx has unsupported version
    UnsupportedTxVersion(usize, i32),
    /// Tx has BIP68 locktime
    LockTime(usize),
    /// PSBT Error
    PsbtError(bitcoin::psbt::Error),
}

impl PartialEq for MergePsbtError {
    fn eq(&self, other: &Self) -> bool { self.to_string() == other.to_string() }
}

impl fmt::Display for MergePsbtError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::InputAlreadyExists(outpoint) =>
                write!(f, "input already exists with outpoint: {}", outpoint),
            Self::InputIsSigned(outpoint) =>
                write!(f, "input is already signed with outpoint: {}", outpoint),
            Self::UnsupportedTxVersion(index, version) =>
                write!(f, "tx at index {} has unsupported version: {}", index, version),
            Self::LockTime(index) => write!(f, "tx at index {} has locktime", index),
            Self::PsbtError(e) => write!(f, "psbt error: {}", e),
        }
    }
}

impl std::error::Error for MergePsbtError {}

#[allow(dead_code)]
pub(crate) trait MergePsbtExt: Sized {
    fn dangerous_clear_signatures(&mut self);
}

impl MergePsbtExt for Psbt {
    /// Clear all script sig and witness fields from this PSBT
    fn dangerous_clear_signatures(&mut self) {
        for input in self.inputs.iter_mut() {
            input.final_script_sig = None;
            input.final_script_witness = None;
        }
    }
}

#[allow(dead_code)]
/// Try to merge two PSBTs
/// PSBTs here are assumed to not have the same unsigned tx
/// if you do have the same unsigned tx, use `combine` instead
/// Note this method does not merge non inputs or outputs
pub(crate) fn merge_unsigned_tx(
    psbts: impl Iterator<Item = Psbt>,
) -> Result<Psbt, Vec<MergePsbtError>> {
    let mut errors = Vec::new();
    let mut unsigned_tx = Transaction {
        version: Version::TWO,
        lock_time: LockTime::ZERO,
        input: vec![],
        output: vec![],
    };

    for (index, psbt) in psbts.enumerate() {
        if !SUPPORTED_TX_VERSIONS.contains(&psbt.unsigned_tx.version.0) {
            errors.push(MergePsbtError::UnsupportedTxVersion(index, psbt.unsigned_tx.version.0));
        }

        if psbt.unsigned_tx.lock_time != LockTime::ZERO {
            errors.push(MergePsbtError::LockTime(index));
        }

        let index = psbt.inputs.iter().position(|input| {
            input.final_script_sig.is_some() || input.final_script_witness.is_some()
        });
        if let Some(index) = index {
            errors
                .push(MergePsbtError::InputIsSigned(psbt.unsigned_tx.input[index].previous_output));
        }

        if let Some(index) =
            psbt.unsigned_tx.input.iter().position(|input| unsigned_tx.input.contains(input))
        {
            errors.push(MergePsbtError::InputAlreadyExists(
                psbt.unsigned_tx.input[index].previous_output,
            ));
        }

        unsigned_tx.input.extend(psbt.unsigned_tx.input);
        unsigned_tx.output.extend(psbt.unsigned_tx.output);
    }

    if !errors.is_empty() {
        return Err(errors);
    }

    match Psbt::from_unsigned_tx(unsigned_tx) {
        Ok(psbt) => Ok(psbt),
        Err(e) => {
            errors.push(MergePsbtError::PsbtError(e));
            Err(errors)
        }
    }
}

#[cfg(test)]
mod tests {
    use bitcoin::absolute::{Height, LockTime};
    use bitcoin::hashes::Hash;
    use bitcoin::key::rand::Rng;
    use bitcoin::secp256k1::rand::thread_rng;
    use bitcoin::secp256k1::SECP256K1;
    use bitcoin::{
        Amount, Network, OutPoint, Psbt, ScriptBuf, Sequence, Transaction, TxIn, TxOut, Txid,
        Witness,
    };

    use super::merge_unsigned_tx;
    use crate::psbt::merge::{MergePsbtError, MergePsbtExt};

    /// Create a random p2wpkh script
    fn random_p2wpkh_script() -> ScriptBuf {
        let sk = bitcoin::PrivateKey::generate(Network::Bitcoin);
        let pk = sk.public_key(SECP256K1);

        pk.p2wpkh_script_code().unwrap()
    }

    /// Create a random 32 byte txid
    fn random_txid() -> Txid {
        let mut rng = thread_rng();
        let mut txid = [0u8; 32];
        rng.try_fill(&mut txid).expect("should fill");
        Txid::from_slice(&txid).unwrap()
    }

    /// Create a tx with random inputs and outputs
    /// Note: all outputs have the same 1000 sat value
    /// Transactions are created with version 2
    fn create_tx(num_inputs: usize, num_outputs: usize) -> Transaction {
        let txid = random_txid();

        let mut inputs = vec![];
        for i in 0..num_inputs {
            let op = OutPoint::new(txid, i as u32);
            inputs.push(TxIn {
                previous_output: op,
                script_sig: ScriptBuf::new(),
                sequence: Sequence::MAX,
                witness: Default::default(),
            });
        }

        let mut outputs = vec![];
        for _ in 0..num_outputs {
            outputs.push(TxOut {
                value: Amount::from_sat(1000),
                script_pubkey: random_p2wpkh_script(),
            });
        }

        Transaction {
            version: bitcoin::transaction::Version(2),
            lock_time: LockTime::ZERO,
            input: inputs,
            output: outputs,
        }
    }

    /// Test that we can clear script sig and witness from inputs
    #[test]
    fn test_clear_signatures() {
        let mut psbt = Psbt::from_unsigned_tx(create_tx(1, 1)).unwrap();
        psbt.inputs[0].final_script_sig = Some(ScriptBuf::new());
        psbt.inputs[0].final_script_witness = Some(Witness::new());

        psbt.dangerous_clear_signatures();
        assert_eq!(psbt.inputs[0].final_script_sig, None);
        assert_eq!(psbt.inputs[0].final_script_witness, None);
    }

    /// Test that we can merge two psbts with unique unsigned txs
    #[test]
    fn test_merge_unsigned_txs() {
        let txs = (0..10).map(|_| create_tx(2, 3)).collect::<Vec<_>>();
        let psbts = txs.iter().map(|tx| Psbt::from_unsigned_tx(tx.clone()).unwrap());
        let merged_psbt = merge_unsigned_tx(psbts).unwrap();

        for tx in txs.iter() {
            assert!(merged_psbt.unsigned_tx.input.contains(&tx.input[0]));
            assert!(merged_psbt.unsigned_tx.input.contains(&tx.input[1]));
            assert!(merged_psbt.unsigned_tx.output.contains(&tx.output[0]));
            assert!(merged_psbt.unsigned_tx.output.contains(&tx.output[1]));
            assert!(merged_psbt.unsigned_tx.output.contains(&tx.output[2]));
        }
    }

    /// Should not accept tx with locktimes
    #[test]
    fn test_merge_tx_with_locktime() {
        let mut tx = create_tx(1, 1);

        tx.lock_time = LockTime::Blocks(Height::from_consensus(100).unwrap());
        let psbt = Psbt::from_unsigned_tx(tx.clone()).unwrap();
        let psbts = vec![psbt.clone()];
        let err = merge_unsigned_tx(psbts.into_iter()).unwrap_err();
        assert_eq!(err.len(), 1);
        assert_eq!(err[0], MergePsbtError::LockTime(0));
    }

    /// Test we cannot merge txs with unsupported versions
    #[test]
    fn test_merge_tx_with_unsupported_version() {
        let tx1 = create_tx(1, 1);
        let mut tx2 = create_tx(1, 1);
        tx2.version = bitcoin::transaction::Version::non_standard(42);
        let psbts =
            vec![Psbt::from_unsigned_tx(tx1).unwrap(), Psbt::from_unsigned_tx(tx2).unwrap()];

        let err = merge_unsigned_tx(psbts.into_iter()).unwrap_err();
        assert_eq!(err.len(), 1);
        assert_eq!(err[0], MergePsbtError::UnsupportedTxVersion(1, 42));
    }

    /// Test merging empty PSBTs
    #[test]
    fn test_merge_empty_psbts() {
        let tx_1 = create_tx(0, 0);
        let tx_2 = create_tx(0, 0);
        let psbts =
            vec![Psbt::from_unsigned_tx(tx_1).unwrap(), Psbt::from_unsigned_tx(tx_2).unwrap()];

        let merged_psbt = merge_unsigned_tx(psbts.into_iter()).unwrap();

        assert_eq!(merged_psbt.inputs.len(), 0);
        assert_eq!(merged_psbt.outputs.len(), 0);
    }

    /// Test that we cannot merge two psbts if psbts share inputs
    #[test]
    fn should_not_merge_if_psbt_share_inputs() {
        let tx = create_tx(1, 1);
        let psbt = Psbt::from_unsigned_tx(tx.clone()).unwrap();
        let psbts = vec![psbt.clone(), psbt.clone()];

        let err = merge_unsigned_tx(psbts.into_iter()).unwrap_err();
        assert!(err.contains(&MergePsbtError::InputAlreadyExists(tx.input[0].previous_output)));
    }

    /// Test that we cannot merge two psbts if psbts have inputs with witness data
    #[test]
    fn should_not_merge_signed_psbt() {
        let tx_1 = create_tx(1, 1);
        let tx_2 = create_tx(1, 1);
        let mut original_psbt = Psbt::from_unsigned_tx(tx_1.clone()).unwrap();
        let mut other = Psbt::from_unsigned_tx(tx_2.clone()).unwrap();

        original_psbt.inputs[0].final_script_witness = Some(Witness::new());
        other.inputs[0].final_script_witness = Some(Witness::new());
        let psbts = vec![original_psbt.clone(), other.clone()];
        let err = merge_unsigned_tx(psbts.into_iter()).unwrap_err();
        assert!(err.contains(&MergePsbtError::InputIsSigned(tx_2.input[0].previous_output)));
        assert!(err.contains(&MergePsbtError::InputIsSigned(tx_1.input[0].previous_output)));

        original_psbt.dangerous_clear_signatures();
        other.dangerous_clear_signatures();
        original_psbt.inputs[0].final_script_sig = Some(ScriptBuf::new());
        other.inputs[0].final_script_sig = Some(ScriptBuf::new());
        let psbts = vec![original_psbt.clone(), other.clone()];
        let err2 = merge_unsigned_tx(psbts.into_iter()).unwrap_err();
        assert_eq!(err2, err);
    }

    /// Test merging PSBTs with only inputs or only outputs
    #[test]
    fn test_merge_inputs_or_outputs_only() {
        let tx_1 = create_tx(2, 0);
        let tx_2 = create_tx(0, 3);

        let psbts =
            vec![Psbt::from_unsigned_tx(tx_1).unwrap(), Psbt::from_unsigned_tx(tx_2).unwrap()];

        let merged_psbt = merge_unsigned_tx(psbts.into_iter()).unwrap();

        assert_eq!(merged_psbt.inputs.len(), 2);
        assert_eq!(merged_psbt.outputs.len(), 3);
    }
}
