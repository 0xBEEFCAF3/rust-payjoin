use std::fmt;

use bitcoin::{OutPoint, Psbt};

/// Error type for merging two unique unsigned PSBTs
#[derive(Debug, PartialEq)]
pub(crate) enum MergePsbtError {
    /// Input from other PSBT already exists in this PSBT
    InputAlreadyExists(OutPoint),
    /// Input is already signed
    MyInputIsSigned(OutPoint),
    /// Other PSBT's input is already signed
    OtherInputIsSigned(OutPoint),
}

impl fmt::Display for MergePsbtError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::InputAlreadyExists(outpoint) =>
                write!(f, "input already exists with outpoint: {}", outpoint),
            Self::MyInputIsSigned(outpoint) =>
                write!(f, "my input is already signed with outpoint: {}", outpoint),
            Self::OtherInputIsSigned(outpoint) =>
                write!(f, "other input is already signed with outpoint: {}", outpoint),
        }
    }
}

impl std::error::Error for MergePsbtError {}

pub(crate) trait MergePsbtExt: Sized {
    fn dangerous_clear_signatures(&mut self);
    fn merge_unsigned_tx(&mut self, other: Self) -> Result<(), Vec<MergePsbtError>>;
}

impl MergePsbtExt for Psbt {
    /// Clear all script sig and witness fields from this PSBT
    fn dangerous_clear_signatures(&mut self) {
        for input in self.inputs.iter_mut() {
            input.final_script_sig = None;
            input.final_script_witness = None;
        }
    }

    /// Try to merge two PSBTs
    /// PSBTs here are assumed to not have the same unsigned tx
    /// if you do have the same unsigned tx, use `combine` instead
    /// Note this method does not merge non inputs or outputs
    fn merge_unsigned_tx(&mut self, other: Self) -> Result<(), Vec<MergePsbtError>> {
        let mut errors = Vec::new();
        for (input, txin) in self.inputs.iter().zip(self.unsigned_tx.input.iter()) {
            if input.final_script_sig.is_some() || input.final_script_witness.is_some() {
                errors.push(MergePsbtError::MyInputIsSigned(txin.previous_output));
            }
        }

        // Do the same for the other PSBT down below
        let mut inputs_to_add = Vec::with_capacity(other.inputs.len());
        let mut txins_to_add = Vec::with_capacity(other.inputs.len());
        for (other_input, other_txin) in other.inputs.iter().zip(other.unsigned_tx.input.iter()) {
            if self.unsigned_tx.input.contains(other_txin) {
                errors.push(MergePsbtError::InputAlreadyExists(other_txin.previous_output));
            }

            if other_input.final_script_sig.is_some() || other_input.final_script_witness.is_some()
            {
                errors.push(MergePsbtError::OtherInputIsSigned(other_txin.previous_output));
                continue;
            }

            inputs_to_add.push(other_input.clone());
            txins_to_add.push(other_txin.clone());
        }

        let mut outputs_to_add = Vec::with_capacity(other.outputs.len());
        let mut txouts_to_add = Vec::with_capacity(other.outputs.len());
        for (other_output, other_txout) in other.outputs.iter().zip(other.unsigned_tx.output.iter())
        {
            // TODO(armins) if we recognize the exact same output this is a not neccecarily an error but an indication for an improved tx structure
            outputs_to_add.push(other_output.clone());
            txouts_to_add.push(other_txout.clone());
        }

        if !errors.is_empty() {
            return Err(errors);
        }

        self.inputs.extend(inputs_to_add);
        self.unsigned_tx.input.extend(txins_to_add);
        self.outputs.extend(outputs_to_add);
        self.unsigned_tx.output.extend(txouts_to_add);

        Ok(())
    }
}

// Tests
#[cfg(test)]
mod tests {
    use bitcoin::absolute::LockTime;
    use bitcoin::hashes::Hash;
    use bitcoin::key::rand::Rng;
    use bitcoin::secp256k1::rand::thread_rng;
    use bitcoin::secp256k1::SECP256K1;
    use bitcoin::{
        Amount, Network, OutPoint, Psbt, ScriptBuf, Sequence, Transaction, TxIn, TxOut, Txid,
        Witness,
    };

    use crate::psbt::merge::{MergePsbtError, MergePsbtExt};

    /// Util function to create a random p2wpkh script
    pub fn random_p2wpkh_script() -> ScriptBuf {
        let sk = bitcoin::PrivateKey::generate(Network::Bitcoin);
        let pk = sk.public_key(SECP256K1);

        pk.p2wpkh_script_code().unwrap()
    }

    /// Util function to create a random txid
    pub fn random_txid() -> Txid {
        let mut rng = thread_rng();
        let mut txid = [0u8; 32];
        rng.try_fill(&mut txid).expect("should fill");
        Txid::from_slice(&txid).unwrap()
    }

    // Util function to create a btc tx with random inputs and outputs as defined by fn params
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

    #[test]
    pub fn test_clear_signatures() {
        let mut psbt = Psbt::from_unsigned_tx(create_tx(1, 1)).unwrap();
        psbt.inputs[0].final_script_sig = Some(ScriptBuf::new());
        psbt.inputs[0].final_script_witness = Some(Witness::new());

        psbt.dangerous_clear_signatures();
        assert_eq!(psbt.inputs[0].final_script_sig, None);
        assert_eq!(psbt.inputs[0].final_script_witness, None);
    }
    #[test]
    fn test_merge_unsigned_tx() {
        let tx_1 = create_tx(1, 1);
        let tx_2 = create_tx(1, 1);
        let original_psbt = Psbt::from_unsigned_tx(tx_1).unwrap();
        let mut merged_psbt = original_psbt.clone();
        let other = Psbt::from_unsigned_tx(tx_2).unwrap();
        merged_psbt.merge_unsigned_tx(other.clone()).expect("should merge two unique psbts");

        assert_eq!(merged_psbt.inputs[0], original_psbt.inputs[0]);
        assert_eq!(merged_psbt.inputs[1], other.inputs[0]);
        assert_eq!(merged_psbt.outputs[0], original_psbt.outputs[0]);
        assert_eq!(merged_psbt.outputs[1], other.outputs[0]);

        // Assert unsigned tx is also updated
        let merged_tx = merged_psbt.unsigned_tx.clone();
        assert_eq!(merged_tx.input[0], original_psbt.unsigned_tx.input[0]);
        assert_eq!(merged_tx.input[1], other.unsigned_tx.input[0]);
        assert_eq!(merged_tx.output[0], original_psbt.unsigned_tx.output[0]);
        assert_eq!(merged_tx.output[1], other.unsigned_tx.output[0]);
    }

    #[test]
    fn should_not_merge_if_psbt_share_inputs() {
        let tx_1 = create_tx(1, 1);
        let original_psbt = Psbt::from_unsigned_tx(tx_1.clone()).unwrap();
        let mut merged_psbt = original_psbt.clone();
        let other = original_psbt.clone();

        let res = merged_psbt.merge_unsigned_tx(other.clone());
        assert!(res.is_err());
        assert_eq!(
            res.err().unwrap()[0],
            MergePsbtError::InputAlreadyExists(tx_1.input[0].previous_output)
        );
        // ensure the psbt has not been modified
        assert_eq!(merged_psbt, original_psbt);
    }

    #[test]
    fn should_not_merge_signed_psbt() {
        let tx_1 = create_tx(1, 1);
        let tx_2 = create_tx(1, 1);
        let mut original_psbt = Psbt::from_unsigned_tx(tx_1.clone()).unwrap();
        let mut other = Psbt::from_unsigned_tx(tx_2.clone()).unwrap();

        // Lets add some witness data
        original_psbt.inputs[0].final_script_witness = Some(Witness::new());
        other.inputs[0].final_script_witness = Some(Witness::new());
        let mut merged_psbt = original_psbt.clone();
        let res = merged_psbt.merge_unsigned_tx(other.clone());
        assert!(res.is_err());
        assert_eq!(
            res.err().unwrap()[0],
            MergePsbtError::MyInputIsSigned(tx_1.input[0].previous_output)
        );
        // ensure the psbt has not been modified
        assert_eq!(merged_psbt, original_psbt);
        // Lets try the same thing with the second psbt
        let err = merged_psbt.merge_unsigned_tx(other.clone()).err().unwrap();
        assert!(err.contains(&MergePsbtError::OtherInputIsSigned(tx_2.input[0].previous_output)));
        assert!(err.contains(&MergePsbtError::MyInputIsSigned(tx_1.input[0].previous_output)));
        // ensure the psbt has not been modified
        assert_eq!(merged_psbt, original_psbt);
    }
}
