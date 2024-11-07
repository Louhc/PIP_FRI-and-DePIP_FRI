use crate::account::AccountInformationVar;
use crate::ledger::*;
use crate::transaction::TransactionVar;
use ark_simple_payments::ConstraintF;
use ark_r1cs_std::prelude::*;
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_simple_payments::{
    account::AccountInformation,
    ledger::{AccPath, AccRoot, Parameters, State, Amount},
    transaction::Transaction,
};
use ark_std::Zero;
use ark_relations::lc;

pub struct DeRollup<const NUM_TX: usize, const NUM_PARTIES: usize> {
    /// The ledger parameters.
    pub ledger_params: Parameters,
    /// The Merkle tree root before applying this batch of transactions.
    pub initial_root: Option<AccRoot>,
    /// The Merkle tree root after applying this batch of transactions.
    pub final_root: Option<AccRoot>,
    /// The current batch of transactions.
    pub transactions: Option<Vec<Transaction>>,
    /// The sender's account information and corresponding authentication path,
    /// *before* applying the transactions.
    pub sender_pre_tx_info_and_paths: Option<Vec<(AccountInformation, AccPath)>>,
    /// The authentication path corresponding to the sender's account information
    /// *after* applying the transactions.
    pub sender_post_paths: Option<Vec<AccPath>>,
    /// The recipient's account information and corresponding authentication path,
    /// *before* applying the transactions.
    pub recv_pre_tx_info_and_paths: Option<Vec<(AccountInformation, AccPath)>>,
    /// The authentication path corresponding to the recipient's account information
    /// *after* applying the transactions.
    pub recv_post_paths: Option<Vec<AccPath>>,
    /// List of state roots, so that the i-th root is the state roots before applying
    /// the i-th transaction. This means that `pre_tx_roots[0] == initial_root`.
    pub pre_tx_roots: Option<Vec<AccRoot>>,
    /// List of state roots, so that the i-th root is the state root after applying
    /// the i-th transaction. This means that `post_tx_roots[NUM_TX - 1] == final_root`.
    pub post_tx_roots: Option<Vec<AccRoot>>,
}

impl<const NUM_TX: usize, const NUM_PARTIES: usize> DeRollup<NUM_TX, NUM_PARTIES> {
    pub fn new_empty(ledger_params: Parameters) -> Self {
        Self {
            ledger_params,
            initial_root: None,
            final_root: None,
            transactions: None,
            sender_pre_tx_info_and_paths: None,
            sender_post_paths: None,
            recv_pre_tx_info_and_paths: None,
            recv_post_paths: None,
            pre_tx_roots: None,
            post_tx_roots: None,
        }
    }

    pub fn only_initial_and_final_roots(
        ledger_params: Parameters,
        initial_root: AccRoot,
        final_root: AccRoot,
    ) -> Self {
        Self {
            ledger_params,
            initial_root: Some(initial_root),
            final_root: Some(final_root),
            transactions: None,
            sender_pre_tx_info_and_paths: None,
            sender_post_paths: None,
            recv_pre_tx_info_and_paths: None,
            recv_post_paths: None,
            pre_tx_roots: None,
            post_tx_roots: None,
        }
    }

    pub fn with_state_and_transactions(
        ledger_params: Parameters,
        transactions: &[Transaction],
        state: &mut State,
        validate_transactions: bool,
    ) -> Option<Self> {
        assert_eq!(transactions.len(), NUM_TX);
        let initial_root = Some(state.root());
        let mut sender_pre_tx_info_and_paths = Vec::with_capacity(NUM_TX);
        let mut recipient_pre_tx_info_and_paths = Vec::with_capacity(NUM_TX);
        let mut sender_post_paths = Vec::with_capacity(NUM_TX);
        let mut recipient_post_paths = Vec::with_capacity(NUM_TX);
        let mut pre_tx_roots = Vec::with_capacity(NUM_TX);
        let mut post_tx_roots = Vec::with_capacity(NUM_TX);
        for tx in transactions {
            if !tx.validate(&ledger_params, &*state) && validate_transactions {
                return None;
            }
        }
        for tx in transactions {
            let sender_id = tx.sender;
            let recipient_id = tx.recipient;
            let pre_tx_root = state.root();
            let sender_pre_acc_info = *state.id_to_account_info.get(&sender_id)?;
            let sender_pre_path = state
                .account_merkle_tree
                .generate_proof(sender_id.0 as usize)
                .unwrap();
            let recipient_pre_acc_info = *state.id_to_account_info.get(&recipient_id)?;
            let recipient_pre_path = state
                .account_merkle_tree
                .generate_proof(recipient_id.0 as usize)
                .unwrap();

            if validate_transactions {
                state.apply_transaction(&ledger_params, tx)?;
            } else {
                let _ = state.apply_transaction(&ledger_params, tx);
            }
            let post_tx_root = state.root();
            let sender_post_path = state
                .account_merkle_tree
                .generate_proof(sender_id.0 as usize)
                .unwrap();
            let recipient_post_path = state
                .account_merkle_tree
                .generate_proof(recipient_id.0 as usize)
                .unwrap();
            sender_pre_tx_info_and_paths.push((sender_pre_acc_info, sender_pre_path));
            recipient_pre_tx_info_and_paths.push((recipient_pre_acc_info, recipient_pre_path));
            sender_post_paths.push(sender_post_path);
            recipient_post_paths.push(recipient_post_path);
            pre_tx_roots.push(pre_tx_root);
            post_tx_roots.push(post_tx_root);
        }

        Some(Self {
            ledger_params,
            initial_root,
            final_root: Some(state.root()),
            transactions: Some(transactions.to_vec()),
            sender_pre_tx_info_and_paths: Some(sender_pre_tx_info_and_paths),
            recv_pre_tx_info_and_paths: Some(recipient_pre_tx_info_and_paths),
            sender_post_paths: Some(sender_post_paths),
            recv_post_paths: Some(recipient_post_paths),
            pre_tx_roots: Some(pre_tx_roots),
            post_tx_roots: Some(post_tx_roots),
        })
    }
}

impl<const NUM_TX: usize, const NUM_PARTIES: usize> ConstraintSynthesizer<ConstraintF> for DeRollup<NUM_TX, NUM_PARTIES> {
    #[tracing::instrument(target = "r1cs", skip(self, cs))]
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<ConstraintF>,
    ) -> Result<(), SynthesisError> {
        let num_tx_per = NUM_TX / NUM_PARTIES;
        assert_eq!(NUM_TX, NUM_PARTIES * num_tx_per);

        // Declare the parameters as constants.
        let ledger_params = ParametersVar::new_constant(
            ark_relations::ns!(cs, "Ledger parameters"),
            &self.ledger_params,
        )?;
        // Declare the initial root as a public input.
        let initial_root = AccRootVar::new_input(ark_relations::ns!(cs, "Initial root"), || {
            self.initial_root.ok_or(SynthesisError::AssignmentMissing)
        })?;

        // Declare the final root as a public input.
        let final_root = AccRootVar::new_input(ark_relations::ns!(cs, "Final root"), || {
            self.final_root.ok_or(SynthesisError::AssignmentMissing)
        })?;
        let mut prev_root = initial_root;

        let mut last_cons_num = 0;
        let mut last_vars_num = 0;
        let mut last_power_of_two = 0;

        for j in 0..NUM_PARTIES {
            for k in 0..num_tx_per {
                let i = j * num_tx_per + k;
                let tx = self.transactions.as_ref().and_then(|t| t.get(i));
    
                let sender_acc_info = self.sender_pre_tx_info_and_paths.as_ref().map(|t| t[i].0);
                let sender_pre_path = self.sender_pre_tx_info_and_paths.as_ref().map(|t| &t[i].1);
    
                let recipient_acc_info = self.recv_pre_tx_info_and_paths.as_ref().map(|t| t[i].0);
                let recipient_pre_path = self.recv_pre_tx_info_and_paths.as_ref().map(|t| &t[i].1);
    
                let sender_post_path = self.sender_post_paths.as_ref().map(|t| &t[i]);
                let recipient_post_path = self.recv_post_paths.as_ref().map(|t| &t[i]);
    
                let pre_tx_root = self.pre_tx_roots.as_ref().map(|t| t[i]);
                let post_tx_root = self.post_tx_roots.as_ref().map(|t| t[i]);
    
                // Let's declare all these things!
    
                let tx = TransactionVar::new_witness(ark_relations::ns!(cs, "Transaction"), || {
                    tx.ok_or(SynthesisError::AssignmentMissing)
                })?;
                // Declare the sender's initial account balance...
                let sender_acc_info = AccountInformationVar::new_witness(
                    ark_relations::ns!(cs, "Sender Account Info"),
                    || sender_acc_info.ok_or(SynthesisError::AssignmentMissing),
                )?;
                // ..., corresponding authentication path, ...
                let sender_pre_path =
                    AccPathVar::new_witness(ark_relations::ns!(cs, "Sender Pre-Path"), || {
                        sender_pre_path.ok_or(SynthesisError::AssignmentMissing)
                    })?;
                // ... and authentication path after the update.
                // TODO: Fill in the following
                let sender_post_path =
                    AccPathVar::new_witness(ark_relations::ns!(cs, "Sender Post-Path"), || {
                        sender_post_path.ok_or(SynthesisError::AssignmentMissing)
                    })?;
    
                // Declare the recipient's initial account balance...
                let recipient_acc_info = AccountInformationVar::new_witness(
                    ark_relations::ns!(cs, "Recipient Account Info"),
                    || recipient_acc_info.ok_or(SynthesisError::AssignmentMissing),
                )?;
                // ..., corresponding authentication path, ...
                let recipient_pre_path =
                    AccPathVar::new_witness(ark_relations::ns!(cs, "Recipient Pre-Path"), || {
                        recipient_pre_path.ok_or(SynthesisError::AssignmentMissing)
                    })?;
    
                // ... and authentication path after the update.
                // TODO: Fill in the following
                let recipient_post_path =
                    AccPathVar::new_witness(ark_relations::ns!(cs, "Recipient Post-Path"), || {
                        recipient_post_path.ok_or(SynthesisError::AssignmentMissing)
                    })?;
    
                // Declare the state root before the transaction...
                let pre_tx_root =
                    AccRootVar::new_witness(ark_relations::ns!(cs, "Pre-tx Root"), || {
                        pre_tx_root.ok_or(SynthesisError::AssignmentMissing)
                    })?;
                // ... and after the transaction.
                let post_tx_root =
                    AccRootVar::new_witness(ark_relations::ns!(cs, "Post-tx Root"), || {
                        post_tx_root.ok_or(SynthesisError::AssignmentMissing)
                    })?;
    
                // Enforce that the state root after the previous transaction equals
                // the starting state root for this transaction
                prev_root.enforce_equal(&pre_tx_root)?;
    
                // Validate that the transaction signature and amount is correct.
                // TODO: Uncomment this
                tx.validate(
                    &ledger_params,
                    &sender_acc_info,
                    &sender_pre_path,
                    &sender_post_path,
                    &recipient_acc_info,
                    &recipient_pre_path,
                    &recipient_post_path,
                    &pre_tx_root,
                    &post_tx_root,
                )?
                .enforce_equal(&Boolean::TRUE)?;
    
                // Set the root for the next transaction.
                prev_root = post_tx_root;
            }

            if j == NUM_PARTIES - 1 {
                // Check that the final root is consistent with the root computed after
                // applying all state transitions
                // TODO: implement this
                prev_root.enforce_equal(&final_root)?;
            }

            let (total_cons_num, total_vars_num) = (cs.num_constraints(), cs.num_witness_variables() + cs.num_instance_variables());
            let cur_cons_num = total_cons_num - last_cons_num;
            let cur_vars_num = total_vars_num - last_vars_num; 

            // println!("Party {}: number of constraints: {}", j, cur_cons_num);
            // println!("Party {}: number of variables: {}", j, cur_vars_num);

            let new_next_power_of_two = (cur_cons_num.max(cur_cons_num)).next_power_of_two();
            // println!("Party {}: new_next_power_of_two: {}", j, new_next_power_of_two);

            if j == 0 {
                last_power_of_two = new_next_power_of_two;
            }
            assert_eq!(new_next_power_of_two, last_power_of_two);
            last_power_of_two = new_next_power_of_two;

            for _ in 0..new_next_power_of_two - cur_cons_num {
                cs.enforce_constraint(lc!(), lc!(), lc!())?;
            }
            for _ in 0..new_next_power_of_two - cur_vars_num {
                let _ = cs.new_witness_variable(|| Ok(ConstraintF::zero())).unwrap();
            }

            // println!("Total number of constraints: {}", cs.num_constraints());
            // println!("Total number of variables: {}", cs.num_witness_variables() + cs.num_instance_variables());

            (last_cons_num, last_vars_num) = (cs.num_constraints(), cs.num_witness_variables() + cs.num_instance_variables());

        }

        Ok(())
    }
}

pub fn build_multi_tx_circuit<const NUM_TX: usize, const NUM_PARTIES: usize>() -> DeRollup<NUM_TX, NUM_PARTIES> {
    let mut rng = ark_std::test_rng();
    let pp = Parameters::sample(&mut rng);
    let mut state = State::new(32, &pp);
    // Let's make an account for Alice.
    let (alice_id, _alice_pk, alice_sk) =
        state.sample_keys_and_register(&pp, &mut rng).unwrap();
    // Let's give her some initial balance to start with.
    state
        .update_balance(alice_id, Amount(NUM_TX as u64 + 1))
        .expect("Alice's account should exist");
    // Let's make an account for Bob.
    let (bob_id, _bob_pk, _bob_sk) = state.sample_keys_and_register(&pp, &mut rng).unwrap();

    let amount_to_send = 1;

    // Alice wants to transfer amount_to_send units to Bob, and does this NUM_TX times
    let mut temp_state = state.clone();
    let tx1 = Transaction::create(&pp, alice_id, bob_id, Amount(amount_to_send), &alice_sk, &mut rng);
    
    let rollup = DeRollup::<NUM_TX, NUM_PARTIES>::with_state_and_transactions(
        pp.clone(),
        &[tx1.clone(); NUM_TX],
        &mut temp_state,
        true,
    )
    .unwrap();
    rollup
}

#[cfg(test)]
mod test {
    use super::*;
    use ark_relations::r1cs::ConstraintSystem;

    #[test]
    fn test_de_padding () {
        const TX_NUM: usize = 1 << 2;
        const PARTIES_NUM: usize = 1 << 2;
        let cs = ConstraintSystem::<ConstraintF>::new_ref();
        let _circuit = build_multi_tx_circuit::<TX_NUM, PARTIES_NUM>().generate_constraints(cs.clone()).unwrap();
        // assert!(cs.is_satisfied().unwrap());
        println!("number of constraints: {:?}", cs.num_constraints());
        println!("number of variables: {:?}", cs.num_witness_variables() + cs.num_instance_variables());
        let mut cs = cs.borrow_mut().unwrap();
        cs.finalize();
        let _cs_matrix = cs.to_matrices().unwrap();
        // println!("cs_matrix.a[0].len(): {:?}", cs_matrix.a.0.len());
    }
}
