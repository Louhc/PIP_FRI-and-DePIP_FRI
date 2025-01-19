use crate::helper::Helper;
use crate::merkle_tree::MerkleTreeVerifier;
use ark_ff::PrimeField;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::mem::size_of;

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct QueryResult<T: PrimeField> {
    pub proof_bytes: Vec<u8>,
    pub proof_values: HashMap<usize, T>,
}

impl<T: PrimeField> QueryResult<T> {
    pub fn verify_merkle_tree(
        &self,
        leaf_indices: &Vec<usize>,
        merkle_verifier: &MerkleTreeVerifier,
    ) -> bool {
        let leaves: Vec<Vec<u8>> = leaf_indices
            .iter()
            .map(|x| {
                Helper::to_bytes_vec(&[
                    self.proof_values.get(x).unwrap().clone(),
                    self.proof_values
                        .get(&(x + merkle_verifier.leave_number))
                        .unwrap()
                        .clone(),
                ])
            })
            .collect();
        let res = merkle_verifier.verify(self.proof_bytes.clone(), leaf_indices, &leaves);
        assert!(res);
        res
    }

    pub fn path_proof_size(&self) -> usize {
        self.proof_bytes.len()
    }

    pub fn field_proof_size(&self) -> usize {
        self.proof_values.len() * size_of::<T>()
    }

    pub fn proof_size(&self) -> usize {
        self.proof_bytes.len() + self.proof_values.len() * size_of::<T>()
    }
}
