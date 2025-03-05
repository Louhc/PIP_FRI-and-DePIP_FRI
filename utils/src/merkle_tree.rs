use rs_merkle::{Hasher, MerkleProof, MerkleTree};
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone)]
pub struct Blake3Algorithm {}

impl Hasher for Blake3Algorithm {
    type Hash = [u8; MERKLE_ROOT_SIZE];

    fn hash(data: &[u8]) -> [u8; MERKLE_ROOT_SIZE] {
        blake3::hash(data).into()
    }
}

pub const MERKLE_ROOT_SIZE: usize = 32;
#[derive(Clone)]
pub struct MerkleTreeProver {
    pub merkle_tree: MerkleTree<Blake3Algorithm>,
    leave_num: usize,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MerkleTreeVerifier {
    pub merkle_root: [u8; MERKLE_ROOT_SIZE],
    pub leave_number: usize,
}

// The Merkle tree prover
impl MerkleTreeProver {
    pub fn new(leaf_values: Vec<Vec<u8>>) -> Self {
        let leaves = leaf_values
            .iter()
            .map(|x| Blake3Algorithm::hash(x))
            .collect::<Vec<_>>();
        let merkle_tree = MerkleTree::<Blake3Algorithm>::from_leaves(&leaves);
        Self {
            merkle_tree,
            leave_num: leaf_values.len(),
        }
    }

    pub fn leave_num(&self) -> usize {
        self.leave_num
    }

    pub fn commit(&self) -> [u8; MERKLE_ROOT_SIZE] {
        self.merkle_tree.root().unwrap()
    }

    // Take the indices as input, open the entries as bytes
    pub fn open(&self, leaf_indices: &Vec<usize>) -> Vec<u8> {
        self.merkle_tree.proof(leaf_indices).to_bytes()
    }
}

impl MerkleTreeVerifier {
    pub fn new(leave_number: usize, merkle_root: &[u8; MERKLE_ROOT_SIZE]) -> Self {
        Self {
            leave_number,
            merkle_root: merkle_root.clone(),
        }
    }

    // Each leave is a vec of bytes
    pub fn verify(
        &self,
        proof_bytes: Vec<u8>,
        indices: &Vec<usize>,
        leaves: &Vec<Vec<u8>>,
    ) -> bool {
        let proof = MerkleProof::<Blake3Algorithm>::try_from(proof_bytes).unwrap();
        let leaves_to_prove: Vec<[u8; MERKLE_ROOT_SIZE]> =
            leaves.iter().map(|x| Blake3Algorithm::hash(x)).collect();
        proof.verify(
            self.merkle_root,
            indices,
            &leaves_to_prove,
            self.leave_number,
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::helper::Helper;
    use ark_test_curves::bls12_381::Fq;

    #[test]
    fn commit_and_open() {
        let leaf_values = vec![
            Helper::as_bytes_vec(&[Fq::from(1), Fq::from(2)]),
            Helper::as_bytes_vec(&[Fq::from(3), Fq::from(4)]),
            Helper::as_bytes_vec(&[Fq::from(5), Fq::from(6), Fq::from(6)]),
            Helper::as_bytes_vec(&[Fq::from(7), Fq::from(8)]),
            Helper::as_bytes_vec(&[Fq::from(9), Fq::from(10)]),
            Helper::as_bytes_vec(&[Fq::from(11), Fq::from(12)]),
            Helper::as_bytes_vec(&[Fq::from(13), Fq::from(14)]),
        ];
        let leave_number = leaf_values.len();
        let prover = MerkleTreeProver::new(leaf_values);
        let root = prover.commit();
        let verifier = MerkleTreeVerifier::new(leave_number, &root);
        let leaf_indices = vec![2, 3];
        println!("{:?}", leaf_indices);
        let proof_bytes = prover.open(&leaf_indices);
        let open_values = vec![
            Helper::as_bytes_vec(&[Fq::from(5), Fq::from(6), Fq::from(6)]),
            Helper::as_bytes_vec(&[Fq::from(7), Fq::from(8)]),
        ];
        println!("len: {}", proof_bytes.len() / 32);
        assert!(verifier.verify(proof_bytes, &leaf_indices, &open_values));
    }

    #[test]
    fn blake3() {
        let hash_res = Blake3Algorithm::hash("data".as_bytes());
        let hex_string = hex::encode(hash_res);
        assert_eq!(
            "28a249c2e4d3a92bc0a16ed8f1b5cf83ca20415ee12e502b096624902bbc97bd",
            hex_string
        );
    }
}
