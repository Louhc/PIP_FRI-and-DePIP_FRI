use super::Tuple;
use ark_ff::PrimeField;
use utils::merkle_tree::MERKLE_ROOT_SIZE;
use utils::query_result::QueryResult;
use utils::fiat_shamir::RandomOracle;
use utils::merkle_tree::MerkleTreeVerifier;
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain};

#[derive(Clone)]
pub struct FriVerifier<T: PrimeField> {
    total_round: usize,
    interpolate_cosets: Vec<GeneralEvaluationDomain<T>>,
    function_root: Vec<(MerkleTreeVerifier, Vec<(T, T)>)>,
    folding_root: Vec<MerkleTreeVerifier>,
    oracle: RandomOracle<T>,
    final_value: Option<T>,
    open_point: Vec<T>,
}

impl<T: PrimeField> FriVerifier<T> {
    pub fn new(
        total_round: usize,
        coset: &Vec<GeneralEvaluationDomain<T>>,
        polynomial_commitment: [u8; MERKLE_ROOT_SIZE],
        oracle: &RandomOracle<T>,
        open_point: &Vec<T>,
    ) -> Self {
        FriVerifier {
            total_round,
            interpolate_cosets: coset.clone(),
            function_root: vec![(
                MerkleTreeVerifier {
                    leave_number: coset[0].size() / 2,
                    merkle_root: polynomial_commitment,
                },
                vec![],
            )],
            folding_root: vec![],
            oracle: oracle.clone(),
            final_value: None,
            open_point: open_point.to_vec(),
        }
    }

    pub fn get_open_point(&mut self) -> Vec<T> {
        let mut rng = rand::thread_rng();
        let point = (0..self.total_round)
            .map(|_| T::rand(&mut rng))
            .collect::<Vec<T>>();
        self.open_point = point.clone();
        point
    }

    pub fn append_function(&mut self, function_root: [u8; MERKLE_ROOT_SIZE]) {
        self.function_root.push((
            MerkleTreeVerifier {
                merkle_root: function_root,
                leave_number: self.interpolate_cosets[0].size() / 2,
            },
            vec![],
        ));
    }

    pub fn set_tuples(&mut self, tuples: &Vec<Tuple<T>>) {
        let beta = self.oracle.beta;
        for i in 0..tuples.len() {
            assert!(tuples[i].verify(beta, self.open_point[i]));
            self.function_root[i].1.push((beta, tuples[i].a));
            self.function_root[i].1.push((-beta, tuples[i].b));
            if i < tuples.len() - 1 {
                self.function_root[i + 1].1.push((beta * beta, tuples[i].c))
            }
        }
    }

    pub fn receive_folding_root(
        &mut self,
        leave_number: usize,
        folding_root: [u8; MERKLE_ROOT_SIZE],
    ) {
        self.folding_root.push(MerkleTreeVerifier {
            leave_number,
            merkle_root: folding_root,
        });
    }

    pub fn set_final_value(&mut self, value: T) {
        assert_ne!(value, T::zero());
        self.final_value = Some(value);
    }

    pub fn verify(
        &mut self,
        tuples: &Vec<Tuple<T>>,
        eval: T,
        folding_proofs: &Vec<QueryResult<T>>,
        function_proofs: &Vec<QueryResult<T>>,
    ) -> bool {

        self.set_tuples(tuples);
        let eval_test = tuples.last().unwrap().c;
        assert_eq!(eval_test, eval);

        let mut leaf_indices = self.oracle.query_list.clone();
        let rlc = self.oracle.rlc;
        for i in 0..self.total_round {
            let domain_size = self.interpolate_cosets[i].size();
            leaf_indices = leaf_indices
                .iter_mut()
                .map(|v| *v % (domain_size >> 1))
                .collect();
            leaf_indices.sort();
            leaf_indices.dedup();

            if i == 0 {
                for j in 0..function_proofs.len() {
                    assert!(function_proofs[j]
                        .verify_merkle_tree(&leaf_indices, &self.function_root[j].0));
                }
            } else {
                folding_proofs[i - 1].verify_merkle_tree(&leaf_indices, &self.folding_root[i - 1]);
            }

            let challenge = self.oracle.folding_challenges[i];
            let get_folding_value = |index: &usize| {
                if i == 0 {
                    let mut tmp_rlc = T::one();
                    let mut res = T::zero(); //function_proofs[0].proof_values[index];
                    for f in 0..self.function_root.len() {
                        let this_v = function_proofs[f].proof_values[index];
                        res += this_v * tmp_rlc;
                        tmp_rlc *= rlc;
                        for (x, y) in &self.function_root[f].1 {
                            res += tmp_rlc
                                * (this_v - *y)
                                * (self.interpolate_cosets[0].element(*index) - *x)
                                    .inverse()
                                    .unwrap();
                            tmp_rlc *= rlc
                        }
                    }
                    res
                } else {
                    folding_proofs[i - 1].proof_values[index]
                }
            };

            for j in &leaf_indices {
                let x = get_folding_value(j);
                let nx = get_folding_value(&(j + domain_size / 2));
                let v =
                    x + nx + challenge * (x - nx) * self.interpolate_cosets[i].element(*j).inverse().unwrap();
                if i < self.total_round - 1 {
                    if v != folding_proofs[i].proof_values[j] {
                        return false;
                    }
                } else {
                    if v != self.final_value.unwrap() {
                        return false;
                    }
                }
            }
        }
        true
    }
}
