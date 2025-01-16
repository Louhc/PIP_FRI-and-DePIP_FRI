use ark_ff::{PrimeField, batch_inversion};
use ark_poly::polynomial::univariate::DensePolynomial as UnivariatePolynomial;
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain};

use super::verifier::Verifier;
// use util::algebra::polynomial::Polynomial;

use utils::merkle_tree::MERKLE_ROOT_SIZE;
use utils::query_result::QueryResult;
use utils::{commit_open_vec::ComOpenOneVec, fiat_shamir::RandomOracle};

#[derive(Clone)]
pub struct Prover<T: PrimeField> {
    total_round: usize,
    polynomial: UnivariatePolynomial<T>,
    // cosets of each round
    interpolate_cosets: Vec<GeneralEvaluationDomain<T>>,
    // fft evaluations of each round, but only the first is computed from fft
    interpolations: Vec<ComOpenOneVec<T>>,
    oracle: RandomOracle<T>,
    final_value: Option<T>,
}

impl<T: PrimeField> Prover<T> {
    pub fn new(
        total_round: usize,
        interpolate_coset: &Vec<GeneralEvaluationDomain<T>>,
        polynomial: UnivariatePolynomial<T>,
        oracle: &RandomOracle<T>,
    ) -> Prover<T> {
        let interpolate_polynomial =
            ComOpenOneVec::new(interpolate_coset[0].fft(&polynomial.coeffs));
        Prover {
            total_round,
            polynomial,
            interpolate_cosets: interpolate_coset.clone(),
            interpolations: vec![interpolate_polynomial],
            oracle: oracle.clone(),
            final_value: None,
        }
    }

    pub fn commit_polynomial(&self) -> [u8; MERKLE_ROOT_SIZE] {
        self.interpolations[0].commit()
    }

    pub fn commit_foldings(&self, verifier: &mut Verifier<T>) {
        for i in 1..self.total_round {
            let interpolation = &self.interpolations[i];
            verifier.receive_interpolation_root(interpolation.leave_num(), interpolation.commit());
        }
        verifier.set_final_value(self.final_value.unwrap());
    }

    fn evaluation_next_domain(&self, folding_value: &Vec<T>, round: usize, challenge: T) -> Vec<T> {
        let mut res = vec![];
        let len = self.interpolate_cosets[round].size();
        let coset = &self.interpolate_cosets[round];
        for i in 0..(len / 2) {
            let x = folding_value[i];
            let nx = folding_value[i + len / 2];
            let new_v = (x + nx) + challenge * (x - nx) * coset.element(i).inverse().unwrap();
            res.push(new_v);
        }
        res
    }

    pub fn prove(&mut self, point: T, eval: T) {
        // let mut res = None;
        for i in 0..self.total_round {
            let challenge = self.oracle.folding_challenges[i];
            let next_evalutation = if i == 0 {
                let mut inv_vec: Vec<T> = self.interpolate_cosets[0]
                    .elements()
                    .into_iter()
                    .map(|x| x - point)
                    .collect();
                batch_inversion(inv_vec.as_mut_slice());
                // let inv: Vec<T> = batch_inverse(
                //     &mut self.interpolate_cosets[0]
                //         .all_elements()
                //         .into_iter()
                //         .map(|x| x - point)
                //         .collect(),
                // );
                // res = Some(self.polynomial.evaluate(&point));
                let v = self.interpolations[0].vec.clone();
                self.evaluation_next_domain(
                    &v.into_iter()
                        .zip(inv_vec.into_iter())
                        .map(|(x, inv)| (x - eval) * inv)
                        .collect(),
                    i,
                    challenge,
                )
            } else {
                self.evaluation_next_domain(&self.interpolations[i].vec, i, challenge)
            };
            if i < self.total_round - 1 {
                self.interpolations
                    .push(ComOpenOneVec::new(next_evalutation));
            } else {
                self.final_value = Some(next_evalutation[0]);
            }
        }
        // res.unwrap()
    }

    pub fn open(&mut self, point: T, eval: T, verifier: &mut Verifier<T>) -> Vec<QueryResult<T>> {
        self.prove(point, eval);

        self.commit_foldings(verifier);

        let mut folding_res = vec![];
        let mut leaf_indices = self.oracle.query_list.clone();

        for i in 0..self.total_round {
            let len = self.interpolate_cosets[i].size();
            leaf_indices = leaf_indices.iter_mut().map(|v| *v % (len >> 1)).collect();
            leaf_indices.sort();
            leaf_indices.dedup();

            folding_res.push(self.interpolations[i].open(&leaf_indices));
        }
        folding_res
    }
}
