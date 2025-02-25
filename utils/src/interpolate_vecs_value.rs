use ark_ff::PrimeField;
use crate::helper::{MultilinearPolynomial, nearest_power_of_two, Helper};
use std::collections::HashMap;
use crate::merkle_tree::{MerkleTreeVerifier, MerkleTreeProver};
use crate::merkle_tree::MERKLE_ROOT_SIZE;

pub fn get_poly_num<T: PrimeField>(poly: &MultilinearPolynomial<T>) -> usize {
    nearest_power_of_two(poly.variable_num())
}

// for comparison with Orion, we set poly_num directly nearest_power_of_two
// we currently only use non-zk version as Orion
pub fn get_sub_variable_num<T: PrimeField>(poly: &MultilinearPolynomial<T>) -> usize {
    let poly_num = get_poly_num(poly);
    (poly.coefficients().len() / poly_num).ilog2() as usize
}

pub fn get_tensor<T: PrimeField>(x: &Vec<T>) -> Vec<T> {
    let mut ret = vec![T::ONE];
    x.iter().for_each(|&x| {
        let mut session: Vec<T> = ret.iter().map(|e| *e * x).collect();
        ret.append(&mut session);
    });
    ret
}

#[derive(Clone)]
pub struct InterpolateVecsValue<T: PrimeField> {
    pub values: Vec<Vec<T>>,
    merkle_tree: MerkleTreeProver,
}

// put multiple vectors into one Merkle tree
impl<T: PrimeField> InterpolateVecsValue<T> {
    pub fn new(values: Vec<Vec<T>>) -> Self {
        let len = values[0].len() / 2;
        let merkle_tree = MerkleTreeProver::new(
            (0..len)
                .map(|i| {
                    let mut vec_left = vec![];
                    let mut vec_right = vec![];
                    for j in 0..values.len() {
                        vec_left.push(values[j][i]);
                        vec_right.push(values[j][i + len]);
                    }
                    let vec = [vec_left, vec_right].concat();
                    Helper::to_bytes_vec(&vec)
                })
                .collect()
        );
        Self { values, merkle_tree }
    }

    pub fn leave_num(&self) -> usize {
        self.merkle_tree.leave_num()
    }

    pub fn commit(&self) -> [u8; MERKLE_ROOT_SIZE] {
        self.merkle_tree.commit()
    }

    pub fn query(&self, leaf_indices: &Vec<usize>) -> QueryVecsResult<T> {
        let len = self.merkle_tree.leave_num();
        let proof_values = leaf_indices
            .iter()
            .flat_map(|j| {
                let mut vec_left = vec![];
                let mut vec_right = vec![];
                for i in 0..self.values.len() {
                    vec_left.push(self.values[i][*j]);
                    vec_right.push(self.values[i][*j + len]);
                }
                [(*j, vec_left), (*j + len, vec_right)]
            })          
            .collect();
        let proof_bytes = self.merkle_tree.open(&leaf_indices);
        QueryVecsResult {
            proof_bytes,
            proof_values,
            vecs_length: self.values.len(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct QueryVecsResult<T: PrimeField> {
    pub proof_bytes: Vec<u8>,
    pub proof_values: HashMap<usize, Vec<T>>,
    pub vecs_length: usize,
}

impl<T: PrimeField> QueryVecsResult<T> {
    pub fn verify_merkle_tree(
        &self,
        leaf_indices: &Vec<usize>,
        merkle_verifier: &MerkleTreeVerifier,
    ) -> bool {
        let leaves: Vec<Vec<u8>> = leaf_indices
            .iter()
            .map(|x| {
                Helper::<T>::to_bytes_vec(&[
                    self.proof_values.get(x).unwrap().clone(),
                    self.proof_values
                        .get(&(x + merkle_verifier.leave_number))
                        .unwrap()
                        .clone(),
                ].concat())
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
        self.proof_values.len() * self.vecs_length * size_of::<T>()
    }

    pub fn proof_size(&self) -> usize {
        self.proof_bytes.len() + self.proof_values.len() * self.vecs_length * size_of::<T>()
    }
}

#[cfg(test)]
mod tests {
    use crate::goldilocks::Goldilocks as T;
    use rand::rngs::StdRng;
    use rand::SeedableRng;
    use ark_ff::{Field, UniformRand};
    use crate::helper::MultilinearPolynomial;
    use crate::merkle_tree::MerkleTreeVerifier;
    use crate::interpolate_vecs_value::*;

    // test for split polynomials and evaluations
    #[test]
    fn test_poly_split() {

        let mut rng = StdRng::seed_from_u64(0u64);
        let poly = MultilinearPolynomial::<T>::rand(6);
        let open_point: Vec<T> = (0..6)
            .into_iter()
            .map(|_| T::rand(&mut rng))
            .collect();
        let poly_eval = poly.evaluate(&open_point);

        let sub_poly_num = get_poly_num(&poly);
        let sub_polys = poly.chunks(sub_poly_num);
        let sub_poly_var_num = get_sub_variable_num(&poly);
        let (sub_poly_point, remaining_var) = open_point.split_at(sub_poly_var_num);

        // w_1, w_2, ...,
        let remaining_tensor = get_tensor(&remaining_var.to_vec());

        let eval_from_sub_polys = sub_polys
            .iter()
            .zip(remaining_tensor.iter())
            .fold(T::ZERO, |acc, (sub_poly, &w_i)| {
                acc + sub_poly.evaluate(&sub_poly_point.to_vec()) * w_i
            });

        assert_eq!(poly_eval, eval_from_sub_polys);
    }

    #[test]
    fn test_multiple_merkle() {
        let vec_1 = vec![T::from(1), T::from(2), T::from(3), T::from(4)];
        let vec_2 = vec![T::from(5), T::from(6), T::from(7), T::from(8)];
        let values = vec![vec_1, vec_2];
        let leave_number = values[0].len() / 2;

        let interpolation = InterpolateVecsValue::new(values);
        let root = interpolation.commit();
        let leaf_indices = vec![1];
        let query_result = interpolation.query(&leaf_indices);

        println!("proof_values are {:?}", query_result.proof_values);
        println!("proof_values[1] are {:?}", query_result.proof_values[&1]);

        let verifier = MerkleTreeVerifier::new(leave_number, &root);
        let is_valid = query_result.verify_merkle_tree(&leaf_indices, &verifier);
        assert!(is_valid);
    }
}