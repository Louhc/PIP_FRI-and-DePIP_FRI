use ark_ff::{Zero, One};
use ark_ec::pairing::Pairing;
use ark_relations::r1cs::{
    ConstraintSystemRef, SynthesisError,
};
use rayon::prelude::*;
use my_kzg::par_join_3;
use itertools::MultiUnzip;
use ark_std::ops::AddAssign;
use ark_std::cfg_iter;

#[derive(Clone)]
pub struct R1CSVectors<P: Pairing> {
    pub vec_x: Vec<P::ScalarField>,
    pub vec_y: Vec<P::ScalarField>,
    pub vec_z: Vec<P::ScalarField>,
    pub vec_w: Vec<P::ScalarField>,
    pub vec_a: Vec<P::ScalarField>,
    pub vec_b: Vec<P::ScalarField>,
    pub vec_c: Vec<P::ScalarField>,
}

// From ark-groth16
pub fn evaluate_constraint<'a, LHS, RHS, R>(terms: &'a [(LHS, usize)], assignment: &'a [RHS]) -> R
where
    LHS: One + Send + Sync + PartialEq,
    RHS: Send + Sync + core::ops::Mul<&'a LHS, Output = RHS> + Copy,
    R: Zero + Send + Sync + AddAssign<RHS> + core::iter::Sum,
{
    // Need to wrap in a closure when using Rayon
    #[cfg(feature = "parallel")]
    let zero = || R::zero();
    #[cfg(not(feature = "parallel"))]
    let zero = R::zero();

    let res = cfg_iter!(terms).fold(zero, |mut sum, (coeff, index)| {
        let val = &assignment[*index];

        if coeff.is_one() {
            sum += *val;
        } else {
            sum += val.mul(coeff);
        }

        sum
    });

    // Need to explicitly call `.sum()` when using Rayon
    #[cfg(feature = "parallel")]
    return res.sum();
    #[cfg(not(feature = "parallel"))]
    return res;
}

impl<P:Pairing> R1CSVectors<P> {
    pub fn build(
        sub_prover_id: usize,
        m: usize,
        l: usize,
        challenge_r: P::ScalarField,
        cs: &ConstraintSystemRef<P::ScalarField>,
    )-> Result<Self, SynthesisError> {
    
        // Each sub-prover holds m constraints
        assert_eq!(m, cs.num_constraints() / l);
        let f_zero = P::ScalarField::zero();
    
        let cs = cs.borrow().unwrap();
        let cs_matrix = cs.to_matrices().unwrap();
        let vec_w = [&cs.instance_assignment[..], &cs.witness_assignment[..]].concat();
    
        let start = m * sub_prover_id;
        let end = start + m;

        let (sub_vec_a, sub_vec_b, sub_vec_c): (Vec<P::ScalarField>, Vec<P::ScalarField>, Vec<P::ScalarField>) = (start..end)
            .map(|row_idx| {
                let a: P::ScalarField = evaluate_constraint(&cs_matrix.a[row_idx], &vec_w);
                let b: P::ScalarField = evaluate_constraint(&cs_matrix.b[row_idx], &vec_w);
                let c: P::ScalarField = evaluate_constraint(&cs_matrix.c[row_idx], &vec_w);
                (a, b, c)
            }).multiunzip();
    
        let mut vec_r = Vec::new();
        let mut r_pow = P::ScalarField::one();
        for _ in 0..m * l {
            vec_r.push(r_pow.clone());
            r_pow *= challenge_r;
        }
    
        let mut sub_vec_x = vec![f_zero; m];
        let mut sub_vec_y = vec![f_zero; m];
        let mut sub_vec_z = vec![f_zero; m];
    
        par_join_3!(
            || {
                for row_idx in 0..m * l {
                    cs_matrix.a[row_idx]
                    .iter()
                    .for_each(|(coeff, id)| {
                        if start <= *id && *id < end {
                            sub_vec_x[*id - start] += *coeff * vec_r[row_idx].clone();
                        }
                    });
                }
            },
            || {
                for row_idx in 0..m * l {
                    cs_matrix.b[row_idx]
                    .iter()
                    .for_each(|(coeff, id)| {
                        if start <= *id && *id < end {
                            sub_vec_y[*id - start] += *coeff * vec_r[row_idx].clone();
                        }
                    });
                }
            },
            || {
                for row_idx in 0..m * l {
                    cs_matrix.c[row_idx]
                    .iter()
                    .for_each(|(coeff, id)| {
                        if start <= *id && *id < end {
                            sub_vec_z[*id - start] += *coeff * vec_r[row_idx].clone();
                        }
                    });
                }
            }
        );

        Ok( Self {
            vec_x: sub_vec_x,
            vec_y: sub_vec_y,
            vec_z: sub_vec_z,
            vec_w: vec_w[start..end].to_vec(),
            vec_a: sub_vec_a,
            vec_b: sub_vec_b,
            vec_c: sub_vec_c
        })
    }
}

#[derive(Clone)]
pub struct R1CSPubVectors<P:Pairing> {
    pub vec_x: Vec<P::ScalarField>,
    pub vec_y: Vec<P::ScalarField>,
    pub vec_z: Vec<P::ScalarField>,
}

impl<P:Pairing> R1CSPubVectors<P> {
    pub fn build(
        m: usize,
        l: usize,
        challenge_r: &P::ScalarField,
        cs: ConstraintSystemRef<P::ScalarField>,
    )-> Result<Self, SynthesisError> {
    
        // Each sub-prover holds m constraints
        assert_eq!(m, cs.num_constraints() / l);
        let f_zero = P::ScalarField::zero();
    
        let cs = cs.borrow().unwrap();
        let cs_matrix = cs.to_matrices().unwrap();
    
        let mut vec_r = Vec::new();
        let mut r_pow = P::ScalarField::one();
        for _ in 0..m * l {
            vec_r.push(r_pow.clone());
            r_pow *= challenge_r;
        }
    
        let mut vec_x = vec![f_zero; m * l];
        let mut vec_y = vec![f_zero; m * l];
        let mut vec_z = vec![f_zero; m * l];
    
        par_join_3!(
            || {
                for row_idx in 0..m * l {
                    cs_matrix.a[row_idx]
                    .iter()
                    .for_each(|(coeff, id)| {
                        vec_x[*id] += *coeff * vec_r[row_idx];
                    });
                }
            },
            || {
                for row_idx in 0..m * l {
                    cs_matrix.b[row_idx]
                    .iter()
                    .for_each(|(coeff, id)| {
                        vec_y[*id] += *coeff * vec_r[row_idx];
                    });
                }
            },
            || {
                for row_idx in 0..m * l {
                    cs_matrix.c[row_idx]
                    .iter()
                    .for_each(|(coeff, id)| {
                        vec_z[*id] += *coeff * vec_r[row_idx];
                    });
                }
            }
        );
    
        Ok( Self {
            vec_x,
            vec_y,
            vec_z
        })
    }    
}