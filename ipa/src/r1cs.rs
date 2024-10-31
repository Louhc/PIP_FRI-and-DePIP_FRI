use ark_ff::{Zero, One};
use ark_ec::pairing::Pairing;
use rayon::prelude::*;
use my_kzg::{par_join_3, helper::generate_powers};
use itertools::MultiUnzip;
use ark_std::ops::AddAssign;
use ark_std::{cfg_iter, start_timer, end_timer};
use ark_relations::{
    lc,
    r1cs::{ConstraintSystemRef, ConstraintSynthesizer, SynthesisError},
};
use ark_std::{UniformRand, test_rng};
use std::marker::PhantomData;

#[derive(Clone)]
pub struct RandomCircuit<P: Pairing> {
    pub num_variables: usize,
    pub num_constraints: usize,
    pub m: usize,
    pub l: usize,
    _pairing: PhantomData<P>,
}

impl<P: Pairing> RandomCircuit<P> {
    pub fn new(
        num_variables: usize,
        num_constraints: usize,
        m: usize,
        l: usize,
    ) -> Self {
        Self {
            num_variables,
            num_constraints,
            m,
            l,
            _pairing: PhantomData,
        }
    }
}

impl<P: Pairing> ConstraintSynthesizer<P::ScalarField> for RandomCircuit<P> {
    fn generate_constraints(self, cs: ConstraintSystemRef<P::ScalarField>) -> Result<(), SynthesisError> {
        assert_eq!(self.num_variables, self.num_constraints);
        let n = (self.m - 1) / 3;
        let mut rng = test_rng();
        for k in 0..self.l {
            let (a_vec, b_vec, c_vec): (Vec<_>, Vec<_>, Vec<_>) = (0..n).map(|_| {
                let rand_a = P::ScalarField::rand(&mut rng);
                let rand_b = P::ScalarField::rand(&mut rng);
                let a = cs.new_witness_variable(|| Ok(rand_a) ).unwrap();
                let b = cs.new_witness_variable(|| Ok(rand_b) ).unwrap();
                let c = cs.new_witness_variable(|| Ok(rand_a * rand_b) ).unwrap();
                (a, b, c)
            }).multiunzip();

            for _ in 0..3 {
                for j in 0..n {
                    cs.enforce_constraint(lc!() + a_vec[j], lc!() + b_vec[j], lc!() + c_vec[j])?;
                }
            }
            
            let left = if k == 0 { self.m - n * 3 - 1 } else { self.m - n * 3 };
            for _ in 0..left {
                let _ = cs.new_witness_variable(|| Ok(P::ScalarField::rand(&mut rng))).unwrap();
            }
    
            for _ in 0..(self.m - 3 * n) {
                cs.enforce_constraint(lc!(), lc!(), lc!())?;
            }
        }

        Ok(())
    }
}


#[derive(Clone, Debug)]
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
        let timer = start_timer!(|| "R1CSVector build");
    
        // Each sub-prover holds m constraints
        assert_eq!(m, cs.num_constraints() / l);
        let f_zero = P::ScalarField::zero();
    
        let step = start_timer!(|| "CS to matrices");
        let cs = cs.borrow().unwrap();
        let cs_matrix = cs.to_matrices().unwrap();
        end_timer!(step);

        let step = start_timer!(|| "Evaluate constraints");
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
        
        end_timer!(step);
    
        let step = start_timer!(|| "sub vec x y z");
        let vec_r = generate_powers(&challenge_r, m * l);
    
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
        end_timer!(step);

        end_timer!(timer);

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
    
        let vec_r = generate_powers(challenge_r, m * l);

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