use ark_ff::{Zero, One};
use ark_ec::pairing::Pairing;
use ark_relations::r1cs::{
    ConstraintSystemRef, SynthesisError,
};
use rayon::prelude::*;
use my_kzg::par_join_3;
use itertools::MultiUnzip;

use my_ipa::helper::{R1CSVectors, R1CSPubVectors};


pub fn build_sub_instance<P: Pairing>(
    sub_prover_id: usize,
    m: usize,
    l: usize,
    challenge_r: &P::ScalarField,
    cs: ConstraintSystemRef<P::ScalarField>,
)-> Result<R1CSVectors<P>, SynthesisError> {

    // Each sub-prover holds m constraints
    assert_eq!(m, cs.num_constraints() / l);
    let f_zero = P::ScalarField::zero();

    let cs = cs.borrow().unwrap();
    let cs_matrix = cs.to_matrices().unwrap();
    let vec_w = cs.witness_assignment.to_vec();

    let start = m * sub_prover_id;
    let end = start + m;

    let (sub_vec_a, sub_vec_b, sub_vec_c): (Vec<P::ScalarField>, Vec<P::ScalarField>, Vec<P::ScalarField>) = (start..end)
        .map(|row_idx| (
            cs_matrix.a[row_idx]
                .par_iter()
                .map(|(val, id)| {
                        *val * vec_w[*id]
                    }).sum::<P::ScalarField>(),
            cs_matrix.b[row_idx]
                .par_iter()
                .map(|(val, id)| {
                        *val * vec_w[*id]
                    }).sum::<P::ScalarField>(),
            cs_matrix.c[row_idx]
                .par_iter()
                .map(|(val, id)| {
                        *val * vec_w[*id]
                    }).sum::<P::ScalarField>(),
            ),
        ).multiunzip();

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
                .for_each(|(val, id)| {
                    if start <= *id && *id < end {
                        sub_vec_x[*id - start] += *val * vec_r[row_idx].clone();
                    }
                });
            }
        },
        || {
            for row_idx in 0..m * l {
                cs_matrix.b[row_idx]
                .iter()
                .for_each(|(val, id)| {
                    if start <= *id && *id < end {
                        sub_vec_y[*id - start] += *val * vec_r[row_idx].clone();
                    }
                });
            }
        },
        || {
            for row_idx in 0..m * l {
                cs_matrix.c[row_idx]
                .iter()
                .for_each(|(val, id)| {
                    if start <= *id && *id < end {
                        sub_vec_z[*id - start] += *val * vec_r[row_idx].clone();
                    }
                });
            }
        }
    );

    Ok(R1CSVectors {
        vec_x: sub_vec_x,
        vec_y: sub_vec_y,
        vec_z: sub_vec_z,
        vec_w: vec_w[start..end].to_vec(),
        vec_a: sub_vec_a,
        vec_b: sub_vec_b,
        vec_c: sub_vec_c
    })
}


pub fn build_pub_instance<P: Pairing>(
    m: usize,
    l: usize,
    challenge_r: &P::ScalarField,
    cs: ConstraintSystemRef<P::ScalarField>,
)-> Result<R1CSPubVectors<P>, SynthesisError> {

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
                .for_each(|(val, id)| {
                    vec_x[*id] += *val * vec_r[row_idx];
                });
            }
        },
        || {
            for row_idx in 0..m * l {
                cs_matrix.b[row_idx]
                .iter()
                .for_each(|(val, id)| {
                    vec_y[*id] += *val * vec_r[row_idx];
                });
            }
        },
        || {
            for row_idx in 0..m * l {
                cs_matrix.c[row_idx]
                .iter()
                .for_each(|(val, id)| {
                    vec_z[*id] += *val * vec_r[row_idx];
                });
            }
        }
    );

    Ok(R1CSPubVectors {
        vec_x,
        vec_y,
        vec_z
    })
}

