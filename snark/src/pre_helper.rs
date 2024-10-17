use ark_poly::{univariate::DensePolynomial as UnivariatePolynomial, 
    // DenseUVPolynomial, 
    EvaluationDomain, Evaluations, GeneralEvaluationDomain, 
    // Polynomial
};
// use std::marker::PhantomData;
use ark_ec::pairing::Pairing;
use my_kzg::{biv_batch_kzg::BivBatchKZG, par_join_3, uni_batch_kzg::BatchKZG, uni_trivial_kzg::KZG};
// use merlin::Transcript;
// use my_ipa::helper::{R1CSPublicPolys, R1CSWitnessPolys, R1CSDePublicPolys};
use ark_ff::{Zero, One, Field};
use de_network::{DeMultiNet as Net, DeNet};
// use std::time::Instant;
use rayon::prelude::*;
use crate::indexer::DeLowerAandBEvals;


#[derive(Clone)]
// The original data of row index vectors for pa, pb, pc
pub struct DeRowIndex {
    pub row_pa_low: Vec<usize>,
    pub row_pa_high: Vec<usize>,
    pub row_pb_low: Vec<usize>,
    pub row_pb_high: Vec<usize>,
    pub row_pc_low: Vec<usize>,
    pub row_pc_high: Vec<usize>,
}

#[derive(Clone)]
// The original data of col index vectors for pa, pb, pc
pub struct DeColIndex {
    pub col_pa: Vec<usize>,
    pub col_pb: Vec<usize>,
    pub col_pc: Vec<usize>,
}

#[derive(Clone)]
// The original data of col index vectors for pa, pb, pc
pub struct DeValPolys<P: Pairing> {
    pub val_pa: UnivariatePolynomial<P::ScalarField>,
    pub val_pb: UnivariatePolynomial<P::ScalarField>,
    pub val_pc: UnivariatePolynomial<P::ScalarField>,
}


#[derive(Clone)]
// polynomials of A_low, A_high for rows, defined by r^{row_low} and r^{row_high}
pub struct DeAandTPolys<P: Pairing> {
    pub a_pa_low: UnivariatePolynomial<P::ScalarField>,
    pub a_pa_high: UnivariatePolynomial<P::ScalarField>,
    pub a_pb_low: UnivariatePolynomial<P::ScalarField>,
    pub a_pb_high: UnivariatePolynomial<P::ScalarField>,
    pub a_pc_low: UnivariatePolynomial<P::ScalarField>,
    pub a_pc_high: UnivariatePolynomial<P::ScalarField>,
    pub t_row_low: UnivariatePolynomial<P::ScalarField>,
    pub t_row_high: UnivariatePolynomial<P::ScalarField>,
}

#[derive(Clone)]
// evaluations of r^{row_low} and r^{row_high}, used in lookup
pub struct DeAandTEvals<P: Pairing> {
    pub eval_a_pa_low: Vec<P::ScalarField>,
    pub eval_a_pa_high: Vec<P::ScalarField>,
    pub eval_a_pb_low: Vec<P::ScalarField>,
    pub eval_a_pb_high: Vec<P::ScalarField>,
    pub eval_a_pc_low: Vec<P::ScalarField>,
    pub eval_a_pc_high: Vec<P::ScalarField>,
    pub eval_t_row_low: Vec<P::ScalarField>,
    pub eval_t_row_high: Vec<P::ScalarField>,
}

#[derive(Clone)]
// polynomials of B for columns, defined by alpha^{col}
pub struct DeBandTPolys<P: Pairing> {
    pub b_pa: UnivariatePolynomial<P::ScalarField>,
    pub b_pb: UnivariatePolynomial<P::ScalarField>,
    pub b_pc: UnivariatePolynomial<P::ScalarField>,
    pub t_col: UnivariatePolynomial<P::ScalarField>,
}

#[derive(Clone)]
// evaluations of alpha^{col}, used in lookup
pub struct DeBandTEvals<P: Pairing> {
    pub eval_b_pa: Vec<P::ScalarField>,
    pub eval_b_pb: Vec<P::ScalarField>,
    pub eval_b_pc: Vec<P::ScalarField>,
    pub eval_t_col: Vec<P::ScalarField>,
}

#[derive(Clone)]
// evaluations of n, used in lookup
pub struct NEvals<P: Pairing> {
    pub row_pa_low: Vec<P::ScalarField>,
    pub row_pa_high: Vec<P::ScalarField>,
    pub row_pb_low: Vec<P::ScalarField>,
    pub row_pb_high: Vec<P::ScalarField>,
    pub row_pc_low: Vec<P::ScalarField>,
    pub row_pc_high: Vec<P::ScalarField>,
    pub col_pa: Vec<P::ScalarField>,
    pub col_pb: Vec<P::ScalarField>,
    pub col_pc: Vec<P::ScalarField>,
}

pub fn compute_upper_a_t_polys_from_rows<P: Pairing> (
    // use x_domain for m, use m_domain for m prime
    m: usize,
    l: usize,
    x_domain: &GeneralEvaluationDomain<P::ScalarField>,
    m_domain: &GeneralEvaluationDomain<P::ScalarField>,
    sub_row: &DeRowIndex,
    r: &P::ScalarField,
) -> DeAandTPolys<P> {

    assert!(m.is_power_of_two());
    assert!(m_domain.size().is_power_of_two());
    assert!(m != m_domain.size());
    assert_eq!(sub_row.row_pa_low.len(), m_domain.size());
    let sqrt_ml = ((m * l) as f64).sqrt() as usize;
    let r_pow = r.pow([sqrt_ml as u64]);

    // compute A_pa_low and A_pa_high
    let (a_pa_low, a_pa_high) = rayon::join(
        || {
            let evals_a_pa_low = sub_row.row_pa_low.par_iter().map(|eval| r.pow([*eval as u64])).collect();
            let evals_a_pa_low = Evaluations::from_vec_and_domain(evals_a_pa_low, *m_domain);
            evals_a_pa_low.interpolate()
        }, 
        || {
            let evals_a_pa_high = sub_row.row_pa_high.par_iter().map(|eval| r_pow.pow([*eval as u64])).collect();
            let evals_a_pa_high = Evaluations::from_vec_and_domain(evals_a_pa_high, *m_domain);
            evals_a_pa_high.interpolate()
    });

    // compute A_pb_low and A_pb_high
    let (a_pb_low, a_pb_high) = rayon::join(
        || {
            let evals_a_pb_low = sub_row.row_pb_low.par_iter().map(|eval| r.pow([*eval as u64])).collect();
            let evals_a_pb_low = Evaluations::from_vec_and_domain(evals_a_pb_low, *m_domain);
            evals_a_pb_low.interpolate()
        }, 
        || {
            let evals_a_pb_high = sub_row.row_pb_high.par_iter().map(|eval| r_pow.pow([*eval as u64])).collect();
            let evals_a_pb_high = Evaluations::from_vec_and_domain(evals_a_pb_high, *m_domain);
            evals_a_pb_high.interpolate()
    });

    // compute A_pc_low and A_pc_high
    let (a_pc_low, a_pc_high) = rayon::join(
        || {
            let evals_a_pc_low = sub_row.row_pc_low.par_iter().map(|eval| r.pow([*eval as u64])).collect();
            let evals_a_pc_low = Evaluations::from_vec_and_domain(evals_a_pc_low, *m_domain);
            evals_a_pc_low.interpolate()
        }, 
        || {
            let evals_a_pc_high = sub_row.row_pc_high.par_iter().map(|eval| r_pow.pow([*eval as u64])).collect();
            let evals_a_pc_high = Evaluations::from_vec_and_domain(evals_a_pc_high, *m_domain);
            evals_a_pc_high.interpolate()
    });

    // compute T_low and T_high
    let (t_row_low, t_row_high) = if Net::am_master() {
        rayon::join(
            || {
                let t_low_evals = (0..m).into_par_iter().map(|i| r.pow([i as u64])).collect();
                let t_low_evals = Evaluations::from_vec_and_domain(t_low_evals, *x_domain);
                t_low_evals.interpolate()
            },
            || {
                let t_high_evals = (0..m).into_par_iter().map(|i| r_pow.pow([i as u64])).collect();
                let t_high_evals = Evaluations::from_vec_and_domain(t_high_evals, *x_domain);
                t_high_evals.interpolate()
            })
    } else {
        (UnivariatePolynomial::zero(), UnivariatePolynomial::zero())
    };
    
    DeAandTPolys {a_pa_low, a_pa_high, a_pb_low, a_pb_high, a_pc_low, a_pc_high, t_row_low, t_row_high}
}

pub fn commit_g1_h1_upper_a_t_polys<P: Pairing> (
    m_srs: &Vec<P::G1Affine>,
    x_srs: &Vec<P::G1Affine>,
    g1: &UnivariatePolynomial<P::ScalarField>, 
    h1: &UnivariatePolynomial<P::ScalarField>,
    upper_a_t_polys: &DeAandTPolys<P>,
) -> (Vec<P::G1>, Vec<P::G1>) {
    let set = upper_a_t_polys.clone();
    let polys_m_srs = vec![set.a_pa_low, set.a_pa_high, set.a_pb_low, set.a_pb_high, set.a_pc_low, set.a_pc_high];
    
    let polys_x_srs = if Net::am_master() {
            vec![g1.clone(), h1.clone(), set.t_row_low, set.t_row_high]
        } else {
            vec![g1.clone(), h1.clone()]
    };
    let coms_m_srs = BatchKZG::<P>::commit(&m_srs, &polys_m_srs).unwrap();
    let coms_x_srs = BatchKZG::<P>::commit(&x_srs, &polys_x_srs).unwrap();

    (coms_m_srs, coms_x_srs)
}

pub fn compute_upper_b_t_polys_from_cols<P: Pairing> (
    // use x_domain for m, use m_domain for m prime
    m: usize,
    x_domain: &GeneralEvaluationDomain<P::ScalarField>,
    m_domain: &GeneralEvaluationDomain<P::ScalarField>,
    sub_col: &DeColIndex,
    alpha: &P::ScalarField,
) -> DeBandTPolys<P> {

    assert!(m.is_power_of_two());
    assert!(m_domain.size().is_power_of_two());
    assert!(m != m_domain.size());
    assert_eq!(sub_col.col_pa.len(), m_domain.size());

    // compute B_pa, B_pb, B_pc
    let (b_pa, b_pb, b_pc) = par_join_3!(
        || {
            let evals_b_pa = sub_col.col_pa.par_iter().map(|eval| alpha.pow([*eval as u64])).collect();
            let evals_b_pa = Evaluations::from_vec_and_domain(evals_b_pa, *m_domain);
            evals_b_pa.interpolate()
        }, 
        || {
            let evals_b_pb = sub_col.col_pb.par_iter().map(|eval| alpha.pow([*eval as u64])).collect();
            let evals_b_pb = Evaluations::from_vec_and_domain(evals_b_pb, *m_domain);
            evals_b_pb.interpolate()
        }, 
        || {
            let evals_b_pc = sub_col.col_pc.par_iter().map(|eval| alpha.pow([*eval as u64])).collect();
            let evals_b_pc = Evaluations::from_vec_and_domain(evals_b_pc, *m_domain);
            evals_b_pc.interpolate()
        }
    );

    // compute T_col
    let t_col = if Net::am_master() {
        let t_col_evals = (0..m).into_par_iter().map(|i| alpha.pow([i as u64])).collect();
        let t_col_evals = Evaluations::from_vec_and_domain(t_col_evals, *x_domain);
        t_col_evals.interpolate()
    } else {
        UnivariatePolynomial::zero()
    };

    DeBandTPolys {b_pa, b_pb, b_pc, t_col}
}

pub fn commit_upper_b_t_polys<P: Pairing> (
    m_srs: &Vec<P::G1Affine>,
    x_srs: &Vec<P::G1Affine>,
    upper_b_t_polys: &DeBandTPolys<P>,
) -> (Vec<P::G1>, P::G1) {
    let set = upper_b_t_polys.clone();
    let polys_m_srs = vec![set.b_pa, set.b_pb, set.b_pc];
    let poly_x_srs = set.t_col;

    let coms_m_srs = BatchKZG::<P>::commit(&m_srs, &polys_m_srs).unwrap();
    let com_x_srs = KZG::<P>::commit(&x_srs, &poly_x_srs).unwrap();

    (coms_m_srs, com_x_srs)
}

pub fn compute_sub_f1_and_f2<P: Pairing> (
    lower_evals: &DeLowerAandBEvals<P>,
    a_t_evals: &DeAandTEvals<P>,
    b_t_evals: &DeBandTEvals<P>,
    n_evals: &NEvals<P>,
    m_domain: &GeneralEvaluationDomain<P::ScalarField>,
    x_domain: &GeneralEvaluationDomain<P::ScalarField>,
    gamma: &P::ScalarField,
    v: &P::ScalarField,
    beta: &P::ScalarField,
) -> (UnivariatePolynomial<P::ScalarField>, UnivariatePolynomial<P::ScalarField>) {

    assert_eq!(m_domain.size(), a_t_evals.eval_a_pa_low.len());

    let w = x_domain.group_gen();
    let elements: Vec<P::ScalarField> = (0..x_domain.size()).into_par_iter().map(|i| w.pow([i as u64])).collect();
    let factors: Vec<P::ScalarField> = (0..9).into_par_iter().map(|i| v.pow([i as u64])).collect();
    assert_eq!(factors[0], P::ScalarField::one());

    let evals_f2: Vec<P::ScalarField> = if Net::am_master() {
        let evals_row_pa_low: Vec<P::ScalarField> = n_evals.row_pa_low.par_iter()
            .zip(a_t_evals.eval_t_row_low.par_iter())
            .zip(elements.par_iter())
            .map(|((n, t), y)| *n * (*gamma + *beta * y + t).inverse().unwrap())
            .collect();
        let evals_row_pb_low: Vec<P::ScalarField> = n_evals.row_pb_low.par_iter()
            .zip(a_t_evals.eval_t_row_low.par_iter())
            .zip(elements.par_iter())
            .map(|((n, t), y)| factors[1] * n * (*gamma + *beta * y + t).inverse().unwrap())
            .collect();
        let evals_row_pc_low: Vec<P::ScalarField> = n_evals.row_pc_low.par_iter()
            .zip(a_t_evals.eval_t_row_low.par_iter())
            .zip(elements.par_iter())
            .map(|((n, t), y)| factors[2] * n * (*gamma + *beta * y + t).inverse().unwrap())
            .collect();
        let evals_row_pa_high: Vec<P::ScalarField> = n_evals.row_pa_high.par_iter()
            .zip(a_t_evals.eval_t_row_high.par_iter())
            .zip(elements.par_iter())
            .map(|((n, t), y)| factors[3] * n * (*gamma + *beta * y + t).inverse().unwrap())
            .collect();
        let evals_row_pb_high: Vec<P::ScalarField> = n_evals.row_pb_high.par_iter()
            .zip(a_t_evals.eval_t_row_high.par_iter())
            .zip(elements.par_iter())
            .map(|((n, t), y)| factors[4] * n * (*gamma + *beta * y + t).inverse().unwrap())
            .collect();
        let evals_row_pc_high: Vec<P::ScalarField> = n_evals.row_pc_high.par_iter()
            .zip(a_t_evals.eval_t_row_high.par_iter())
            .zip(elements.par_iter())
            .map(|((n, t), y)| factors[5] * n * (*gamma + *beta * y + t).inverse().unwrap())
            .collect();
        let evals_col_pa: Vec<P::ScalarField> = n_evals.col_pa.par_iter()
            .zip(b_t_evals.eval_t_col.par_iter())
            .zip(elements.par_iter())
            .map(|((n, t), y)| factors[6] * n * (*gamma + *beta * y + t).inverse().unwrap())
            .collect();
        let evals_col_pb: Vec<P::ScalarField> = n_evals.col_pb.par_iter()
            .zip(b_t_evals.eval_t_col.par_iter())
            .zip(elements.par_iter())
            .map(|((n, t), y)| factors[7] * n * (*gamma + *beta * y + t).inverse().unwrap())
            .collect();
        let evals_col_pc: Vec<P::ScalarField> = n_evals.col_pc.par_iter()
            .zip(b_t_evals.eval_t_col.par_iter())
            .zip(elements.par_iter())
            .map(|((n, t), y)| factors[8] * n * (*gamma + *beta * y + t).inverse().unwrap())
            .collect();
        evals_row_pa_low.par_iter().zip(evals_row_pa_high.par_iter()).zip(evals_row_pb_low.par_iter()).zip(evals_row_pb_high.par_iter())
            .zip(evals_row_pc_low.par_iter()).zip(evals_row_pc_high.par_iter()).zip(evals_col_pa.par_iter()).zip(evals_col_pb.par_iter()).zip(evals_col_pc.par_iter())
            .map(|((((((((pa_low, pa_high), pb_low), pb_high), pc_low), pc_high), col_pa), col_pb), col_pc)| *pa_low + *pa_high + *pb_low + *pb_high + *pc_low + *pc_high + *col_pa + *col_pb + *col_pc).collect() 
    } else {
        Vec::new()
    };

    let poly_f2 = if Net::am_master() {
        let eval_domain_f2 = Evaluations::<P::ScalarField>::from_vec_and_domain(evals_f2, *x_domain);
        eval_domain_f2.interpolate()
    } else {
        UnivariatePolynomial::zero()
    };

    let evals_sub_f1: Vec<P::ScalarField> = {
        let evals_row_pa_low: Vec<P::ScalarField> = lower_evals.eval_la_pa_low.par_iter()
            .zip(a_t_evals.eval_a_pa_low.par_iter())
            .map(|(lower, upper)| (*gamma + *beta * lower + upper).inverse().unwrap())
            .collect();
        let evals_row_pb_low: Vec<P::ScalarField> = lower_evals.eval_la_pb_low.par_iter()
            .zip(a_t_evals.eval_a_pb_low.par_iter())
            .map(|(lower, upper)| factors[1] * (*gamma + *beta * lower + upper).inverse().unwrap())
            .collect();
        let evals_row_pc_low: Vec<P::ScalarField> = lower_evals.eval_la_pc_low.par_iter()
            .zip(a_t_evals.eval_a_pc_low.par_iter())
            .map(|(lower, upper)| factors[2] * (*gamma + *beta * lower + upper).inverse().unwrap())
            .collect();
        let evals_row_pa_high: Vec<P::ScalarField> = lower_evals.eval_la_pa_high.par_iter()
            .zip(a_t_evals.eval_a_pa_high.par_iter())
            .map(|(lower, upper)| factors[3] * (*gamma + *beta * lower + upper).inverse().unwrap())
            .collect();
        let evals_row_pb_high: Vec<P::ScalarField> = lower_evals.eval_la_pb_high.par_iter()
            .zip(a_t_evals.eval_a_pb_high.par_iter())
            .map(|(lower, upper)| factors[4] * (*gamma + *beta * lower + upper).inverse().unwrap())
            .collect();
        let evals_row_pc_high: Vec<P::ScalarField> = lower_evals.eval_la_pc_high.par_iter()
            .zip(a_t_evals.eval_a_pc_high.par_iter())
            .map(|(lower, upper)| factors[5] * (*gamma + *beta * lower + upper).inverse().unwrap())
            .collect();
        let evals_col_pa: Vec<P::ScalarField> = lower_evals.eval_lb_pa.par_iter()
            .zip(b_t_evals.eval_b_pa.par_iter())
            .map(|(lower, upper)| factors[6] * (*gamma + *beta * lower + upper).inverse().unwrap())
            .collect();
        let evals_col_pb: Vec<P::ScalarField> = lower_evals.eval_lb_pb.par_iter()
            .zip(b_t_evals.eval_b_pb.par_iter())
            .map(|(lower, upper)| factors[7] * (*gamma + *beta * lower + upper).inverse().unwrap())
            .collect();
        let evals_col_pc: Vec<P::ScalarField> = lower_evals.eval_lb_pc.par_iter()
            .zip(b_t_evals.eval_b_pc.par_iter())
            .map(|(lower, upper)| factors[8] * (*gamma + *beta * lower + upper).inverse().unwrap())
            .collect();
        evals_row_pa_low.par_iter().zip(evals_row_pa_high.par_iter()).zip(evals_row_pb_low.par_iter()).zip(evals_row_pb_high.par_iter())
        .zip(evals_row_pc_low.par_iter()).zip(evals_row_pc_high.par_iter()).zip(evals_col_pa.par_iter()).zip(evals_col_pb.par_iter()).zip(evals_col_pc.par_iter())
        .map(|((((((((pa_low, pa_high), pb_low), pb_high), pc_low), pc_high), col_pa), col_pb), col_pc)| *pa_low + *pa_high + *pb_low + *pb_high + *pc_low + *pc_high + *col_pa + *col_pb + *col_pc).collect() 
    };
    let evals_domain_sub_f1 = Evaluations::from_vec_and_domain(evals_sub_f1, *m_domain);
    let sub_poly_f1 = evals_domain_sub_f1.interpolate();

    (sub_poly_f1, poly_f2)
}

pub fn commit_f1_f2<P: Pairing> (
    sub_prover_id: usize,
    m_powers: &Vec<Vec<P::G1Affine>>,
    x_srs: &Vec<P::G1Affine>,
    sub_poly_f1: &UnivariatePolynomial<P::ScalarField>,
    poly_f2: &UnivariatePolynomial<P::ScalarField>,
) -> (P::G1, P::G1) {
    let sub_polynomials = vec![sub_poly_f1.clone()];
    let com_f1 = BivBatchKZG::<P>::de_commit(sub_prover_id, &m_powers, &sub_polynomials);

    let (com_f1, com_f2) = if Net::am_master() {
        let com_f1 = com_f1.unwrap()[0];
        let com_f2 = KZG::<P>::commit(&x_srs, poly_f2).unwrap();
        (com_f1, com_f2)
    } else {
        (P::G1::zero(), P::G1::zero())
    };

    (com_f1, com_f2)
}

pub fn compute_g3_h3<P: Pairing> (
    val_polys: &DeValPolys<P>,
    upper_a_t_polys: &DeAandTPolys<P>,
    upper_b_t_polys: &DeBandTPolys<P>,
    m_domain: &GeneralEvaluationDomain<P::ScalarField>,
    beta: P::ScalarField,
    v: P::ScalarField,
    u3: P::ScalarField,
) -> Vec<P::G1> {
    
}

// // to prove T_col (omega x) = alpha T_col (x) for x \in {omega^j}, j \in [0, m-2]
// // we actually prove T_col(omega X) = alpha T_col(X) + L(X) (1 - alpha^m)
// pub fn prove_t_for_col_row<P: Pairing> (
//     powers: &[P::G1Affine],
//     m: usize,
//     domain: &GeneralEvaluationDomain<P::ScalarField>,
//     alpha: &P::ScalarField,
//     delta: &P::ScalarField,
// ) -> (Vec<P::ScalarField>, P::G1) {
//     assert_eq!(m, domain.size());
//     // find the generator
//     let omega = domain.group_gen();

//     // generate polynomial T_col
//     let t_col_evals: Vec<P::ScalarField> = (0..m).into_par_iter().map(|i| alpha.pow([i as u64])).collect();
//     let t_col_evals_on_domain = Evaluations::<P::ScalarField>::from_vec_and_domain(t_col_evals, *domain);
//     let t_col = t_col_evals_on_domain.interpolate();

//     // commit
//     let com_t_col = KZG::<P>::commit(&powers, &t_col).unwrap();

//     // open 1, delta, omega delta
//     let eval_one = P::ScalarField::one();
//     let eval_delta = t_col.evaluate(&delta);
//     let eval_omega_delta = t_col.evaluate(&(*delta * omega));
// }

