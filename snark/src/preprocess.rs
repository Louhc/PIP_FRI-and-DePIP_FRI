use ark_poly::{univariate::DensePolynomial as UnivariatePolynomial, DenseUVPolynomial, EvaluationDomain, Evaluations, GeneralEvaluationDomain, Polynomial};
use std::marker::PhantomData;
use ark_ec::pairing::Pairing;
use my_kzg::{batch_kzg::BatchKZG, biv_batch_kzg::BivBatchKZG, biv_trivial_kzg::VerifierSRS, helper::linear_combination_field, transcript::ProofTranscript, trivial_kzg::{KZG, UniVerifierSRS}};
use merlin::Transcript;
use my_ipa::ipa::IPA;
use my_ipa::helper::{R1CSPublicPolys, R1CSWitnessPolys, R1CSDePublicPolys};
use ark_ff::{Zero, One, Field};
use de_network::{DeMultiNet as Net, DeNet, DeSerNet};
use std::time::{
    Instant,
    // Duration
};
use rayon::prelude::*;

// to prove T_col (omega x) = alpha T_col (x) for x \in {omega^j}, j \in [0, m-2]
// we actually prove T_col(omega X) = alpha T_col(X) + L(X) (1 - alpha^m)
pub fn prove_t_for_col_row<P: Pairing> (
    powers: &[P::G1Affine],
    m: usize,
    domain: &GeneralEvaluationDomain<P::ScalarField>,
    alpha: &P::ScalarField,
    delta: &P::ScalarField,
) -> (Vec<P::ScalarField>, P::G1) {
    assert_eq!(m, domain.size());
    // find the generator
    let omega = domain.group_gen();

    // generate polynomial T_col
    let t_col_evals: Vec<P::ScalarField> = (0..m).into_par_iter().map(|i| alpha.pow([i as u64])).collect();
    let t_col_evals_on_domain = Evaluations::<P::ScalarField>::from_vec_and_domain(t_col_evals, *domain);
    let t_col = t_col_evals_on_domain.interpolate();

    // commit
    let com_t_col = KZG::<P>::commit(&powers, &t_col).unwrap();

    // open 1, delta, omega delta
    let eval_one = P::ScalarField::one();
    let eval_delta = t_col.evaluate(&delta);
    let eval_omega_delta = t_col.evaluate(&(*delta * omega));
}