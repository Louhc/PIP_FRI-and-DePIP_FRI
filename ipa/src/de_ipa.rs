use ark_poly::{univariate::DensePolynomial as UnivariatePolynomial, Evaluations, GeneralEvaluationDomain};
use std::marker::PhantomData;
use ark_ec::pairing::Pairing;
// use my_kzg::{uni_batch_kzg::BatchKZG, biv_batch_kzg::BivBatchKZG, biv_trivial_kzg::VerifierSRS, helper::linear_combination_field, transcript::ProofTranscript, uni_trivial_kzg::UniVerifierSRS};
// use merlin::Transcript;
// use crate::{ipa::IPA, helper::{R1CSPublicPolys, R1CSWitnessPolys, R1CSDePublicPolys}};
// use ark_ff::{Zero, One, Field};
// use de_network::{DeMultiNet as Net, DeNet, DeSerNet};
// use std::time::{
//     Instant,
//     // Duration
// };
// use rayon::prelude::*;

pub struct DeIPA<P: Pairing> {
    _pairing: PhantomData<P>,
}

impl<P: Pairing> DeIPA<P> {

    pub fn interpolate_from_eval_domain (
        evals: &Vec<P::ScalarField>,
        domain: &GeneralEvaluationDomain<P::ScalarField>,
    ) -> UnivariatePolynomial<P::ScalarField> {
        let eval_domain = Evaluations::<P::ScalarField, GeneralEvaluationDomain<P::ScalarField>>::from_vec_and_domain(evals.clone(), *domain);
        eval_domain.interpolate()
    }

}

