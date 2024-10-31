use ark_poly::{univariate::DensePolynomial as UnivariatePolynomial, Evaluations, GeneralEvaluationDomain};
use std::marker::PhantomData;
use ark_ec::pairing::Pairing;

pub struct DeIPA<P: Pairing> {
    _pairing: PhantomData<P>,
}

impl<P: Pairing> DeIPA<P> {

    pub fn interpolate_from_eval_domain (
        evals: Vec<P::ScalarField>,
        domain: &GeneralEvaluationDomain<P::ScalarField>,
    ) -> UnivariatePolynomial<P::ScalarField> {
        let eval_domain = Evaluations::<P::ScalarField, GeneralEvaluationDomain<P::ScalarField>>::from_vec_and_domain(evals, *domain);
        eval_domain.interpolate()
    }

}

