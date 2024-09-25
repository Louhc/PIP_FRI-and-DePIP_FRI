use ark_ff::{Field, PrimeField, Zero};
use ark_poly::{
    univariate::DensePolynomial as UnivariatePolynomial, EvaluationDomain, Evaluations as EvaluationsOnDomain,
    GeneralEvaluationDomain, Polynomial
};

use std::marker::PhantomData;

use ark_ec::{
    pairing::Pairing,
};

pub struct SUMCHECK<P: Pairing> {
    _pairing: PhantomData<P>,
}

// Simple implementation of univariate sum-check via KZG
impl<P: Pairing> SUMCHECK<P> {
    
}


#[cfg(test)]
mod tests{
    use ark_bls12_381::Bls12_381;
    use ark_ec::pairing::Pairing;
    use ark_poly::{univariate::DensePolynomial as UnivariatePolynomial, DenseUVPolynomial, EvaluationDomain, GeneralEvaluationDomain};
    use crate::sumcheck;
    use ark_ff::{BigInt, FftField, Field, One, Zero, PrimeField};
    use ark_ff::UniformRand;
    use ark_std::rand::{rngs::StdRng, SeedableRng};

    type MyField = <Bls12_381 as Pairing>::ScalarField;

    #[test]
    fn test_for_generate_domain() {
        let size: usize = 8;
        let mut rng = StdRng::seed_from_u64(0u64);
        let domain = 
            <GeneralEvaluationDomain<MyField> as EvaluationDomain<MyField>>::new(size).unwrap();
        let polynomial = UnivariatePolynomial::rand(16, &mut rng);

        let evals = polynomial.clone().evaluate_over_domain(domain);
        let mut sum = MyField::zero();
        for i in 0..evals.evals.len() {
            sum += evals.evals[i];
        }

        let (quotient_polynomial, reminder_polynomial) = polynomial.clone().divide_by_vanishing_poly(domain).unwrap();
        let right = quotient_polynomial.mul_by_vanishing_poly(domain) + reminder_polynomial.clone();
        assert_eq!(right, polynomial);

        let size_of_domain = MyField::from_bigint(BigInt::from(size as u64)).unwrap();
        
        let coeffs_reminder = reminder_polynomial.coeffs.to_vec();
        assert_eq!(coeffs_reminder[0], sum / size_of_domain);
    }
}