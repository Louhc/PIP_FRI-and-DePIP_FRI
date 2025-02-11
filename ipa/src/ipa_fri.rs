use ark_poly::{
    univariate::DensePolynomial as UnivariatePolynomial,
    GeneralEvaluationDomain,
    DenseUVPolynomial
};
use std::marker::PhantomData;
use ark_ff::PrimeField;

pub struct FRIIPA<T: PrimeField> {
    _field: PhantomData<T>,
}

// Simple implementation of univariate sum-check via KZG
impl<T: PrimeField> FRIIPA<T> {

    pub fn get_sum_on_domain (
        polynomial: &UnivariatePolynomial<T>,
        domain: &GeneralEvaluationDomain<T>,
    ) -> T {
        let evals = polynomial.evaluate_over_domain_by_ref(*domain);
        let mut sum = T::zero();
        for i in 0..evals.evals.len() {
            sum += evals.evals[i];
        }
        sum
    }

    pub fn get_g_h_g_prime (
        polynomial: &UnivariatePolynomial<T>,
        domain: &GeneralEvaluationDomain<T>,
    ) -> (UnivariatePolynomial<T>, UnivariatePolynomial<T>, UnivariatePolynomial<T>) {
        let (h, reminder_polynomial) = polynomial.divide_by_vanishing_poly(*domain).unwrap();
        let constant_term = reminder_polynomial.coeffs[0];
        let g_prime = reminder_polynomial + UnivariatePolynomial::from_coefficients_vec(vec![-constant_term]);
        assert_eq!(g_prime.coeffs[0], T::zero());
        let g = UnivariatePolynomial::from_coefficients_slice(&g_prime.coeffs[1..]);

        (g, h, g_prime)
    }

}

#[cfg(test)]
mod tests{
    use ark_poly::{
        EvaluationDomain,
        GeneralEvaluationDomain, Polynomial, Evaluations,
        univariate::DensePolynomial as UnivariatePolynomial,
        DenseUVPolynomial,
    };
    use fri::prover::BatchProver;
    use fri::verifier::BatchVerifier;
    use utils::{
        CODE_RATE, SECURITY_BITS, fiat_shamir::RandomOracle, 
        helper::Helper, merkle_tree::MERKLE_ROOT_SIZE,
    };
    use crate::ipa_fri::FRIIPA;
    use utils::goldilocks::Goldilocks as T;
    use ark_std::rand::{rngs::StdRng, SeedableRng};
    use ark_std::{log2, UniformRand};

    #[test]
    fn trivial_fri_ipa_test() {
        let degree: usize = (1 << 10) - 1;
        let size = degree + 1;
        let mut rng = StdRng::seed_from_u64(0u64);
        let domain = 
            <GeneralEvaluationDomain<T> as EvaluationDomain<T>>::new(size).unwrap();
        let mut vector_left = Vec::new();
        let mut vector_right = Vec::new();
        for _ in 0..size {
            vector_left.push(T::rand(&mut rng));
            vector_right.push(T::rand(&mut rng));
        }
        let inner_product: T = vector_left.iter().zip(vector_right.iter()).map(|(left, right)| left * right).sum();

        assert!(vector_left.len().is_power_of_two());
        assert_eq!(vector_left.len(), vector_right.len());
        assert_eq!(domain.size(), vector_left.len());

        // generate the polynomials f1(x) and f2(x)
        let coeffs_left = vector_left.clone();
        let evals_left = Evaluations::<T, GeneralEvaluationDomain<T>>::from_vec_and_domain(coeffs_left, domain);
        let polynomial_left = evals_left.interpolate_by_ref();
        let coeffs_right = vector_right.clone();
        let evals_right = Evaluations::<T, GeneralEvaluationDomain<T>>::from_vec_and_domain(coeffs_right, domain);
        let polynomial_right = evals_right.interpolate();

        // generate the commitment of f1 and f2
        let variable_num = log2(vector_left.len()) as usize;
        let mut interpolate_cosets = vec![EvaluationDomain::new_coset(1 << (variable_num+ CODE_RATE), T::from(1)).unwrap()];
        for i in 1..variable_num {
            interpolate_cosets.push(Helper::pow(&interpolate_cosets[i-1], 2));
        }

        // compute the target polynomial
        let ifft_domain = <GeneralEvaluationDomain<T> as EvaluationDomain<T>>::new(domain.size() * 2).unwrap();
        let evals_left = polynomial_left.evaluate_over_domain_by_ref(ifft_domain);
        let evals_right = polynomial_right.evaluate_over_domain_by_ref(ifft_domain);
        let evals_target = &evals_left * &evals_right;
        let polynomial_target = evals_target.interpolate();

        // compute polynomials g and h, and their evaluations
        let oracle = RandomOracle::new(variable_num, SECURITY_BITS / CODE_RATE);
        let (g, h, _g_prime) = FRIIPA::get_g_h_g_prime(&polynomial_target, &domain);
        let alpha = T::rand(&mut rng);
        let points = vec![alpha; 2];
        let evals_f = vec![polynomial_left.evaluate(&alpha), polynomial_right.evaluate(&alpha)];
        let evals_g_h = vec![g.evaluate(&alpha), h.evaluate(&alpha)];

        let mut prover_f = BatchProver::new(variable_num, &interpolate_cosets, &[polynomial_left, polynomial_right], &oracle);
        let coms_f = prover_f.commit_polynomial();
        let helper_polynomials = [g, h];
        let mut prover_g_h = BatchProver::new(variable_num, &interpolate_cosets, &helper_polynomials, &oracle);
        let coms_g_h = prover_g_h.commit_polynomial();

        // generate the evals and proofs and verifier
        let mut verifier_f = BatchVerifier::new(variable_num, &interpolate_cosets, coms_f, &oracle, &points);
        let mut verifier_g_h = BatchVerifier::new(variable_num, &interpolate_cosets, coms_g_h, &oracle, &points);
        let proof_f = prover_f.open(&points, &evals_f, &mut verifier_f);
        let proof_g_h = prover_g_h.open(&points, &evals_g_h, &mut verifier_g_h);

        // verify
        assert!(verifier_f.verify(&proof_f, &evals_f));
        assert!(verifier_g_h.verify(&proof_g_h, &evals_g_h));
        let eval_left = evals_f[0] * evals_f[1];
        let eval_right = alpha * evals_g_h[0] + inner_product / domain.size_as_field_element() + domain.evaluate_vanishing_polynomial(alpha) * evals_g_h[1];
        assert_eq!(eval_left, eval_right);
    }

    #[test]
    fn improved_fri_ipa_test() {
        let degree: usize = (1 << 10) - 1;
        let size = degree + 1;
        let mut rng = StdRng::seed_from_u64(0u64);
        let domain = 
            <GeneralEvaluationDomain<T> as EvaluationDomain<T>>::new(size).unwrap();
        let mut vector_left = Vec::new();
        let mut vector_right = Vec::new();
        for _ in 0..size {
            vector_left.push(T::rand(&mut rng));
            vector_right.push(T::rand(&mut rng));
        }
        let inner_product: T = vector_left.iter().zip(vector_right.iter()).map(|(left, right)| left * right).sum();

        assert!(vector_left.len().is_power_of_two());
        assert_eq!(vector_left.len(), vector_right.len());
        assert_eq!(domain.size(), vector_left.len());

        // generate the polynomials f1(x) and f2(x)
        let coeffs_left = vector_left.clone();
        let polynomial_left: UnivariatePolynomial<T> = UnivariatePolynomial::from_coefficients_vec(coeffs_left);
        let mut coeffs_right = vec![vector_right[0].clone()];
        let mut rest = vector_right.clone().split_off(1);
        rest.reverse();
        coeffs_right.extend(rest);
        let polynomial_right = UnivariatePolynomial::from_coefficients_vec(coeffs_right);

        // generate the commitment of f1 and f2
        let variable_num = log2(vector_left.len()) as usize;
        let mut interpolate_cosets = vec![EvaluationDomain::new_coset(1 << (variable_num+ CODE_RATE), T::from(1)).unwrap()];
        for i in 1..variable_num {
            interpolate_cosets.push(Helper::pow(&interpolate_cosets[i-1], 2));
        }

        // compute the target polynomial
        let ifft_domain = <GeneralEvaluationDomain<T> as EvaluationDomain<T>>::new(domain.size() * 2).unwrap();
        let evals_left = polynomial_left.evaluate_over_domain_by_ref(ifft_domain);
        let evals_right = polynomial_right.evaluate_over_domain_by_ref(ifft_domain);
        let evals_target = &evals_left * &evals_right;
        let polynomial_target = evals_target.interpolate();

        // compute polynomials g and h, and their evaluations
        let oracle = RandomOracle::new(variable_num, SECURITY_BITS / CODE_RATE);
        let (g, h, _g_prime) = FRIIPA::get_g_h_g_prime(&polynomial_target, &domain);
        let alpha = T::rand(&mut rng);
        let points = vec![alpha; 2];
        let evals_f = vec![polynomial_left.evaluate(&alpha), polynomial_right.evaluate(&alpha)];
        let evals_g_h = vec![g.evaluate(&alpha), h.evaluate(&alpha)];

        let mut prover_f = BatchProver::new(variable_num, &interpolate_cosets, &[polynomial_left, polynomial_right], &oracle);
        let coms_f = prover_f.commit_polynomial();
        let helper_polynomials = [g, h];
        let mut prover_g_h = BatchProver::new(variable_num, &interpolate_cosets, &helper_polynomials, &oracle);
        let coms_g_h = prover_g_h.commit_polynomial();

        // generate the evals and proofs and verifier
        let mut verifier_f = BatchVerifier::new(variable_num, &interpolate_cosets, coms_f, &oracle, &points);
        let mut verifier_g_h = BatchVerifier::new(variable_num, &interpolate_cosets, coms_g_h, &oracle, &points);
        let proof_f = prover_f.open(&points, &evals_f, &mut verifier_f);
        let proof_g_h = prover_g_h.open(&points, &evals_g_h, &mut verifier_g_h);

        // verify
        assert!(verifier_f.verify(&proof_f, &evals_f));
        assert!(verifier_g_h.verify(&proof_g_h, &evals_g_h));
        let eval_left = evals_f[0] * evals_f[1];
        let eval_right = alpha * evals_g_h[0] + inner_product + domain.evaluate_vanishing_polynomial(alpha) * evals_g_h[1];
        assert_eq!(eval_left, eval_right);

        // compute the proof size
        let proof_size = 2 * (proof_f.0.proof_size()
            + proof_f.1
                .iter()
                .map(|x| x.proof_size())
                .sum::<usize>()
            + (variable_num - 1) * MERKLE_ROOT_SIZE);
        println!("proof size is: {:?} KB", proof_size / 1024);
    }

}