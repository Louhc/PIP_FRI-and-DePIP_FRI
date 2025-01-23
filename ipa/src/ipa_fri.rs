use ark_poly::{
    univariate::DensePolynomial as UnivariatePolynomial, DenseUVPolynomial, EvaluationDomain,
    GeneralEvaluationDomain, Polynomial, Evaluations
};
use std::marker::PhantomData;
use my_kzg::{uni_batch_kzg::BatchKZG, transcript::ProofTranscript, uni_trivial_kzg::{KZG, UniVerifierSRS}};
use crate::Error;
use merlin::Transcript;
use ark_ff::{Zero, Field, PrimeField};
use rayon::prelude::*;
use utils::merkle_tree::MERKLE_ROOT_SIZE;

pub struct IPA<T: PrimeField> {
    _field: PhantomData<T>,
}

// Simple implementation of univariate sum-check via KZG
impl<T: PrimeField> IPA<T> {

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

    pub fn trivial_ipa_commit_and_prove (
        vector_left: &Vec<T>,
        vector_right: &Vec<T>,
        domain: &GeneralEvaluationDomain<T>,
        transcript: &mut Transcript,
    ) -> Result<((P::G1, P::G1), (Vec<T>, Vec<P::G1>, P::G1)), Error> {
        assert_eq!(vector_left.len(), vector_right.len());
        assert_eq!(domain.size(), vector_left.len());

        // generate the polynomials f1(x) and f2(x)
        let coeffs_left = vector_left.clone();
        let evals_left = Evaluations::<T, GeneralEvaluationDomain<T>>::from_vec_and_domain(coeffs_left, *domain);
        let polynomial_left = evals_left.interpolate_by_ref();
        let coeffs_right = vector_right.clone();
        let evals_right = Evaluations::<T, GeneralEvaluationDomain<T>>::from_vec_and_domain(coeffs_right, *domain);
        let polynomial_right = evals_right.interpolate();

        // generate the commitment of f1 and f2
        let (com_left, com_right) = IPA::<P>::ipa_commit(&powers, &polynomial_left, &polynomial_right).unwrap();

        // compute the target polynomial
        let ifft_domain = <GeneralEvaluationDomain<T> as EvaluationDomain<T>>::new(domain.size() * 2).unwrap();
        let evals_left = polynomial_left.evaluate_over_domain_by_ref(ifft_domain);
        let evals_right = polynomial_right.evaluate_over_domain_by_ref(ifft_domain);
        let evals_target = &evals_left * &evals_right;
        let polynomial_target = evals_target.interpolate();

        // generate the proof
        let proof = IPA::<P>::sumcheck_prove(&powers, &polynomial_left, &polynomial_right, &polynomial_target, &com_left, &com_right, &domain, transcript).unwrap();
        Ok(((com_left, com_right), proof))
    }

    pub fn sumcheck_prove (
        polynomial_left: &UnivariatePolynomial<T>,
        polynomial_right: &UnivariatePolynomial<T>,
        polynomial_target: &UnivariatePolynomial<T>,
        com_left: &P::G1,
        com_right: &P::G1,
        // sum: &T,
        domain: &GeneralEvaluationDomain<T>,
        transcript: &mut Transcript,
    ) -> Result<(Vec<T>, Vec<P::G1>, P::G1), Error> {
        let (g, h, g_prime) = Self::get_g_h_g_prime(&polynomial_target, &domain);
        let helper_polynomials = vec![&g, &h, &g_prime];
        let helper_coms = BatchKZG::<P>::commit(&powers, &helper_polynomials).unwrap();

        // generate eta using fiat-shamir
        let mut slice_vector = helper_coms;
        slice_vector.push(com_left.clone());
        slice_vector.push(com_right.clone());
        let slice: &[P::G1] = &slice_vector;
        <Transcript as ProofTranscript<P>>::append_points(transcript, b"add commitments", slice);
        let alpha = <Transcript as ProofTranscript<P>>::challenge_scalar(
            transcript, b"random_evaluate_point");

        let proof = IPA::<P>::prove(&powers, &polynomial_left, &polynomial_right, &helper_polynomials, &alpha, transcript).unwrap();
        Ok(proof)
    }

    // generate the commitments and evaluations of f1,f2,g,h,g_prime,gu, as well as KZG proofs
    pub fn prove (
        // target polynomial
        polynomial_left: &UnivariatePolynomial<T>,
        polynomial_right: &UnivariatePolynomial<T>,
        // helper polynomials
        // for ldt: g, h, g_prime
        // for ours, g, h
        helper_polynomials: &[&UnivariatePolynomial<T>],
        point: &T,
        transcript: &mut Transcript,
    ) -> Result<(Vec<T>, Vec<P::G1>, P::G1), Error> {
        let mut evals = vec![polynomial_left.evaluate(&point), polynomial_right.evaluate(&point)];

        let mut polynomials = vec![polynomial_left, polynomial_right];
        for i in 0..helper_polynomials.len() {
            evals.push(helper_polynomials[i].evaluate(&point));
            polynomials.push(helper_polynomials[i]);
        }

        // evaluations of f1,f2,g_u,h or f1,f2,g,h,g_prime
        let proof_1 = evals;
        // commitments of g_u,h or g,h,g_prime
        let proof_2 = BatchKZG::<P>::commit(&powers, &helper_polynomials).unwrap();
        // proof of openings of f1,f2,g_u,h or f1,f2,g,h,g_prime
        let challenge = <Transcript as ProofTranscript<P>>::challenge_scalar(
            transcript, b"batch_kzg_rlc_challenge");
        let proof_3 = BatchKZG::<P>::open(&powers, &polynomials, &point, &challenge).unwrap();
        Ok((proof_1, proof_2, proof_3))
    }

}



#[cfg(test)]
mod tests{
    use ark_poly::{
        EvaluationDomain, 
        GeneralEvaluationDomain};
    use ark_std::rand::{rngs::StdRng, SeedableRng};
    use std::time::{Instant, Duration};
    use utils::goldilocks::Goldilocks as T;
    use crate::ipa::IPA;
    // use crate::sumcheck::SUMCHECK;
    use merlin::Transcript;
    use ark_ff::UniformRand;

    #[test]
    fn ipa_test() {
        let degree: usize = (1 << 2) - 1;
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
    
        // Trivial IPA_from_sumcheck prover
        let prover_start = Instant::now();
        let mut transcript : Transcript = Transcript::new(b"Trivial IPA from sumcheck");
        let proof = IPA::<T>::trivial_ipa_commit_and_prove(&g_alpha_powers, &vector_left, &vector_right, &domain, &mut transcript).unwrap();
        println!("Trivial IPA prover time: {:?} ms", prover_start.elapsed().as_millis());
    }

}