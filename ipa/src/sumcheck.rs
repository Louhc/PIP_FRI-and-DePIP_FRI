use ark_ff::{Zero, One};
use ark_poly::{
    univariate::DensePolynomial as UnivariatePolynomial, DenseUVPolynomial, EvaluationDomain,
    GeneralEvaluationDomain, Polynomial,
};
use std::marker::PhantomData;
use ark_ec::pairing::Pairing;
use my_kzg::{batch_kzg::BatchKZG, transcript::ProofTranscript, trivial_kzg::{KZG, VerifierSRS}};
use crate::Error;
use merlin::Transcript;


pub struct SUMCHECK<P: Pairing> {
    _pairing: PhantomData<P>,
}

// Simple implementation of univariate sum-check via KZG
// The idea is postpone opening commitments until the last
impl<P: Pairing> SUMCHECK<P> {

    pub fn get_sum_on_domain (
        polynomial: &UnivariatePolynomial<P::ScalarField>,
        domain: &GeneralEvaluationDomain<P::ScalarField>,
    ) -> P::ScalarField {
        let evals = polynomial.clone().evaluate_over_domain(*domain);
        let mut sum = P::ScalarField::zero();
        for i in 0..evals.evals.len() {
            sum += evals.evals[i];
        }
        sum
    }

    pub fn get_g_h_g_prime (
        polynomial: &UnivariatePolynomial<P::ScalarField>,
        sum: &P::ScalarField,
        domain: &GeneralEvaluationDomain<P::ScalarField>,
    ) -> (UnivariatePolynomial<P::ScalarField>, UnivariatePolynomial<P::ScalarField>, UnivariatePolynomial<P::ScalarField>) {
        let (h, reminder_polynomial) = polynomial.clone().divide_by_vanishing_poly(*domain).unwrap();
        let constant_term = *sum / domain.size_as_field_element();
        let g_prime = reminder_polynomial + UnivariatePolynomial::from_coefficients_vec(vec![-constant_term]);
        assert_eq!(g_prime.coeffs[0], P::ScalarField::zero());
        let mut coeffs_g = g_prime.coeffs.clone();
        coeffs_g.remove(0);
        // let g = &g_prime / &UnivariatePolynomial::from_coefficients_vec(vec![P::ScalarField::zero(), P::ScalarField::one()]);
        let g = UnivariatePolynomial::from_coefficients_vec(coeffs_g);

        (g, h, g_prime)
    }

    pub fn get_g_mul_u_and_h (
        polynomial: &UnivariatePolynomial<P::ScalarField>,
        challenge: &P::ScalarField,
        sum: &P::ScalarField,
        domain: &GeneralEvaluationDomain<P::ScalarField>,
    ) -> (UnivariatePolynomial<P::ScalarField>, UnivariatePolynomial<P::ScalarField>) {
        let u = *challenge;
        let (h, reminder_polynomial) = polynomial.clone().divide_by_vanishing_poly(*domain).unwrap();
        let constant_term = *sum / domain.size_as_field_element();
        let g_prime = reminder_polynomial + UnivariatePolynomial::from_coefficients_vec(vec![-constant_term]);
        // Check the correctness of sum, the constant coefficient of g_prime should be zero
        assert_eq!(g_prime.coeffs[0], P::ScalarField::zero());
        let mut coeffs_g = g_prime.coeffs.clone();
        coeffs_g.remove(0);
        // let g = &g_prime / &UnivariatePolynomial::from_coefficients_vec(vec![P::ScalarField::zero(), P::ScalarField::one()]);
        let g = UnivariatePolynomial::from_coefficients_vec(coeffs_g);
        let g_u = &g * &UnivariatePolynomial::from_coefficients_vec(vec![-u, P::ScalarField::one()]);

        (g_u, h)
    }

     // generate the commitments and evaluations of g,h,g_prime,gu, as well as KZG proofs
     pub fn prove (
        powers: &[P::G1Affine],
        // target polynomial
        polynomial: &UnivariatePolynomial<P::ScalarField>,
        // helper polynomials
        // for ldt: g, h, g_prime
        // for ours, g, h
        helper_polynomials: &Vec<UnivariatePolynomial<P::ScalarField>>,
        point: &P::ScalarField,
        transcript: &mut Transcript,
    ) -> Result<(Vec<P::ScalarField>, Vec<P::G1>, P::G1), Error> {
        let mut evals = vec![polynomial.evaluate(&point)];
        let mut polynomials = vec![polynomial.clone()];
        for i in 0..helper_polynomials.len() {
            evals.push(helper_polynomials[i].evaluate(&point));
            polynomials.push(helper_polynomials[i].clone());
        }

        let proof_1 = evals;
        let proof_2 = BatchKZG::<P>::commit(&powers, &helper_polynomials).unwrap();
        let proof_3 = BatchKZG::<P>::open(&powers, &polynomials, &point, transcript).unwrap();
        Ok((proof_1, proof_2, proof_3))
    }

    pub fn get_proof_size (
        proof: &(Vec<P::ScalarField>, Vec<P::G1>, P::G1),
    ) -> usize {
        if proof.0.len() == 3 {
            (proof.1.len() + 1) * size_of_val(&proof.1[0]) +  proof.0.len() * size_of_val(&proof.0[0])
        }
        else {
            // -1 because g_prime(alpha) can be computed from g(alpha)
            (proof.1.len() + 1) * size_of_val(&proof.1[0]) +  (proof.0.len() - 1) * size_of_val(&proof.0[0])
        }
    }
    
    // partial trivial sumcheck verifier
    pub fn verify (
        v_srs: &VerifierSRS<P>,
        com: &P::G1,
        point: &P::ScalarField,
        domain: &GeneralEvaluationDomain<P::ScalarField>,
        sum: &P::ScalarField,
        proof: &(Vec<P::ScalarField>, Vec<P::G1>, P::G1),
        transcript: &mut Transcript,
    ) -> Result<bool, Error> {

        let z_h_eval = domain.evaluate_vanishing_polynomial(*point);
        let (evals, helper_coms, kzg_proof) = proof.clone();
        assert_eq!(helper_coms.len(), proof.0.len() - 1);
        let check1 = evals[0] == *point * evals[1] + *sum / domain.size_as_field_element() + z_h_eval * evals[2];
        assert!(check1);

        // let check2_start = Instant::now();
        let mut coms = vec![*com];
        for i in 0..helper_coms.len() {
            coms.push(helper_coms[i]);
        }
        let check2 = BatchKZG::<P>::verify(&v_srs, &coms, &point, &evals, &kzg_proof, transcript).unwrap();
        assert!(check2);

        let mut check3 = true;
        if proof.0.len() == 4 {
            check3 = *point * evals[1] == evals[3];
        }
        else {  
            assert_eq!(proof.0.len(), 3);
        }
        assert!(check3);

        Ok(check1 && check2 && check3)
    }

    // partial sumcheck verifier without ldt
    pub fn verify_no_ldt (
        v_srs: &VerifierSRS<P>,
        com: &P::G1,
        challenge_u: &P::ScalarField,
        point: &P::ScalarField,
        domain: &GeneralEvaluationDomain<P::ScalarField>,
        sum: &P::ScalarField,
        proof: &(Vec<P::ScalarField>, Vec<P::G1>, P::G1),
        transcript: &mut Transcript,
    ) -> Result<bool, Error> {
        let z_h_eval = domain.evaluate_vanishing_polynomial(*point);
        let (evals, helper_coms, kzg_proof) = proof.clone();
        assert_eq!(helper_coms.len(), proof.0.len() - 1);
        let constant_term = *point - *challenge_u;
        let left =  evals[0];
        let right = *point * evals[1] / constant_term + *sum / domain.size_as_field_element() + z_h_eval * evals[2];
        let check1 = left == right;

        // let check2_start = Instant::now();
        let mut coms = vec![*com];
        for i in 0..helper_coms.len() {
            coms.push(helper_coms[i]);
        }
        let check2 = BatchKZG::<P>::verify(&v_srs, &coms, &point, &evals, &kzg_proof, transcript).unwrap();
        assert!(check2);

        assert_eq!(proof.0.len(), 3);

        Ok(check1 && check2)
    }

    // just commit the target polynomial using kzg or batchkzg
    pub fn sumcheck_commit (
        powers: &[P::G1Affine],
        polynomial: &UnivariatePolynomial<P::ScalarField>, 
    ) -> Result<P::G1, Error> {
        let com = KZG::<P>::commit(&powers, &polynomial).unwrap();
        Ok(com)
    }

    pub fn sumcheck_prove (
        powers: &[P::G1Affine],
        polynomial: &UnivariatePolynomial<P::ScalarField>,
        com: &P::G1,
        sum: &P::ScalarField,
        domain: &GeneralEvaluationDomain<P::ScalarField>,
        transcript: &mut Transcript,
    ) -> Result<(Vec<P::ScalarField>, Vec<P::G1>, P::G1), Error> {
        let (g, h, g_prime) = Self::get_g_h_g_prime(&polynomial, &sum, &domain);
        let helper_polynomials = vec![g, h, g_prime];
        let helper_coms = BatchKZG::<P>::commit(&powers, &helper_polynomials).unwrap();

        // generate eta using fiat-shamir
        let mut slice_vector = helper_coms;
        slice_vector.push(com.clone());
        let slice: &[P::G1] = &slice_vector;
        <Transcript as ProofTranscript<P>>::append_points(transcript, b"add commitments", slice);
        let alpha = <Transcript as ProofTranscript<P>>::challenge_scalar(
            transcript, b"random_evaluate_point");

        let proof = SUMCHECK::<P>::prove(&powers, &polynomial, &helper_polynomials, &alpha, transcript).unwrap();
        Ok(proof)
    }

    pub fn sumcheck_no_ldt_prove (
        powers: &[P::G1Affine],
        polynomial: &UnivariatePolynomial<P::ScalarField>,
        com: &P::G1,
        sum: &P::ScalarField,
        domain: &GeneralEvaluationDomain<P::ScalarField>,
        transcript: &mut Transcript,
    ) -> Result<(Vec<P::ScalarField>, Vec<P::G1>, P::G1), Error> {
        <Transcript as ProofTranscript<P>>::append_point(transcript, b"add the first commitment", &com);
        let u = <Transcript as ProofTranscript<P>>::challenge_scalar(
            transcript, b"generate challenge u to eliminate ldt");
        
        let (g_u, h) = SUMCHECK::<P>::get_g_mul_u_and_h(&polynomial, &u, &sum, &domain);
        let helper_polynomials = vec![g_u, h];
        let helper_coms = BatchKZG::<P>::commit(&powers, &helper_polynomials).unwrap();

        // generate alpha using fiat-shamir
        let mut slice_vector = vec![com.clone()];
        for i in 0..helper_coms.len() {
            slice_vector.push(helper_coms[i].clone());
        }
        let slice: &[P::G1] = &slice_vector;
        <Transcript as ProofTranscript<P>>::append_points(transcript, b"add commitments", slice);
        let alpha = <Transcript as ProofTranscript<P>>::challenge_scalar(
            transcript, b"generate challenge alpha for evaluation");

        let proof = SUMCHECK::<P>::prove(&powers, &polynomial, &helper_polynomials, &alpha, transcript).unwrap();
        Ok(proof)
    }

    pub fn sumcheck_verify (
        v_srs: &VerifierSRS<P>,
        com: &P::G1,
        domain: &GeneralEvaluationDomain<P::ScalarField>,
        sum: &P::ScalarField,
        proof: &(Vec<P::ScalarField>, Vec<P::G1>, P::G1),
        transcript: &mut Transcript,
    ) -> Result<bool, Error> {
        let mut slice_vector = proof.1.clone();
        slice_vector.push(com.clone());
        let slice: &[P::G1] = &slice_vector;
        <Transcript as ProofTranscript<P>>::append_points(transcript, b"add commitments", slice);
        let alpha = <Transcript as ProofTranscript<P>>::challenge_scalar(
            transcript, b"random_evaluate_point");
        
        Ok(SUMCHECK::<P>::verify(&v_srs, &com, &alpha, &domain, &sum, &proof, transcript).unwrap())
    }

    pub fn sumcheck_no_ldt_verify (
        v_srs: &VerifierSRS<P>,
        com: &P::G1,
        domain: &GeneralEvaluationDomain<P::ScalarField>,
        sum: &P::ScalarField,
        proof: &(Vec<P::ScalarField>, Vec<P::G1>, P::G1),
        transcript: &mut Transcript,
    ) -> Result<bool, Error> {
        <Transcript as ProofTranscript<P>>::append_point(transcript, b"add the first commitment", &com);
        let u = <Transcript as ProofTranscript<P>>::challenge_scalar(transcript, b"generate challenge u to eliminate ldt");

        let helper_coms = proof.1.clone();
        let mut slice_vector = vec![com.clone()];
        for i in 0..helper_coms.len() {
            slice_vector.push(helper_coms[i].clone());
        }
        let slice: &[P::G1] = &slice_vector;
        <Transcript as ProofTranscript<P>>::append_points(transcript, b"add commitments", slice);
        let alpha = <Transcript as ProofTranscript<P>>::challenge_scalar(
            transcript, b"generate challenge alpha for evaluation");
        
        Ok(SUMCHECK::<P>::verify_no_ldt(&v_srs, &com, &u, &alpha, &domain, &sum, &proof, transcript).unwrap())
    }

}


#[cfg(test)]
mod tests{
    use ark_bls12_381::Bls12_381;
    use ark_ec::pairing::Pairing;
    use ark_poly::{univariate::DensePolynomial as UnivariatePolynomial, DenseUVPolynomial, EvaluationDomain, GeneralEvaluationDomain};
    use ark_std::rand::{rngs::StdRng, SeedableRng};
    use std::time::{Duration, Instant};
    type MyField = <Bls12_381 as Pairing>::ScalarField;
    use crate::sumcheck::SUMCHECK;
    use my_kzg::batch_kzg::BatchKZG;
    use merlin::Transcript;
    type TestSumCheck = SUMCHECK<Bls12_381>;

    #[test]
    fn trivial_sum_check_test() {
        let size: usize = 1 << 11;
        let degree: usize = (1 << 12) - 1;
        let mut rng = StdRng::seed_from_u64(0u64);
        let domain = 
            <GeneralEvaluationDomain<MyField> as EvaluationDomain<MyField>>::new(size).unwrap();
        let polynomial = UnivariatePolynomial::rand(degree, &mut rng);
        let sum = TestSumCheck::get_sum_on_domain(&polynomial, &domain);
        let (g_alpha_powers, v_srs) = BatchKZG::<Bls12_381>::setup(&mut rng, degree).unwrap();

        // Sumcheck prover
        let prover_start = Instant::now();
        let com = TestSumCheck::sumcheck_commit(&g_alpha_powers, &polynomial).unwrap();
        let mut transcript : Transcript = Transcript::new(b"Trivial sumcheck");
        let proof = TestSumCheck::sumcheck_prove(&g_alpha_powers, &polynomial, &com, &sum, &domain, &mut transcript).unwrap();
        println!("Trivial sumcheck prover time: {:?} ms", prover_start.elapsed().as_millis());

        // Sumcheck proof size
        let proof_size = TestSumCheck::get_proof_size(&proof);
        println!("Trivial sumcheck proof size: {:?} bytes", proof_size);

        // Sumcheck verifier
        std::thread::sleep(Duration::from_millis(5000));
        let mut transcript : Transcript = Transcript::new(b"Trivial sumcheck");
        let verify_start = Instant::now();
        let is_valid = 
            TestSumCheck::sumcheck_verify(&v_srs, &com, &domain, &sum, &proof, &mut transcript).unwrap();
        assert!(is_valid);
        let verify_time = verify_start.elapsed().as_millis();
        println!("Trivial sumcheck verifier time: {:?} ms", verify_time);
    }

    #[test]
    fn sumcheck_no_ldt_test() {
        let size: usize = 1 << 11;
        let degree: usize = (1 << 12) - 1;
        let mut rng = StdRng::seed_from_u64(0u64);
        let domain = 
            <GeneralEvaluationDomain<MyField> as EvaluationDomain<MyField>>::new(size).unwrap();
        let polynomial = UnivariatePolynomial::rand(degree, &mut rng);
        let sum = TestSumCheck::get_sum_on_domain(&polynomial, &domain);
        let (g_alpha_powers, v_srs) = BatchKZG::<Bls12_381>::setup(&mut rng, degree).unwrap();

        // (x-u)f(x) = x*g(x) + sum/|domain| (x-u) + Z_H(x)h(x)(x-u)
        // Sumcheck prover
        let prover_start = Instant::now();
        let mut transcript: Transcript = Transcript::new(b"No_ldt sumcheck");
        let com = SUMCHECK::<Bls12_381>::sumcheck_commit(&g_alpha_powers, &polynomial).unwrap();

        let proof = TestSumCheck::sumcheck_no_ldt_prove(&g_alpha_powers, &polynomial, &com, &sum, &domain, &mut transcript).unwrap();
        println!("No_ldt sumcheck prover time: {:?} ms", prover_start.elapsed().as_millis());

        // Sumcheck proof size
        let proof_size = TestSumCheck::get_proof_size(&proof);
        println!("No_ldt sumcheck proof size: {:?} bytes", proof_size);

        // Sumcheck verifier
        std::thread::sleep(Duration::from_millis(5000));
        let verify_start = Instant::now();
        for _ in 0..50 {
            let mut transcript: Transcript = Transcript::new(b"No_ldt sumcheck");
            let is_valid = 
                TestSumCheck::sumcheck_no_ldt_verify(&v_srs, &com, &domain, &sum, &proof, &mut transcript).unwrap();
            assert!(is_valid);
        }
        let verify_time = verify_start.elapsed().as_millis() / 50;
        println!("No_ldt sumcheck verifier time: {:?} ms", verify_time);
    }

}