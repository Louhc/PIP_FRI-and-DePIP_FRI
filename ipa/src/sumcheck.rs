use ark_ff::{Zero, One};
use ark_poly::{
    univariate::DensePolynomial as UnivariatePolynomial, DenseUVPolynomial, EvaluationDomain,
    GeneralEvaluationDomain, Polynomial
};
use std::marker::PhantomData;
use ark_ec::pairing::Pairing;
use my_kzg::batch_kzg::{BatchKZG, VerifierSRS};
use crate::Error;
use merlin::Transcript;


pub struct SUMCHECK<P: Pairing> {
    _pairing: PhantomData<P>,
}

// Simple implementation of univariate sum-check via KZG
// The idea is postpone opening commitments until the last
impl<P: Pairing> SUMCHECK<P> {
    // commit f(x)
    // list it lonely as in proof systems the commitment is usually generated prescribedly
    // pub fn commit (
    //     powers: &[P::G1Affine],
    //     polynomial: &UnivariatePolynomial<P::ScalarField>,
    // ) -> Result<P::G1, Error> {
    //     Ok(KZG::<P>::commit(&powers, &polynomial).unwrap())
    // }

    pub fn get_sum_on_domain (
        polynomial: &UnivariatePolynomial<P::ScalarField>,
        domain: &GeneralEvaluationDomain<P::ScalarField>,
    ) -> P::ScalarField {
        let evals = polynomial.clone().evaluate_over_domain(domain.clone());
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
        let (h, reminder_polynomial) = polynomial.clone().divide_by_vanishing_poly(domain.clone()).unwrap();
        let constant_term = sum.clone() / domain.size_as_field_element();
        let g_prime = reminder_polynomial + UnivariatePolynomial::from_coefficients_vec(vec![-constant_term]);
        let g = &g_prime / &UnivariatePolynomial::from_coefficients_vec(vec![P::ScalarField::zero(), P::ScalarField::one()]);

        (g, h, g_prime)
    }

    pub fn get_g_mul_u_and_h (
        polynomial: &UnivariatePolynomial<P::ScalarField>,
        challenge: &P::ScalarField,
        sum: &P::ScalarField,
        domain: &GeneralEvaluationDomain<P::ScalarField>,
    ) -> (UnivariatePolynomial<P::ScalarField>, UnivariatePolynomial<P::ScalarField>) {
        let u = challenge.clone();
        let (h, reminder_polynomial) = polynomial.clone().divide_by_vanishing_poly(domain.clone()).unwrap();
        let constant_term = sum.clone() / domain.size_as_field_element();
        let g_prime = reminder_polynomial + UnivariatePolynomial::from_coefficients_vec(vec![-constant_term]);
        let g = &g_prime / &UnivariatePolynomial::from_coefficients_vec(vec![P::ScalarField::zero(), P::ScalarField::one()]);
        let g_u = &g * &UnivariatePolynomial::from_coefficients_vec(vec![-u, P::ScalarField::one()]);

        (g_u, h)
    }

     // generate the evaluations and KZG proofs
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
    ) -> Result<(Vec<P::ScalarField>, P::G1), Error> {
        let mut evals = vec![polynomial.evaluate(&point)];
        let mut polynomials = vec![polynomial.clone()];
        for i in 0..helper_polynomials.len() {
            evals.push(helper_polynomials[i].evaluate(&point));
            polynomials.push(helper_polynomials[i].clone());
        }

        let proof_1 = evals;
        let proof_2 = BatchKZG::<P>::open(&powers, &polynomials, &point, &mut transcript.clone()).unwrap();
        Ok((proof_1, proof_2))
    }

    pub fn get_proof_size (
        proof: &(Vec<P::ScalarField>, P::G1),
    ) -> usize {
        if proof.0.len() == 3 {
            (proof.0.len() + 1) * size_of_val(&proof.1) +  proof.0.len() * size_of_val(&proof.0[0])
        }
        else {
            (proof.0.len() + 1) * size_of_val(&proof.1) +  (proof.0.len() - 1) * size_of_val(&proof.0[0])
        }
    }

    pub fn verify (
        v_srs: &VerifierSRS<P>,
        com: &P::G1,
        helper_coms: &Vec<P::G1>,
        point: &P::ScalarField,
        domain: &GeneralEvaluationDomain<P::ScalarField>,
        sum: &P::ScalarField,
        proof: &(Vec<P::ScalarField>, P::G1),
        transcript: &mut Transcript,
    ) -> Result<bool, Error> {
        assert_eq!(helper_coms.len(), proof.0.len() - 1);


        let z_h_eval = domain.evaluate_vanishing_polynomial(point.clone());
        let (evals, kzg_proof) = proof.clone();
        let check1 = evals[0] == point.clone() * evals[1] + sum.clone() / domain.size_as_field_element() + z_h_eval * evals[2];
        assert!(check1);

        // let check2_start = Instant::now();
        let mut coms = vec![com.clone()];
        for i in 0..helper_coms.len() {
            coms.push(helper_coms[i]);
        }
        let check2 = BatchKZG::<P>::verify(&v_srs, &coms, &point, &evals, &kzg_proof, &mut transcript.clone()).unwrap();
        assert!(check2);

        let mut check3 = true;
        if proof.0.len() == 4 {
            check3 = point.clone() * evals[1] == evals[3];
        }
        else {  
            assert_eq!(proof.0.len(), 3);
        }
        assert!(check3);

        Ok(check1 && check2 && check3)
    }

    pub fn verify_no_ldt (
        v_srs: &VerifierSRS<P>,
        com: &P::G1,
        helper_coms: &Vec<P::G1>,
        challenge_u: &P::ScalarField,
        point: &P::ScalarField,
        domain: &GeneralEvaluationDomain<P::ScalarField>,
        sum: &P::ScalarField,
        proof: &(Vec<P::ScalarField>, P::G1),
        transcript: &mut Transcript,
    ) -> Result<bool, Error> {
        assert_eq!(helper_coms.len(), proof.0.len() - 1);

        let z_h_eval = domain.evaluate_vanishing_polynomial(point.clone());
        let (evals, kzg_proof) = proof.clone();
        let constant_term = point.clone() - challenge_u.clone();
        let left =  evals[0];
        let right = point.clone() * evals[1] / constant_term + sum.clone() / domain.size_as_field_element() + z_h_eval * evals[2];
        let check1 = left == right;

        // let check2_start = Instant::now();
        let mut coms = vec![com.clone()];
        for i in 0..helper_coms.len() {
            coms.push(helper_coms[i]);
        }
        let check2 = BatchKZG::<P>::verify(&v_srs, &coms, &point, &evals, &kzg_proof, &mut transcript.clone()).unwrap();
        assert!(check2);

        assert_eq!(proof.0.len(), 3);

        Ok(check1 && check2)
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
    use my_kzg::{
        batch_kzg::BatchKZG,
        trivial_kzg::KZG,
        transcript::ProofTranscript,
    };
    use merlin::Transcript;

    type TestSumCheck = SUMCHECK<Bls12_381>;

    #[test]
    fn trivial_sum_check_test() {
        let size: usize = 1 << 11;
        let degree: usize = 1 << 12 - 1;
        let mut rng = StdRng::seed_from_u64(0u64);
        let domain = 
            <GeneralEvaluationDomain<MyField> as EvaluationDomain<MyField>>::new(size).unwrap();
        let polynomial = UnivariatePolynomial::rand(degree, &mut rng);
        let sum = TestSumCheck::get_sum_on_domain(&polynomial, &domain);
        let (g_alpha_powers, v_srs) = BatchKZG::<Bls12_381>::setup(&mut rng, degree).unwrap();

        // Sumcheck prover
        let prover_start = Instant::now();
        let mut transcript : Transcript = Transcript::new(b"Trivial sumcheck");
        let com = KZG::<Bls12_381>::commit(&g_alpha_powers, &polynomial).unwrap();

        let (g, h, g_prime) = TestSumCheck::get_g_h_g_prime(&polynomial, &sum, &domain);
        let helper_polynomials = vec![g, h, g_prime];
        let helper_coms = BatchKZG::<Bls12_381>::commit(&g_alpha_powers, &helper_polynomials).unwrap();

        // generate eta using fiat-shamir
        let mut slice_vector = helper_coms.clone();
        slice_vector.push(com.clone());
        let slice: &[<Bls12_381 as Pairing>::G1] = &slice_vector;
        <Transcript as ProofTranscript<Bls12_381>>::append_points(&mut transcript, b"add commitments", slice);
        let alpha = <Transcript as ProofTranscript<Bls12_381>>::challenge_scalar(
            &mut transcript, b"random_evaluate_point");

        let proof = TestSumCheck::prove(&g_alpha_powers, &polynomial, &helper_polynomials, &alpha, &mut transcript).unwrap();
        println!("Trivial sumcheck prover time: {:?} ms", prover_start.elapsed().as_millis());

        // Sumcheck proof size
        let proof_size = TestSumCheck::get_proof_size(&proof);
        println!("Trivial sumcheck proof size: {:?} bytes", proof_size);

        // Sumcheck verifier
        std::thread::sleep(Duration::from_millis(5000));
        let mut transcript : Transcript = Transcript::new(b"Trivial sumcheck");

        let verify_start = Instant::now();
        let mut slice_vector = helper_coms.clone();
        slice_vector.push(com.clone());
        let slice: &[<Bls12_381 as Pairing>::G1] = &slice_vector;
        <Transcript as ProofTranscript<Bls12_381>>::append_points(&mut transcript, b"add commitments", slice);
        let alpha = <Transcript as ProofTranscript<Bls12_381>>::challenge_scalar(
            &mut transcript, b"random_evaluate_point");
        let is_valid =
            TestSumCheck::verify(&v_srs, &com, &helper_coms, &alpha, &domain, &sum, &proof, &mut transcript).unwrap();
        assert!(is_valid);

        let verify_time = verify_start.elapsed().as_millis();
        println!("Trivial sumcheck verifier time: {:?} ms", verify_time);
    }

    #[test]
    fn sumcheck_no_ldt_test() {
        let size: usize = 1 << 11;
        let degree: usize = 1 << 12 - 1;
        let mut rng = StdRng::seed_from_u64(0u64);
        let domain = 
            <GeneralEvaluationDomain<MyField> as EvaluationDomain<MyField>>::new(size).unwrap();
        let polynomial = UnivariatePolynomial::rand(degree, &mut rng);
        let sum = TestSumCheck::get_sum_on_domain(&polynomial, &domain);
        let (g_alpha_powers, v_srs) = BatchKZG::<Bls12_381>::setup(&mut rng, degree).unwrap();

        // (x-u)f(x) = x*g(x) + sum/|domain| (x-u) + Z_H(x)h(x)(x-u)
        // Sumcheck prover
        let prover_start = Instant::now();
        let mut transcript : Transcript = Transcript::new(b"No_ldt sumcheck");
        let com = KZG::<Bls12_381>::commit(&g_alpha_powers, &polynomial).unwrap();

        <Transcript as ProofTranscript<Bls12_381>>::append_point(&mut transcript, b"add the first commitment", &com);
        let u = <Transcript as ProofTranscript<Bls12_381>>::challenge_scalar(
            &mut transcript, b"generate challenge u to eliminate ldt");
        
        let (g_u, h) = TestSumCheck::get_g_mul_u_and_h(&polynomial, &u, &sum, &domain);
        let helper_polynomials = vec![g_u.clone(), h.clone()];
        let helper_coms = BatchKZG::<Bls12_381>::commit(&g_alpha_powers, &helper_polynomials).unwrap();

        // generate alpha using fiat-shamir
        let mut slice_vector = helper_coms.clone();
        slice_vector.push(com.clone());
        let slice: &[<Bls12_381 as Pairing>::G1] = &slice_vector;
        <Transcript as ProofTranscript<Bls12_381>>::append_points(&mut transcript, b"add commitments", slice);
        let alpha = <Transcript as ProofTranscript<Bls12_381>>::challenge_scalar(
            &mut transcript, b"generate challenge alpha for evaluation");

        let proof = TestSumCheck::prove(&g_alpha_powers, &polynomial, &helper_polynomials, &alpha, &mut transcript).unwrap();
        println!("No_ldt sumcheck prover time: {:?} ms", prover_start.elapsed().as_millis());

        // Sumcheck proof size
        let proof_size = TestSumCheck::get_proof_size(&proof);
        println!("No_ldt sumcheck proof size: {:?} bytes", proof_size);

        // Sumcheck verifier
        std::thread::sleep(Duration::from_millis(5000));
        let verify_start = Instant::now();

        let mut transcript : Transcript = Transcript::new(b"No_ldt sumcheck");
        <Transcript as ProofTranscript<Bls12_381>>::append_point(&mut transcript, b"add the first commitment", &com);
        let u = <Transcript as ProofTranscript<Bls12_381>>::challenge_scalar(
            &mut transcript, b"generate challenge u to eliminate ldt");

        let mut slice_vector = helper_coms.clone();
        slice_vector.push(com.clone());
        let slice: &[<Bls12_381 as Pairing>::G1] = &slice_vector;
        <Transcript as ProofTranscript<Bls12_381>>::append_points(&mut transcript, b"add commitments", slice);
        let alpha = <Transcript as ProofTranscript<Bls12_381>>::challenge_scalar(
            &mut transcript, b"generate challenge alpha for evaluation");

        let is_valid =
            TestSumCheck::verify_no_ldt(&v_srs, &com, &helper_coms, &u, &alpha, &domain, &sum, &proof, &mut transcript).unwrap();
        assert!(is_valid);

        let verify_time = verify_start.elapsed().as_millis();
        println!("No_ldt sumcheck verifier time: {:?} ms", verify_time);
    }
}