use ark_poly::{
    univariate::DensePolynomial as UnivariatePolynomial, DenseUVPolynomial, EvaluationDomain,
    GeneralEvaluationDomain, Polynomial
};
use std::marker::PhantomData;
use ark_ec::pairing::Pairing;
use my_kzg::{batch_kzg::BatchKZG, transcript::ProofTranscript, trivial_kzg::{
    VerifierSRS
    // , KZG
}};
use crate::Error;
use merlin::Transcript;
use crate::ipa::IPA;
// use ark_ff::{Zero, One, Field};
// use de_network::{DeMultiNet as Net, DeNet, DeSerNet};

pub struct DeIPA<P: Pairing> {
    _pairing: PhantomData<P>,
}

pub struct SubWitnessPolys<P: Pairing> {
    pub poly_w: UnivariatePolynomial<P::ScalarField>,
    pub poly_a: UnivariatePolynomial<P::ScalarField>,
    pub poly_b: UnivariatePolynomial<P::ScalarField>,
    pub poly_c: UnivariatePolynomial<P::ScalarField>,
}

pub struct SubPublicPolys<P: Pairing> {
    pub poly_pa: UnivariatePolynomial<P::ScalarField>,
    pub poly_pb: UnivariatePolynomial<P::ScalarField>,
    pub poly_pc: UnivariatePolynomial<P::ScalarField>,
}

// Simple implementation of univariate sum-check via KZG
impl<P: Pairing> DeIPA<P> {

    // pub fn de_r1cs_prove (
    //     // id can be zero
    //     sub_prover_id: usize,
    //     powers: &Vec<Vec<P::G1Affine>>,
    //     witness_polynomials: &SubWitnessPolys<P>,
    //     public_polynomials: &SubPublicPolys<P>,
    //     r: &P::ScalarField,
    //     domain: &GeneralEvaluationDomain<P::ScalarField>,
    //     transcript: &mut Transcript,
    //     challenge_v: &P::ScalarField,
    //     challenge_u1: &P::ScalarField,
    // ) -> Option<P::G1> {

    //     // sub_power and m
    //     let sub_power = powers[sub_prover_id].clone();
    //     let m = sub_power.len();

    //     // R_i(X) = X^{i-1} and evals R_i(r^{m})
    //     let mut coeffs_r_i = vec![P::ScalarField::zero(); sub_prover_id];
    //     coeffs_r_i.insert(0, P::ScalarField::one());
    //     let polynomial_r_i = UnivariatePolynomial::from_coefficients_vec(coeffs_r_i);
    //     let eval_r_i = polynomial_r_i.evaluate(&(r.pow([m as u64])));

    //     // f_a(rX)
    //     let mut coeffs_fa = witness_polynomials.poly_a.coeffs.to_vec();
    //     let mut linear_factor = P::ScalarField::one();
    //     for i in 0..coeffs_fa.len() {
    //         coeffs_fa[i] *= linear_factor;
    //         linear_factor *= r;
    //     }
    //     let poly_fa_rx = UnivariatePolynomial::from_coefficients_vec(coeffs_fa);

    //     // f1 - f4
    //     let polynomial_f1 = &public_polynomials.poly_pa * &witness_polynomials.poly_w + UnivariatePolynomial::from_coefficients_vec(vec![-eval_r_i * witness_polynomials.poly_a.evaluate(r)]);
    //     let polynomial_f2 = &public_polynomials.poly_pb * &witness_polynomials.poly_w + UnivariatePolynomial::from_coefficients_vec(vec![-eval_r_i * witness_polynomials.poly_b.evaluate(&r.clone().inverse().unwrap())]);
    //     let polynomial_f3 = &public_polynomials.poly_pa * &witness_polynomials.poly_w + UnivariatePolynomial::from_coefficients_vec(vec![-eval_r_i * witness_polynomials.poly_c.evaluate(r)]);
    //     let polynomial_f4 = &(&poly_fa_rx * &witness_polynomials.poly_b) * eval_r_i + UnivariatePolynomial::from_coefficients_vec(vec![-eval_r_i * witness_polynomials.poly_c.evaluate(r)]);

    //     // target polynomial, rlc of f1-f4
    //     let mut polynomial_target = &polynomial_f1 + &(&polynomial_f2 * *challenge_v);
    //     polynomial_target += (*challenge_v * challenge_v, &polynomial_f3);
    //     polynomial_target += (challenge_v.pow([3 as u64]), &polynomial_f4);

    //     // get g_u and h
    //     let (poly_g1, poly_h1) = IPA::<P>::get_g_mul_u_and_h(&polynomial_target, &challenge_u1, &domain);
    //     let com_g1 = KZG::<P>::commit(&sub_power, &poly_g1).unwrap();
    //     let com_h1 = KZG::<P>::commit(&sub_power, &poly_h1).unwrap();

    //     // send com of g1 and h1 to P0
    //     let com_g1_h1_slice = Net::send_to_master(&(com_g1, com_h1));
    //     let com_g1_h1 = if Net::am_master() {
    //         com_g1_h1_slice.unwrap().iter().fold((P::G1::zero(), P::G1::zero()), |(acc1, acc2), &(a, b)| {
    //             (acc1 + a, acc2 + b)
    //         })
    //     } else {
    //         (P::G1::zero(), P::G1::zero())
    //     };
    //     let (com_g1, com_h1) = com_g1_h1;

    //     // generate new challenges alpha and u2
    //     let (alpha, u2) = if Net::am_master() {
    //         let slice: &[P::G1] = &vec![com_g1, com_h1];
    //         <Transcript as ProofTranscript<P>>::append_points(transcript, b"alpha_and_u2", slice);
    //         let alpha = <Transcript as ProofTranscript<P>>::challenge_scalar(transcript, b"random_evaluation_for_x");
    //         let u2 = <Transcript as ProofTranscript<P>>::challenge_scalar(transcript, b"random_ldt_padding");
    //         Net::recv_from_master(Some(vec![(alpha, u2); Net::n_parties()]));
    //         (alpha, u2)
    //     } else {
    //         Net::recv_from_master(None)
    //     };

    //     // evaluate and send polynomial evaluations on alpha
    //     let eval_pa_alpha = public_polynomials.poly_pa.evaluate(&alpha);
    //     let eval_pb_alpha = public_polynomials.poly_pb.evaluate(&alpha);
    //     let eval_pc_alpha = public_polynomials.poly_pc.evaluate(&alpha);
    //     let eval_w_alpha = witness_polynomials.poly_w.evaluate(&alpha);
    //     let eval_a_alph = witness_polynomials.poly_w.evaluate(&alpha);

    //     Some(P::G1::zero())
    // }

    pub fn sumcheck_prove (
        powers: &[P::G1Affine],
        polynomial_left: &UnivariatePolynomial<P::ScalarField>,
        polynomial_right: &UnivariatePolynomial<P::ScalarField>,
        polynomial_target: &UnivariatePolynomial<P::ScalarField>,
        com_left: &P::G1,
        com_right: &P::G1,
        domain: &GeneralEvaluationDomain<P::ScalarField>,
        transcript: &mut Transcript,
    ) -> Result<(Vec<P::ScalarField>, Vec<P::G1>, P::G1), Error> {
        
        let mut slice_vector = vec![com_left.clone(), com_right.clone()];
        let slice: &[P::G1] = &slice_vector;
        <Transcript as ProofTranscript<P>>::append_points(transcript, b"add the first commitment", slice);
        let u = <Transcript as ProofTranscript<P>>::challenge_scalar(
            transcript, b"generate challenge u to eliminate ldt");
        
        let (g_u, h) = IPA::<P>::get_g_mul_u_and_h(&polynomial_target, &u, &domain);
        // assert_eq!(g_u.degree(), domain.size() - 1);
        let helper_polynomials = vec![g_u, h];
        let helper_coms = BatchKZG::<P>::commit(&powers, &helper_polynomials).unwrap();

        // generate alpha using fiat-shamir
        for i in 0..helper_coms.len() {
            slice_vector.push(helper_coms[i]);
        }
        let slice: &[P::G1] = &slice_vector;
        <Transcript as ProofTranscript<P>>::append_points(transcript, b"add commitments", slice);
        let alpha = <Transcript as ProofTranscript<P>>::challenge_scalar(
            transcript, b"generate challenge alpha for evaluation");

        let mut evals = vec![polynomial_left.evaluate(&alpha), polynomial_right.evaluate(&alpha)];
        let mut polynomials = vec![polynomial_left.clone(), polynomial_right.clone()];
        for i in 0..helper_polynomials.len() {
            evals.push(helper_polynomials[i].evaluate(&alpha));
            polynomials.push(helper_polynomials[i].clone());
        }

        // evaluations of f1,f2,g_u,h or f1,f2,g,h,g_prime
        let proof_1 = evals;
        // commitments of g_u,h or g,h,g_prime
        let proof_2 = BatchKZG::<P>::commit(&powers, &helper_polynomials).unwrap();
        // proof of openings of f1,f2,g_u,h or f1,f2,g,h,g_prime
        let challenge = <Transcript as ProofTranscript<P>>::challenge_scalar(
            transcript, b"batch_kzg_rlc_challenge");
        let proof_3 = BatchKZG::<P>::open(&powers, &polynomials, &alpha, &challenge).unwrap();
        Ok((proof_1, proof_2, proof_3))
    }

    pub fn sumcheck_verify (
        v_srs: &VerifierSRS<P>,
        com_left: &P::G1,
        com_right: &P::G1,
        domain: &GeneralEvaluationDomain<P::ScalarField>,
        sum: &P::ScalarField,
        proof: &(Vec<P::ScalarField>, Vec<P::G1>, P::G1),
        transcript: &mut Transcript,
    ) -> Result<bool, Error> {
        let mut slice_vector = vec![com_left.clone(), com_right.clone()];
        let slice: &[P::G1] = &slice_vector;
        <Transcript as ProofTranscript<P>>::append_points(transcript, b"add the first commitment", slice);
        let u = <Transcript as ProofTranscript<P>>::challenge_scalar(transcript, b"generate challenge u to eliminate ldt");

        let helper_coms = proof.1.clone();
        for i in 0..helper_coms.len() {
            slice_vector.push(helper_coms[i]);
        }
        let slice: &[P::G1] = &slice_vector;
        <Transcript as ProofTranscript<P>>::append_points(transcript, b"add commitments", slice);
        let alpha = <Transcript as ProofTranscript<P>>::challenge_scalar(
            transcript, b"generate challenge alpha for evaluation");
        
        let z_h_eval = domain.evaluate_vanishing_polynomial(alpha);
        let (evals, helper_coms, kzg_proof) = proof.clone();
        assert_eq!(helper_coms.len(), proof.0.len() - 2);
        let constant_term = alpha - u;
        let left =  evals[0] * evals[1];
        let right = alpha * evals[2] / constant_term + *sum / domain.size_as_field_element() + z_h_eval * evals[3];
        let check1 = left == right;
        assert!(check1);

        let mut coms = vec![*com_left, *com_right];
        for i in 0..helper_coms.len() {
            coms.push(helper_coms[i]);
        }

        let challenge = <Transcript as ProofTranscript<P>>::challenge_scalar(
            transcript, b"batch_kzg_rlc_challenge");
        let check2 = BatchKZG::<P>::verify(&v_srs, &coms, &alpha, &evals, &kzg_proof, &challenge).unwrap();
        assert!(check2);
        assert_eq!(proof.0.len(), 4);
        
        Ok(check1 && check2)
    }

    pub fn ipa_commit_and_prove (
        powers: &[P::G1Affine],
        vector_left: &Vec<P::ScalarField>,
        vector_right: &Vec<P::ScalarField>,
        domain: &GeneralEvaluationDomain<P::ScalarField>,
        transcript: &mut Transcript,
    ) -> Result<((P::G1, P::G1), (Vec<P::ScalarField>, Vec<P::G1>, P::G1)), Error> {
        assert_eq!(vector_left.len(), vector_right.len());
        assert_eq!(domain.size(), vector_left.len());

        // generate the polynomials f1(x) and f2(x)
        let coeffs_left = vector_left.clone();
        let polynomial_left = UnivariatePolynomial::from_coefficients_vec(coeffs_left);
        let mut coeffs_right = vec![vector_right[0].clone()];
        let mut rest = vector_right.clone().split_off(1);
        rest.reverse();
        coeffs_right.extend(rest);
        let polynomial_right = UnivariatePolynomial::from_coefficients_vec(coeffs_right);

        // generate the commitment of f1 and f2
        let (com_left, com_right) = IPA::<P>::ipa_commit(&powers, &polynomial_left, &polynomial_right).unwrap();

        // compute the target polynomial
        let ifft_domain = <GeneralEvaluationDomain<P::ScalarField> as EvaluationDomain<P::ScalarField>>::new(domain.size() * 2).unwrap();
        let evals_left = polynomial_left.clone().evaluate_over_domain(ifft_domain);
        let evals_right = polynomial_right.clone().evaluate_over_domain(ifft_domain);
        let evals_target = &evals_left * &evals_right;
        let polynomial_target = evals_target.interpolate();

        // generate the proof
        let proof = DeIPA::<P>::sumcheck_prove(&powers, &polynomial_left, &polynomial_right, &polynomial_target, &com_left, &com_right, &domain, transcript).unwrap();

        Ok(((com_left, com_right), proof))
    }

    pub fn ipa_verify (
        v_srs: &VerifierSRS<P>,
        domain: &GeneralEvaluationDomain<P::ScalarField>,
        inner_product: &P::ScalarField,
        proof: &((P::G1, P::G1), (Vec<P::ScalarField>, Vec<P::G1>, P::G1)),
        transcript: &mut Transcript,
    ) -> Result<bool, Error> {
        let (com_left, com_right) = proof.0;
        let sum = *inner_product * domain.size_as_field_element();
        Ok(DeIPA::<P>::sumcheck_verify(&v_srs, &com_left, &com_right, &domain, &sum, &proof.1, transcript).unwrap())
    }

    pub fn get_proof_size (
        proof: &((P::G1, P::G1), (Vec<P::ScalarField>, Vec<P::G1>, P::G1)),
    ) -> usize {
        if proof.1.0.len() == 4 {
            (proof.1.1.len() + 3) * size_of_val(&proof.1.1[0]) +  proof.1.0.len() * size_of_val(&proof.1.0[0])
        }
        else {
            // -1 because g_prime(alpha) can be computed from g(alpha)
            (proof.1.1.len() + 3) * size_of_val(&proof.1.1[0]) +  (proof.1.0.len() - 1) * size_of_val(&proof.1.0[0])
        }
    }

}


#[cfg(test)]
mod tests{
    use ark_bls12_381::Bls12_381;
    use ark_ec::pairing::Pairing;
    use ark_poly::{
        univariate::DensePolynomial as UnivariatePolynomial, DenseUVPolynomial, EvaluationDomain, GeneralEvaluationDomain, Polynomial};
    use ark_std::rand::{rngs::StdRng, SeedableRng};
    use std::time::{Instant, Duration};
    type MyField = <Bls12_381 as Pairing>::ScalarField;
    use crate::{de_ipa::DeIPA, ipa::IPA};
    // use crate::sumcheck::SUMCHECK;
    use my_kzg::{batch_kzg::BatchKZG, biv_trivial_kzg::BivariatePolynomial};
    use merlin::Transcript;
    use ark_ff::{
        UniformRand,
        One,
        Zero
        };
    // use crate::ipa::IPA;
    const BIVARIATE_X_DEGREE: usize = (1 << 3) - 1;
    const BIVARIATE_Y_DEGREE: usize = (1 << 2) - 1;

    // Test of Lemma 4
    #[test]
    fn bivariate_sum_test() {
        let size_x = BIVARIATE_X_DEGREE + 1;
        let size_y = BIVARIATE_Y_DEGREE + 1;
        let mut rng = StdRng::seed_from_u64(0u64);
        let domain_y = 
            <GeneralEvaluationDomain<MyField> as EvaluationDomain<MyField>>::new(size_y).unwrap();
        let domain_x = 
            <GeneralEvaluationDomain<MyField> as EvaluationDomain<MyField>>::new(size_x).unwrap();
        
        // f1
        let mut x_polynomials_1 = Vec::new();
        for _ in 0..BIVARIATE_Y_DEGREE + 1 {
            let mut x_polynomial_coeffs = vec![];
            for _ in 0..BIVARIATE_X_DEGREE + 1 {
                x_polynomial_coeffs.push(MyField::rand(&mut rng));
            }
            x_polynomials_1.push(UnivariatePolynomial::from_coefficients_slice(
                &x_polynomial_coeffs,
            ));
        }
        let bivariate_polynomial_1 = BivariatePolynomial{ x_polynomials: x_polynomials_1.clone() };

        // f2
        let mut x_polynomials_2 = Vec::new();
        for _ in 0..BIVARIATE_Y_DEGREE + 1 {
            let mut x_polynomial_coeffs = vec![];
            for _ in 0..BIVARIATE_X_DEGREE + 1 {
                x_polynomial_coeffs.push(MyField::rand(&mut rng));
            }
            x_polynomials_2.push(UnivariatePolynomial::from_coefficients_slice(
                &x_polynomial_coeffs,
            ));
        }
        let bivariate_polynomial_2 = BivariatePolynomial{ x_polynomials: x_polynomials_2.clone() };

        // f3
        let mut x_polynomials_3 = Vec::new();
        for _ in 0..BIVARIATE_Y_DEGREE + 1 {
            let mut x_polynomial_coeffs = vec![];
            for _ in 0..BIVARIATE_X_DEGREE + 1 {
                x_polynomial_coeffs.push(MyField::rand(&mut rng));
            }
            x_polynomials_3.push(UnivariatePolynomial::from_coefficients_slice(
                &x_polynomial_coeffs,
            ));
        }
        let bivariate_polynomial_3 = BivariatePolynomial{ x_polynomials: x_polynomials_3.clone() };
        assert!(x_polynomials_1.len() == x_polynomials_2.len());
        assert!(x_polynomials_2.len() == x_polynomials_3.len());

        let alpha = MyField::rand(&mut rng);
        let evals_3: Vec<MyField> = x_polynomials_3.iter().map(|polynomial| polynomial.evaluate(&alpha)).collect();
        let mut left_polynomial = UnivariatePolynomial::from_coefficients_vec(vec![MyField::zero()]);
        for i in 0..x_polynomials_1.len() {
            let mut current_polynomial = &x_polynomials_1[i] * &x_polynomials_2[i];
            current_polynomial = &current_polynomial * evals_3[i];
            left_polynomial += &current_polynomial;
        }

        let omega = domain_y.group_gen();
        let mut point = MyField::one();
        let mut right_polynomial = UnivariatePolynomial::from_coefficients_vec(vec![MyField::zero()]);
        for _ in 0..bivariate_polynomial_1.x_polynomials.len() {
            let mut current_polynomial: UnivariatePolynomial<MyField> = bivariate_polynomial_1.evaluate_at_y_lagrange(&point, &domain_y);
            current_polynomial = &current_polynomial * &bivariate_polynomial_2.evaluate_at_y_lagrange(&point, &domain_y);
            current_polynomial = &current_polynomial * bivariate_polynomial_3.evaluate_lagrange(&(alpha, point), &domain_y);
            right_polynomial += &current_polynomial;
            point *= omega;
        }

        assert_eq!(left_polynomial, right_polynomial);

        let left_sum = IPA::<Bls12_381>::get_sum_on_domain(&left_polynomial, &domain_x);
        let right_sum = IPA::<Bls12_381>::get_sum_on_domain(&right_polynomial, &domain_x);
        assert_eq!(left_sum, right_sum);

    }

    #[test]
    fn ipa_improved_test() {
        let degree: usize = (1 << 12) - 1;
        let size = degree + 1;
        let mut rng = StdRng::seed_from_u64(0u64);
        let domain = 
            <GeneralEvaluationDomain<MyField> as EvaluationDomain<MyField>>::new(size).unwrap();
        let mut vector_left = Vec::new();
        let mut vector_right = Vec::new();
        for _ in 0..size {
            vector_left.push(MyField::rand(&mut rng));
            vector_right.push(MyField::rand(&mut rng));
        }
        let inner_product = vector_left.iter().zip(vector_right.iter()).map(|(left, right)| left * right).sum();
        let (g_alpha_powers, v_srs) = BatchKZG::<Bls12_381>::setup(&mut rng, degree).unwrap();

        // Improved IPA_from_sumcheck prover
        let prover_start = Instant::now();
        let mut transcript : Transcript = Transcript::new(b"Trivial IPA from sumcheck");
        let proof = DeIPA::<Bls12_381>::ipa_commit_and_prove(&g_alpha_powers, &vector_left, &vector_right, &domain, &mut transcript).unwrap();
        println!("Improved IPA prover time: {:?} ms", prover_start.elapsed().as_millis());

        // Improved IPA_from_sumcheck proof size
        let proof_size = DeIPA::<Bls12_381>::get_proof_size(&proof);
        println!("Improved IPA proof size: {:?} bytes", proof_size);

        // Improved IPA_from_sumcheck verifier
        std::thread::sleep(Duration::from_millis(5000));
        let verify_start = Instant::now();
        let mut transcript : Transcript = Transcript::new(b"Trivial IPA from sumcheck");
        let is_valid = 
            DeIPA::<Bls12_381>::ipa_verify(&v_srs, &domain, &inner_product, &proof, &mut transcript).unwrap();
        assert!(is_valid);
        let verify_time = verify_start.elapsed().as_millis();
        println!("Improved IPA verifier time: {:?} ms", verify_time);
    }
}