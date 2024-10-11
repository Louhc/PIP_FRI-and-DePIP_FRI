use ark_poly::{univariate::DensePolynomial as UnivariatePolynomial, DenseUVPolynomial, EvaluationDomain, Evaluations, GeneralEvaluationDomain, Polynomial};
use std::marker::PhantomData;
use ark_ec::pairing::Pairing;
use my_kzg::{batch_kzg::BatchKZG, helper::linear_combination_field, transcript::ProofTranscript, trivial_kzg::{VerifierSRS, KZG}};
use crate::Error;
use merlin::Transcript;
use crate::{ipa::IPA, helper::{R1CSPublicPolys, R1CSWitnessPolys}};
use ark_ff::{Zero, One, Field};
use de_network::{DeMultiNet as Net, DeNet, DeSerNet};

pub struct DeIPA<P: Pairing> {
    _pairing: PhantomData<P>,
}


impl<P: Pairing> DeIPA<P> {

    pub fn de_r1cs_prove (
        // id can be zero
        sub_prover_id: usize,
        powers: &Vec<Vec<P::G1Affine>>,
        // x_srs for univariate polynomials over X
        x_srs: &Vec<P::G1Affine>,
        wit_polys: &R1CSWitnessPolys<P>,
        pub_polys: &R1CSPublicPolys<P>,
        r: &P::ScalarField,
        x_domain: &GeneralEvaluationDomain<P::ScalarField>,
        y_domain: &GeneralEvaluationDomain<P::ScalarField>,
        transcript: &mut Transcript,
        challenge_v: &P::ScalarField,
        challenge_u1: &P::ScalarField,
    ) -> Option<P::G1> {

        assert_eq!(powers[0].len(), x_srs.len());
        let m = x_srs.len();
        let l = Net::n_parties();

        // R_i(X) = X^{i-1} and evals R_i(r^{m})
        let eval_r  = r.pow([(m * sub_prover_id) as u64]);
        let r_pow_m = r.pow([m as u64]);

        // f_a(rX)
        // get (1, r, r^{2} ..., r^{m-1})
        let mut r_m_powers = Vec::new();
        let mut current = P::ScalarField::one();
        for _ in 0..m {
            r_m_powers.push(current.clone());
            current *= r;
        }
        let coeffs_a = wit_polys.poly_a.coeffs.to_vec();
        let coeffs_ar: Vec<P::ScalarField> = coeffs_a.iter().zip(r_m_powers.iter()).map(|(left, right)| *left * *right).collect();
        let poly_ar = UnivariatePolynomial::from_coefficients_vec(coeffs_ar);

        // f1 - f4
        let eval_a_r = wit_polys.poly_a.evaluate(r);
        let eval_b_0 = wit_polys.poly_b.evaluate(&P::ScalarField::zero());
        let eval_b_virtual = wit_polys.poly_b.evaluate(&r.clone().inverse().unwrap()) * r_pow_m + eval_b_0 * (P::ScalarField::one() - r_pow_m);
        let eval_c_r = wit_polys.poly_c.evaluate(r);
        let eval_r_pow_m_mul_c_r = UnivariatePolynomial::from_coefficients_vec(vec![-eval_r * eval_c_r]);

        let polynomial_f1 = &pub_polys.poly_pa * &wit_polys.poly_w + UnivariatePolynomial::from_coefficients_vec(vec![-eval_r * eval_a_r]);
        let polynomial_f2 = &pub_polys.poly_pb * &wit_polys.poly_w + UnivariatePolynomial::from_coefficients_vec(vec![-eval_r * eval_b_virtual]);
        let polynomial_f3 = &(&pub_polys.poly_pc * &wit_polys.poly_w) + &eval_r_pow_m_mul_c_r;
        let polynomial_f4 = &(&(&poly_ar * &wit_polys.poly_b) * eval_r) + &eval_r_pow_m_mul_c_r;

        // target polynomial, rlc of f1-f4
        let mut polynomial_target = &polynomial_f1 + &(&polynomial_f2 * *challenge_v);
        polynomial_target += (*challenge_v * challenge_v, &polynomial_f3);
        polynomial_target += (challenge_v.pow([3 as u64]), &polynomial_f4);

        // get g1 and h1
        let (poly_g1, poly_h1) = IPA::<P>::get_g_mul_u_and_h(&polynomial_target, &challenge_u1, &x_domain);
        let com_g1 = KZG::<P>::commit(&x_srs, &poly_g1).unwrap();
        let com_h1 = KZG::<P>::commit(&x_srs, &poly_h1).unwrap();

        // send com of g1 and h1 to P0
        let com_g1_h1_slice = Net::send_to_master(&(com_g1, com_h1));
        let com_g1_h1 = if Net::am_master() {
            com_g1_h1_slice.unwrap().iter().fold((P::G1::zero(), P::G1::zero()), |(acc1, acc2), &(a, b)| {(acc1 + a, acc2 + b)})
        } else {
            (P::G1::zero(), P::G1::zero())
        };
        let (com_g1, com_h1) = com_g1_h1;

        // generate new challenges alpha and u2
        let (alpha, u2) = if Net::am_master() {
            let slice: &[P::G1] = &vec![com_g1, com_h1];
            <Transcript as ProofTranscript<P>>::append_points(transcript, b"alpha_and_u2", slice);
            let alpha = <Transcript as ProofTranscript<P>>::challenge_scalar(transcript, b"random_evaluation_for_x");
            let u2 = <Transcript as ProofTranscript<P>>::challenge_scalar(transcript, b"random_ldt_padding");
            Net::recv_from_master(Some(vec![(alpha, u2); Net::n_parties()]));
            (alpha, u2)
        } else {
            Net::recv_from_master(None)
        };

        // evaluate and send polynomial evaluations on alpha
        // also send g1(alpha) and h1(alpha)
        let eval_pa_alpha = pub_polys.poly_pa.evaluate(&alpha);
        let eval_pb_alpha = pub_polys.poly_pb.evaluate(&alpha);
        let eval_pc_alpha = pub_polys.poly_pc.evaluate(&alpha);
        let eval_w_alpha = wit_polys.poly_w.evaluate(&alpha);
        let eval_ar_alpha = wit_polys.poly_a.evaluate(&(*r * alpha));
        // assert_eq!(eval_ar_alpha, poly_ar.evaluate(&alpha));
        let eval_a_r = eval_a_r;
        let eval_b_alpha = wit_polys.poly_b.evaluate(&alpha);
        let eval_b_r_virtual = eval_b_virtual;
        let eval_c_r = eval_c_r;
        let eval_r = eval_r;

        // slices of g1(alpha) and h1(alpha)
        let eval_g1 = poly_g1.evaluate(&alpha);
        let eval_h1 = poly_h1.evaluate(&alpha);

        let evals = vec![eval_pa_alpha, eval_pb_alpha, eval_pc_alpha, eval_w_alpha, eval_ar_alpha, eval_a_r, 
                                                           eval_b_alpha, eval_b_r_virtual, eval_c_r, eval_r,
                                                           eval_g1, eval_h1];
        let evals_slice = Net::send_to_master(&evals);
        let evals = if Net::am_master() {
            evals_slice.unwrap()
        } else {
            vec![vec![P::ScalarField::zero()]]
        };

        let (eval_g1, eval_h1, com_g2, com_h2_low, com_h2_high, polynomials_y, polynomials_g2_h2) = if Net::am_master() {
            // g1(alpha) and h1(alpha)
            let eval_g1 = evals.iter().map(|eval| eval[10]).sum();
            let eval_h1 = evals.iter().map(|eval| eval[11]).sum();

            // compute univariate polynomials over Y with X = alpha
            // using ifft, from evaluations to polynomials
            // Require g2 and h2, so have to convert to coefficient terms
            let evals_pa_alpha = evals.iter().map(|eval| eval[0]).collect();
            let evals_pb_alpha = evals.iter().map(|eval| eval[1]).collect();
            let evals_pc_alpha = evals.iter().map(|eval| eval[2]).collect();
            let evals_w_alpha = evals.iter().map(|eval| eval[3]).collect();
            let evals_a_r_alpha = evals.iter().map(|eval| eval[4]).collect();
            let evals_a_r = evals.iter().map(|eval| eval[5]).collect();
            let evals_b_alpha = evals.iter().map(|eval| eval[6]).collect();
            let evals_b_r_virtual = evals.iter().map(|eval| eval[7]).collect();
            let evals_c_r = evals.iter().map(|eval| eval[8]).collect();
            let evals_r = evals.iter().map(|eval| eval[9]).collect();

            let poly_pa_alpha = Self::interpolate_from_eval_domain(&evals_pa_alpha, y_domain);
            let poly_pb_alpha = Self::interpolate_from_eval_domain(&evals_pb_alpha, y_domain);
            let poly_pc_alpha = Self::interpolate_from_eval_domain(&evals_pc_alpha, y_domain);
            let poly_w_alpha = Self::interpolate_from_eval_domain(&evals_w_alpha, y_domain);
            let poly_a_r_alpha = Self::interpolate_from_eval_domain(&evals_a_r_alpha, y_domain);
            let poly_a_r = Self::interpolate_from_eval_domain(&evals_a_r, y_domain);
            let poly_b_alpha = Self::interpolate_from_eval_domain(&evals_b_alpha, y_domain);
            let poly_b_r_virtual = Self::interpolate_from_eval_domain(&evals_b_r_virtual, y_domain);
            let poly_c_r = Self::interpolate_from_eval_domain(&evals_c_r, y_domain);
            let poly_r = Self::interpolate_from_eval_domain(&evals_r, y_domain);

            let poly_f1_alpha = &(&poly_pa_alpha * &poly_w_alpha) - &(&poly_r * &poly_a_r);
            let poly_f2_alpha = &(&poly_pb_alpha * &poly_w_alpha) - &(&poly_r * &poly_b_r_virtual);
            let poly_f3_alpha = &(&poly_pc_alpha * &poly_w_alpha) - &(&poly_r * &poly_c_r);
            let poly_f4_alpha = &(&(&poly_r * &poly_a_r_alpha) * &poly_b_alpha) - &(&poly_r * &poly_c_r);

            let polynomials_y = vec![poly_pa_alpha, poly_pb_alpha, poly_pc_alpha, poly_w_alpha,
                                                                                poly_a_r_alpha, poly_a_r, poly_b_alpha, poly_b_r_virtual, poly_c_r, poly_r];

            // get the target polynomial over Y via rlc
            let mut alpha_minus_u1 = alpha - challenge_u1;
            let mut polynomial_target_y = &poly_f1_alpha * alpha_minus_u1;
            alpha_minus_u1 *= challenge_v;
            polynomial_target_y += (alpha_minus_u1, &poly_f2_alpha);
            alpha_minus_u1 *= challenge_v;
            polynomial_target_y += (alpha_minus_u1, &poly_f3_alpha);
            alpha_minus_u1 *= challenge_v;
            polynomial_target_y += (alpha_minus_u1, &poly_f4_alpha);

            // get g2, h2low, h2high
            let (poly_g2, poly_h2) = IPA::<P>::get_g_mul_u_and_h(&polynomial_target_y, &u2, &y_domain);
            let coeffs_h2 = poly_h2.coeffs.to_vec();
            assert!(coeffs_h2.len() > l);
            let coeffs_h2_low: Vec<P::ScalarField> = coeffs_h2.iter().take(l).cloned().collect();
            let coeffs_h2_high = coeffs_h2.clone()[l..].to_vec();
            let poly_h2_low = UnivariatePolynomial::from_coefficients_vec(coeffs_h2_low);
            let poly_h2_high = UnivariatePolynomial::from_coefficients_vec(coeffs_h2_high);

            // get lagrange evaluations of g2, h2low, h2high
            let evals_g2 = poly_g2.evaluate_over_domain_by_ref(*y_domain);
            let evals_h2_low = poly_h2_low.evaluate_over_domain_by_ref(*y_domain);
            let evals_h2_high = poly_h2_high.evaluate_over_domain_by_ref(*y_domain);

            // compute commitments to g2, h2low, h2high
            // Note that y_srs is lagrange-based
            let y_srs: Vec<<P as Pairing>::G1Affine> = powers.iter()
                .filter_map(|row| row.get(0))
                .cloned()
                .collect();
            let com_g2 = KZG::<P>::commit_lagrange(&y_srs, &evals_g2).unwrap();
            let com_h2_low = KZG::<P>::commit_lagrange(&y_srs, &evals_h2_low).unwrap();
            let com_h2_high = KZG::<P>::commit_lagrange(&y_srs, &evals_h2_high).unwrap();

            // get polynomials_g2_h2
            let polynomials_g2_h2 = vec![poly_g2, poly_h2_low, poly_h2_high];

            (eval_g1, eval_h1, com_g2, com_h2_low, com_h2_high, polynomials_y, polynomials_g2_h2)
        } else {
            (P::ScalarField::zero(), P::ScalarField::zero(), P::G1::zero(), P::G1::zero(), P::G1::zero(), vec![UnivariatePolynomial::zero()], vec![UnivariatePolynomial::zero()])
        };

        // generate new challenge= beta
        let beta = if Net::am_master() {
            let slice: &[P::G1] = &vec![com_g2, com_h2_low, com_h2_high];
            <Transcript as ProofTranscript<P>>::append_points(transcript, b"beta", slice);
            let beta = <Transcript as ProofTranscript<P>>::challenge_scalar(transcript, b"random_evaluation_for_y");
            Net::recv_from_master(Some(vec![beta; Net::n_parties()]));
            beta
        } else {
            Net::recv_from_master(None)
        };

        // evaluate polynomials over beta
        let (evals_alpha_beta, evals_g2_h2) = if Net::am_master() {
            let eval_pa_alpha_beta = polynomials_y[0].evaluate(&beta);
            let eval_pb_alpha_beta = polynomials_y[1].evaluate(&beta);
            let eval_pc_alpha_beta = polynomials_y[2].evaluate(&beta);
            let eval_w_alpha_beta = polynomials_y[3].evaluate(&beta);
            let eval_ar_alpha_beta = polynomials_y[4].evaluate(&beta);
            let eval_a_r_beta = polynomials_y[5].evaluate(&beta);
            let eval_b_alpha_beta = polynomials_y[6].evaluate(&beta);
            let eval_b_r_virtual_beta = polynomials_y[7].evaluate(&beta);
            let eval_c_r_beta = polynomials_y[8].evaluate(&beta);
            let eval_r_beta = polynomials_y[9].evaluate(&beta);

            let eval_g2 = polynomials_g2_h2[0].evaluate(&beta);
            let eval_h2_low = polynomials_g2_h2[1].evaluate(&beta);
            let eval_h2_high = polynomials_g2_h2[2].evaluate(&beta);

            let vec1 = vec![eval_pa_alpha_beta, eval_pb_alpha_beta, eval_pc_alpha_beta, eval_w_alpha_beta,
                                                              eval_ar_alpha_beta, eval_a_r_beta, eval_b_alpha_beta, eval_b_r_virtual_beta, eval_c_r_beta, eval_r_beta];
            let vec2 = vec![eval_g2, eval_h2_low, eval_h2_high];
            (vec1, vec2)
        } else {
            (vec![P::ScalarField::zero()], vec![P::ScalarField::zero()])
        };

        // Self-test of evaluation validity
        if Net::am_master() {
            let z_h_eval_x = x_domain.evaluate_vanishing_polynomial(alpha);
            let t2 = (alpha * eval_g1 + (alpha - challenge_u1) * z_h_eval_x * eval_h1)/y_domain.size_as_field_element();
            let f1 = evals_alpha_beta[0] * evals_alpha_beta[3] - evals_alpha_beta[9] * evals_alpha_beta[5];
            let f2 = evals_alpha_beta[1] * evals_alpha_beta[3] - evals_alpha_beta[9] * evals_alpha_beta[7];
            let f3 = evals_alpha_beta[2] * evals_alpha_beta[3] - evals_alpha_beta[9] * evals_alpha_beta[8];
            let f4 = (evals_alpha_beta[4] * evals_alpha_beta[6] - evals_alpha_beta[8]) * evals_alpha_beta[9];

            let eval_rlc = linear_combination_field::<P>(&vec![f1, f2, f3, f4], &challenge_v);
            let left_hand = (beta - u2) * (alpha - challenge_u1) * eval_rlc;
            let right_hand = beta * evals_g2_h2[0] + (beta - u2) * t2 + (beta - u2) * y_domain.evaluate_vanishing_polynomial(beta) * (evals_g2_h2[1] + beta.pow([l as u64]) * evals_g2_h2[2]);
            assert_eq!(left_hand, right_hand);
        }

        println!("111");

        // TODO: invoke the de-batch-bivarate-kzg, de-univariate-kzg over x, de-uni-kzg over y with lagrange

        Some(P::G1::zero())
    }

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

    pub fn interpolate_from_eval_domain (
        evals: &Vec<P::ScalarField>,
        domain: &GeneralEvaluationDomain<P::ScalarField>,
    ) -> UnivariatePolynomial<P::ScalarField> {
        let eval_domain = Evaluations::<P::ScalarField, GeneralEvaluationDomain<P::ScalarField>>::from_vec_and_domain(evals.clone(), *domain);
        eval_domain.interpolate()
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
    fn test_r1cs_inner_instance() {

    }

    #[test]
    fn bivariate_sum_test() {
        let size_x = BIVARIATE_X_DEGREE + 1;
        let size_y = BIVARIATE_Y_DEGREE + 1;
        let mut rng = StdRng::seed_from_u64(0u64);
        let y_domain = 
            <GeneralEvaluationDomain<MyField> as EvaluationDomain<MyField>>::new(size_y).unwrap();
        let x_domain = 
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
        let mut left_polynomial = UnivariatePolynomial::zero();
        for i in 0..x_polynomials_1.len() {
            let mut current_polynomial = &x_polynomials_1[i] * &x_polynomials_2[i];
            current_polynomial = &current_polynomial * evals_3[i];
            left_polynomial += &current_polynomial;
        }

        let omega = y_domain.group_gen();
        let mut point = MyField::one();
        let mut right_polynomial = UnivariatePolynomial::zero();
        for _ in 0..bivariate_polynomial_1.x_polynomials.len() {
            let mut current_polynomial: UnivariatePolynomial<MyField> = bivariate_polynomial_1.evaluate_at_y_lagrange(&point, &y_domain);
            current_polynomial = &current_polynomial * &bivariate_polynomial_2.evaluate_at_y_lagrange(&point, &y_domain);
            current_polynomial = &current_polynomial * bivariate_polynomial_3.evaluate_lagrange(&(alpha, point), &y_domain);
            right_polynomial += &current_polynomial;
            point *= omega;
        }

        assert_eq!(left_polynomial, right_polynomial);

        let left_sum = IPA::<Bls12_381>::get_sum_on_domain(&left_polynomial, &x_domain);
        let right_sum = IPA::<Bls12_381>::get_sum_on_domain(&right_polynomial, &x_domain);
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