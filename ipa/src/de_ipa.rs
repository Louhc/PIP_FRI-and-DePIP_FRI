use ark_poly::{univariate::DensePolynomial as UnivariatePolynomial, DenseUVPolynomial, EvaluationDomain, Evaluations, GeneralEvaluationDomain, Polynomial};
use std::marker::PhantomData;
use ark_ec::pairing::Pairing;
use my_kzg::{batch_kzg::BatchKZG, biv_batch_kzg::BivBatchKZG, biv_trivial_kzg::VerifierSRS, helper::linear_combination_field, transcript::ProofTranscript, trivial_kzg::{UniVerifierSRS, KZG}};
use merlin::Transcript;
use crate::{ipa::IPA, helper::{R1CSPublicPolys, R1CSWitnessPolys}};
use ark_ff::{Zero, One, Field};
use de_network::{DeMultiNet as Net, DeNet, DeSerNet};
use std::time::{
    Instant,
    // Duration
};

pub struct DeIPA<P: Pairing> {
    _pairing: PhantomData<P>,
}

pub struct SNARKProofNoPre<P: Pairing> {
    coms_wit_polys: Vec<P::G1>,
    coms_g1_h1: Vec<P::G1>,
    coms_g2_h2: Vec<P::G1>,
    evals_wit_polys: Vec<P::ScalarField>,
    evals_g1_h1: Vec<P::ScalarField>,
    evals_g2_h2: Vec<P::ScalarField>,
    _proof_g1_h1: P::G1,
    _proof_g2_h2: P::G1,
    proofs_wit_polys: (P::G1, Vec<P::ScalarField>, P::ScalarField, (P::G1, P::G1), P::G1)
}


impl<P: Pairing> DeIPA<P> {

    pub fn de_r1cs_prove (
        // id can be zero
        sub_prover_id: usize,
        powers: &Vec<Vec<P::G1Affine>>,
        // x_srs for univariate polynomials over X
        x_srs: &Vec<P::G1Affine>,
        y_srs: &Vec<P::G1Affine>,
        v_srs: &VerifierSRS<P>,
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
        let uni_v_srs_for_x = UniVerifierSRS {
                g: v_srs.g.clone(),
                h: v_srs.h.clone(),
                h_alpha: v_srs.h_alpha.clone()
        };
        let uni_v_srs_for_y = UniVerifierSRS {
            g: v_srs.g.clone(),
            h: v_srs.h.clone(),
            h_alpha: v_srs.h_beta.clone()
        };

        // commit secret polynomials
        let time = Instant::now();
        let sub_polynomials = vec![wit_polys.poly_w.clone(), wit_polys.poly_a.clone(), wit_polys.poly_b.clone(), wit_polys.poly_c.clone()];
        let coms_wit_polys = BivBatchKZG::<P>::de_commit(sub_prover_id, &powers, &sub_polynomials);
        println!("Prover {:?} commit time: {:?}", sub_prover_id, time.elapsed());

        // R_i(X) = X^{i-1} and evals R_i(r^{m})
        let time = Instant::now();
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
        let eval_b_inverse = wit_polys.poly_b.evaluate(&r.clone().inverse().unwrap());
        let eval_b_virtual = eval_b_inverse * r_pow_m + eval_b_0 * (P::ScalarField::one() - r_pow_m);
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
        println!("Prover {:?} compute target polynomial time: {:?}", sub_prover_id, time.elapsed());

        // get g1 and h1
        let time = Instant::now();
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
        let coms_g1_h1 = vec![com_g1_h1.0, com_g1_h1.1];
        println!("Prover {:?} g_1 h_1 commit time: {:?}", sub_prover_id, time.elapsed());

        // generate new challenges alpha and u2
        let (alpha, u2, gamma) = if Net::am_master() {
            let slice: &[P::G1] = &coms_g1_h1;
            <Transcript as ProofTranscript<P>>::append_points(transcript, b"alpha_and_u2", slice);
            let alpha = <Transcript as ProofTranscript<P>>::challenge_scalar(transcript, b"random_evaluation_for_x");
            let u2 = <Transcript as ProofTranscript<P>>::challenge_scalar(transcript, b"random_ldt_padding");
            let gamma = <Transcript as ProofTranscript<P>>::challenge_scalar(transcript, b"batch_kzg_for_g1_h1");
            Net::recv_from_master(Some(vec![(alpha, u2, gamma); Net::n_parties()]));
            (alpha, u2, gamma)
        } else {
            Net::recv_from_master(None)
        };

        // evaluate and send polynomial evaluations on alpha
        // also send g1(alpha) and h1(alpha)
        let time = Instant::now();
        let eval_pa_alpha = pub_polys.poly_pa.evaluate(&alpha);
        let eval_pb_alpha = pub_polys.poly_pb.evaluate(&alpha);
        let eval_pc_alpha = pub_polys.poly_pc.evaluate(&alpha);
        let eval_w_alpha = wit_polys.poly_w.evaluate(&alpha);
        let eval_ar_alpha = wit_polys.poly_a.evaluate(&(*r * alpha));
        // assert_eq!(eval_ar_alpha, poly_ar.evaluate(&alpha));
        let eval_a_r = eval_a_r;
        let eval_b_alpha = wit_polys.poly_b.evaluate(&alpha);
        let eval_b_r_inverse = eval_b_inverse;
        let eval_b_0 = eval_b_0;
        let eval_c_r = eval_c_r;
        let eval_r = eval_r;

        // slices of g1(alpha) and h1(alpha)
        let eval_g1 = poly_g1.evaluate(&alpha);
        let eval_h1 = poly_h1.evaluate(&alpha);
        let proof_g1_h1 = BatchKZG::<P>::open(&x_srs, &vec![poly_g1, poly_h1], &alpha, &gamma).unwrap();

        let evals = vec![eval_pa_alpha, eval_pb_alpha, eval_pc_alpha, eval_w_alpha, eval_ar_alpha, eval_a_r, 
                                                           eval_b_alpha, eval_b_r_inverse, eval_b_0, eval_c_r, eval_r,
                                                           eval_g1, eval_h1];
        let evals_slice = Net::send_to_master(&(evals, proof_g1_h1));
        let evals = if Net::am_master() {
            evals_slice.unwrap()
        } else {
            Vec::new()
        };
        println!("Prover {:?} computes evaluations_alpha & de_proof_g1_h1 time: {:?}", sub_prover_id, time.elapsed());

        let time = Instant::now();
        let (evals_g1_h1, proof_g1_h1, coms_g2_h2, evals_domain_g2_h2, polynomials_y, polys_g2_h2) = if Net::am_master() {
            // g1(alpha) and h1(alpha)
            let eval_g1: P::ScalarField = evals.iter().map(|(eval, _)| eval[11]).sum();
            let eval_h1: P::ScalarField = evals.iter().map(|(eval, _)| eval[12]).sum();
            let evals_g1_h1 = vec![eval_g1, eval_h1];

            // get proof of g1 and h1
            let proof_g1_h1 = evals.iter().map(|(_, proof)| proof).sum();

            // compute univariate polynomials over Y with X = alpha
            // using ifft, from evaluations to polynomials
            // Require g2 and h2, so have to convert to coefficient terms
            let evals_pa_alpha = evals.iter().map(|(eval, _)| eval[0]).collect();
            let evals_pb_alpha = evals.iter().map(|(eval, _)| eval[1]).collect();
            let evals_pc_alpha = evals.iter().map(|(eval, _)| eval[2]).collect();
            let evals_w_alpha = evals.iter().map(|(eval, _)| eval[3]).collect();
            let evals_a_r_alpha = evals.iter().map(|(eval, _)| eval[4]).collect();
            let evals_a_r = evals.iter().map(|(eval, _)| eval[5]).collect();
            let evals_b_alpha = evals.iter().map(|(eval, _)| eval[6]).collect();
            let evals_b_r_inverse: Vec<P::ScalarField> = evals.iter().map(|(eval, _)| eval[7]).collect();
            let evals_b_0: Vec<P::ScalarField> = evals.iter().map(|(eval, _)| eval[8]).collect();
            let evals_c_r = evals.iter().map(|(eval, _)| eval[9]).collect();
            let evals_r = evals.iter().map(|(eval, _)| eval[10]).collect();

            let poly_pa_alpha = Self::interpolate_from_eval_domain(&evals_pa_alpha, y_domain);
            let poly_pb_alpha = Self::interpolate_from_eval_domain(&evals_pb_alpha, y_domain);
            let poly_pc_alpha = Self::interpolate_from_eval_domain(&evals_pc_alpha, y_domain);
            let poly_w_alpha = Self::interpolate_from_eval_domain(&evals_w_alpha, y_domain);
            let poly_a_r_alpha = Self::interpolate_from_eval_domain(&evals_a_r_alpha, y_domain);
            let poly_a_r = Self::interpolate_from_eval_domain(&evals_a_r, y_domain);
            let poly_b_alpha = Self::interpolate_from_eval_domain(&evals_b_alpha, y_domain);
            let poly_b_r_inverse = Self::interpolate_from_eval_domain(&evals_b_r_inverse, y_domain);
            let poly_b_0 = Self::interpolate_from_eval_domain(&evals_b_0, y_domain);
            let poly_b_r_virtual = &poly_b_r_inverse * r_pow_m + &poly_b_0 * (P::ScalarField::one() - r_pow_m);
            let poly_c_r = Self::interpolate_from_eval_domain(&evals_c_r, y_domain);
            let poly_r = Self::interpolate_from_eval_domain(&evals_r, y_domain);

            let poly_f1_alpha = &(&poly_pa_alpha * &poly_w_alpha) - &(&poly_r * &poly_a_r);
            let poly_f2_alpha = &(&poly_pb_alpha * &poly_w_alpha) - &(&poly_r * &poly_b_r_virtual);
            let poly_f3_alpha = &(&poly_pc_alpha * &poly_w_alpha) - &(&poly_r * &poly_c_r);
            let poly_f4_alpha = &(&(&poly_r * &poly_a_r_alpha) * &poly_b_alpha) - &(&poly_r * &poly_c_r);

            let polynomials_y = vec![poly_pa_alpha, poly_pb_alpha, poly_pc_alpha, poly_w_alpha,
                                                                                poly_a_r_alpha, poly_a_r, poly_b_alpha, poly_b_r_inverse, poly_b_0, poly_c_r, poly_r];
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
            let polys_g2_h2 = vec![poly_g2, poly_h2_low, poly_h2_high];

            // compute commitments to g2, h2low, h2high
            let com_g2 = KZG::<P>::commit_lagrange(&y_srs, &evals_g2).unwrap();
            let com_h2_low = KZG::<P>::commit_lagrange(&y_srs, &evals_h2_low).unwrap();
            let com_h2_high = KZG::<P>::commit_lagrange(&y_srs, &evals_h2_high).unwrap();
            let coms_g2_h2 = vec![com_g2, com_h2_low, com_h2_high];
            let evals_domain_g2_h2 = vec![evals_g2, evals_h2_low, evals_h2_high];

            (evals_g1_h1, proof_g1_h1, coms_g2_h2, evals_domain_g2_h2, polynomials_y, polys_g2_h2)
        } else {
            (Vec::new(), P::G1::zero(), Vec::new(), Vec::new(), Vec::new(), Vec::new())
        };
        println!("Prover {:?} computes  time: {:?}", sub_prover_id, time.elapsed());

        // get challenge beta from fiat shamir
        let beta = if Net::am_master() {
            let slice: &[P::G1] = &coms_g2_h2;
            <Transcript as ProofTranscript<P>>::append_points(transcript, b"beta", slice);
            let beta = <Transcript as ProofTranscript<P>>::challenge_scalar(transcript, b"random_evaluation_for_y");
            Net::recv_from_master(Some(vec![beta; Net::n_parties()]));
            beta
        } else {
            Net::recv_from_master(None)
        };

        // generate proof to alpha, beta
        let time = Instant::now();
        let x_points = vec![vec![alpha], vec![*r * alpha, *r], vec![alpha, r.inverse().unwrap(), P::ScalarField::zero()], vec![*r]];
        let transcript_here = transcript;
        let proofs_alpha_beta= BivBatchKZG::<P>::de_open_lagrange_at_same_y(sub_prover_id, &powers, &x_srs, &sub_polynomials, &x_points, &beta, &y_domain, &mut transcript_here.clone(), &gamma);
        println!("Prover {:?} computs proofs of bivariate polynomials time: {:?}", sub_prover_id, time.elapsed());

        let time = Instant::now();
        let  (evals_g1_h1, proof_g1_h1, evals_alpha_beta, evals_g2_h2, proof_g2_h2) = if Net::am_master() {
            // compute proof and evaluations to g2, h2low, h2high
            let proof_g2_h2 = BatchKZG::<P>::open_lagrange(&y_srs, &evals_domain_g2_h2, &beta, &y_domain, &gamma).unwrap();
            let eval_g2 = polys_g2_h2[0].evaluate(&beta);
            let eval_h2_low = polys_g2_h2[1].evaluate(&beta);
            let eval_h2_high = polys_g2_h2[2].evaluate(&beta);
            
            let eval_pa_alpha_beta = polynomials_y[0].evaluate(&beta);
            let eval_pb_alpha_beta = polynomials_y[1].evaluate(&beta);
            let eval_pc_alpha_beta = polynomials_y[2].evaluate(&beta);
            let eval_w_alpha_beta = polynomials_y[3].evaluate(&beta);
            let eval_ar_alpha_beta = polynomials_y[4].evaluate(&beta);
            let eval_a_r_beta = polynomials_y[5].evaluate(&beta);
            let eval_b_alpha_beta = polynomials_y[6].evaluate(&beta);
            let eval_b_r_inverse_beta = polynomials_y[7].evaluate(&beta);
            let eval_b_0_beta = polynomials_y[8].evaluate(&beta);
            let eval_c_r_beta = polynomials_y[9].evaluate(&beta);
            let eval_r_beta = polynomials_y[10].evaluate(&beta);

            let vec1 = vec![eval_pa_alpha_beta, eval_pb_alpha_beta, eval_pc_alpha_beta, eval_w_alpha_beta,
                                                              eval_ar_alpha_beta, eval_a_r_beta, eval_b_alpha_beta, eval_b_r_inverse_beta, eval_b_0_beta, eval_c_r_beta, eval_r_beta];
            let evals_g2_h2 = vec![eval_g2, eval_h2_low, eval_h2_high];
            (evals_g1_h1, proof_g1_h1, vec1, evals_g2_h2, proof_g2_h2)
        } else {
            (Vec::new(), P::G1::zero(), Vec::new(), Vec::new(), P::G1::zero())
        };
        println!("Prover {:?} computes g2 and h_2 evals and proofs time: {:?}", sub_prover_id, time.elapsed());

        // Self-test of evaluation validity
        if Net::am_master() {
            let z_h_eval_x = x_domain.evaluate_vanishing_polynomial(alpha);
            let t2 = (alpha * evals_g1_h1[0] + (alpha - challenge_u1) * z_h_eval_x * evals_g1_h1[1])/y_domain.size_as_field_element();
            let f1 = evals_alpha_beta[0] * evals_alpha_beta[3] - evals_alpha_beta[10] * evals_alpha_beta[5];
            let f2 = evals_alpha_beta[1] * evals_alpha_beta[3] - evals_alpha_beta[10] * (evals_alpha_beta[7] * r_pow_m + evals_alpha_beta[8] * (P::ScalarField::one() - r_pow_m));
            let f3 = evals_alpha_beta[2] * evals_alpha_beta[3] - evals_alpha_beta[10] * evals_alpha_beta[9];
            let f4 = (evals_alpha_beta[4] * evals_alpha_beta[6] - evals_alpha_beta[9]) * evals_alpha_beta[10];

            let eval_rlc = linear_combination_field::<P>(&vec![f1, f2, f3, f4], &challenge_v);
            let left_hand = (beta - u2) * (alpha - challenge_u1) * eval_rlc;
            let right_hand = beta * evals_g2_h2[0] + (beta - u2) * t2 + (beta - u2) * y_domain.evaluate_vanishing_polynomial(beta) * (evals_g2_h2[1] + beta.pow([l as u64]) * evals_g2_h2[2]);
            let check1 = left_hand == right_hand;
            assert!(check1);

            // check the validity of g1 and h1
            let check2 = BatchKZG::<P>::verify(&uni_v_srs_for_x, &coms_g1_h1, &alpha, &evals_g1_h1, &proof_g1_h1, &gamma).unwrap();
            assert!(check2);

            // check the validity of g2 and h2
            let check3 = BatchKZG::<P>::verify(&uni_v_srs_for_y, &coms_g2_h2, &beta, &evals_g2_h2, &proof_g2_h2, &gamma).unwrap();
            assert!(check3);

            // check the validity of bivariate polynomials
            let evals_bivariate = vec![vec![evals_alpha_beta[3]],
                                                    vec![evals_alpha_beta[4], evals_alpha_beta[5]],
                                                    vec![evals_alpha_beta[6], evals_alpha_beta[7], evals_alpha_beta[8]],
                                                    vec![evals_alpha_beta[9]]];
            let check4 = BivBatchKZG::<P>::verify_at_same_y(&v_srs, &coms_wit_polys.unwrap(), &x_points, &beta, &evals_bivariate, &proofs_alpha_beta.unwrap(), transcript_here, &gamma).unwrap();
            assert!(check4);

            println!("all checks pass !!!");
        }

        // TODO: invoke the de-batch-bivarate-kzg, de-univariate-kzg over x, de-uni-kzg over y with lagrange

        Some(P::G1::zero())
    }

    pub fn interpolate_from_eval_domain (
        evals: &Vec<P::ScalarField>,
        domain: &GeneralEvaluationDomain<P::ScalarField>,
    ) -> UnivariatePolynomial<P::ScalarField> {
        let eval_domain = Evaluations::<P::ScalarField, GeneralEvaluationDomain<P::ScalarField>>::from_vec_and_domain(evals.clone(), *domain);
        eval_domain.interpolate()
    }

    pub fn get_proof_size (
        proof: SNARKProofNoPre<P>
    ) -> usize {
        let field_size = size_of_val(&P::ScalarField::one());
        let group_size = size_of_val(&P::G1::zero());
        let proof_len_wit_polys = (proof.proofs_wit_polys.1.len() + 1) * field_size + 4 * group_size;
        let proof_len_groups = group_size * (
            proof.coms_wit_polys.len() +
            proof.coms_g1_h1.len() +
            proof.coms_g2_h2.len() +
            2
        );
        let proof_len_fields = field_size * (
            proof.evals_wit_polys.len() +
            proof.evals_g1_h1.len() +
            proof.evals_g2_h2.len()
        );
        proof_len_fields + proof_len_groups + proof_len_wit_polys
    }

}

