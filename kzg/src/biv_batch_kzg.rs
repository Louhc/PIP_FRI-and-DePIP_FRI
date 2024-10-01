use ark_ec::AffineRepr;
use ark_ec::{
    pairing::Pairing,
    scalar_mul::variable_base::VariableBaseMSM,
    Group, CurveGroup
};
use ark_ff::{One, Zero};
use ark_poly::polynomial::{
    univariate::DensePolynomial as UnivariatePolynomial, DenseUVPolynomial, Polynomial,
};
use ark_poly::{EvaluationDomain, Evaluations, GeneralEvaluationDomain};
use merlin::Transcript;
use crate::trivial_kzg::{self, KZG};
use crate::biv_trivial_kzg::BivariateKZG;
use crate::{helper::{interpolate_on_trivial_domain, generator_numerator_polynomial}, transcript::ProofTranscript};
use std::marker::PhantomData;
use ark_std::rand::Rng;
use crate::biv_trivial_kzg::{BivariatePolynomial, VerifierSRS};
use crate::{
    // transcript::ProofTranscript, 
    Error};

pub struct BivariateBatchKZG<P: Pairing> {
    _pairing: PhantomData<P>,
}

// Batch polynomial commitment for the same X and Y points, which will be used for the final batch PCS
impl<P: Pairing> BivariateBatchKZG<P> {
    pub fn setup<R: Rng>(
        rng: &mut R,
        x_degree: usize,
        y_degree: usize,
    ) -> Result<(Vec<Vec<P::G1Affine>>, VerifierSRS<P>), Error> {
        Ok(BivariateKZG::<P>::setup(rng, x_degree, y_degree).unwrap())
    }

    pub fn setup_lagrange<R: Rng>(
        rng: &mut R,
        x_degree: usize,
        y_degree: usize,
        domain: &GeneralEvaluationDomain<P::ScalarField>,
    ) -> Result<(Vec<Vec<P::G1Affine>>, VerifierSRS<P>), Error> {
        Ok(BivariateKZG::<P>::setup_lagrange(rng, x_degree, y_degree, domain).unwrap())
    }

    pub fn commit(
        powers: &Vec<Vec<P::G1Affine>>,
        bivariate_polynomials: &Vec<BivariatePolynomial<P::ScalarField>>,
    ) -> Result<Vec<P::G1>, Error> {
        assert!(powers.len() == bivariate_polynomials[0].x_polynomials.len());
        assert!(powers.len().is_power_of_two());
        assert!(powers[0].len() >= bivariate_polynomials[0].x_polynomials[0].degree() + 1);

        let mut coms = Vec::new();

        let mut extended_powers: Vec<<P as Pairing>::G1Affine> = Vec::new();
        for i in 0..powers.len() {
            extended_powers.extend(&powers[i]);
        }

        for j in 0..bivariate_polynomials.len() {
            let mut extended_coeff: Vec<<P as Pairing>::ScalarField> = Vec::new();
            for i in 0..powers.len() {
                let mut coeffs = bivariate_polynomials[j].x_polynomials[i].coeffs.to_vec();
                coeffs.resize(powers[0].len(), <P::ScalarField>::zero());
                extended_coeff.extend(&coeffs);
            }
            coms.push(P::G1::msm(&extended_powers, &extended_coeff).unwrap());
        }

        Ok(coms)
    }

    pub fn open(
        powers: &Vec<Vec<P::G1Affine>>,
        bivariate_polynomials: &Vec<BivariatePolynomial<P::ScalarField>>,
        point: &(P::ScalarField, P::ScalarField),
        transcript: &mut Transcript,
    ) -> Result<(P::G1, P::G1), Error> {

        // generate q1(x,y) and q2(y)
        // see f(x,y) - f(z1,z2) = f(x,y) - f(z1,y) + f(z1,y) - f(z1,z2)
        // q1(x,y) = f(x,y)-f(z1,y)/(x-z1) = \sum_i [(f_{i}(x)-f_{i}(z1))/(x-z1)] \cdot y^{i-1}
        // q2(y) = f(z1,y) - f(z1,z2) / (y - z2)

        let (x, y) = point;
        // used to generate q2(y)
        let y_srs: Vec<<P as Pairing>::G1Affine> = powers.iter()
            .filter_map(|row| row.get(0))
            .cloned()
            .collect();
        let challenge = <Transcript as ProofTranscript<P>>::challenge_scalar(
                transcript, b"combined_polynomials_evaluated_at_the_same_point");

        // compute the vector composed by (f_{1,1}(z1), f_{2,1}(z1), ..., f_{l,1}(z1))
        //                                (f_{1,2}(z1), f_{2,2}(z1), ..., f_{l,2}(z1))
        //                                 ..........................................
        //                                (f_{1,k}(z1), f_{2,k}(z1), ..., f_{l,k}(z1))
        // let mut evals_z1 = Vec::new();
        let mut combined_polynomial_q2 = UnivariatePolynomial::zero();
        let mut linear_factor = P::ScalarField::one();
        // generate q2(Y)
        // compute f_{j,i} (z1) and f_j (z1, Y)
        for j in 0..bivariate_polynomials.len() {
            let evals: Vec<P::ScalarField> = bivariate_polynomials[j].x_polynomials
                .iter()
                .map(|poly| poly.evaluate(&x))
                .collect();
            // evals_z1.push(evals.clone());

            let combined_polynomial_slice_q2 = &UnivariatePolynomial::from_coefficients_vec(evals) * linear_factor;
            linear_factor *= challenge;
            combined_polynomial_q2 += &combined_polynomial_slice_q2;
        }

        let polynomial_q2 = &combined_polynomial_q2
        / &UnivariatePolynomial::from_coefficients_vec(vec![
            -y.clone(),
            P::ScalarField::one(),
        ]);
        let mut coeffs_q2 = polynomial_q2.coeffs.to_vec();
        coeffs_q2.resize(y_srs.len(), <P::ScalarField>::zero());
        
        // generate q1(x,y) = \sum_j f_j (x,y)-f_j (z1,y) / (x-z1) = \sum_i gamma^{i-1} \sum_j [(f_{j,i}(x)-f_{j,i}(z1))/(x-z1)] \cdot y^{i-1}

        let mut coeffs_q1: Vec<<P as Pairing>::ScalarField> = Vec::new();
        let mut xy_srs: Vec<<P as Pairing>::G1Affine> = Vec::new();

        for i in 0..y_srs.len() {
            let mut combined_polynomial_slice_for_q1 = UnivariatePolynomial::zero();
            linear_factor = P::ScalarField::one();
            for j in 0..bivariate_polynomials.len() {
                combined_polynomial_slice_for_q1 += &(&bivariate_polynomials[j].x_polynomials[i] * linear_factor);
                linear_factor *= challenge;
            }
            let polynomial_slice_q1 = &combined_polynomial_slice_for_q1
                / &UnivariatePolynomial::from_coefficients_vec(vec![
                    -x.clone(),
                    P::ScalarField::one()
                ]);
            let mut coeffs_slice_q1 = polynomial_slice_q1.coeffs.to_vec();
            coeffs_slice_q1.resize(powers[0].len(), <P::ScalarField>::zero());

            coeffs_q1.extend(&coeffs_slice_q1);
            xy_srs.extend(&powers[i]);
        }

        let proof = (
            P::G1::msm(&xy_srs, &coeffs_q1).unwrap(), 
            P::G1::msm(&y_srs, &coeffs_q2).unwrap());
        
        Ok(proof)
    }

    pub fn open_lagrange(
        powers: &Vec<Vec<P::G1Affine>>,
        bivariate_polynomials: &Vec<BivariatePolynomial<P::ScalarField>>,
        point: &(P::ScalarField, P::ScalarField),
        domain: &GeneralEvaluationDomain<P::ScalarField>,
        transcript: &mut Transcript,
    ) -> Result<(P::G1, P::G1), Error> {

        // generate q1(x,y) and q2(y)
        // see f(x,y) - f(z1,z2) = f(x,y) - f(z1,y) + f(z1,y) - f(z1,z2)
        // q1(x,y) = f(x,y)-f(z1,y)/(x-z1) = \sum_i [(f_{i}(x)-f_{i}(z1))/(x-z1)] \cdot y^{i-1}
        // q2(y) = f(z1,y) - f(z1,z2) / (y - z2)

        let (x, y) = point;
        // used to generate q2(y)
        let y_srs: Vec<<P as Pairing>::G1Affine> = powers.iter()
            .filter_map(|row| row.get(0))
            .cloned()
            .collect();
        let challenge = <Transcript as ProofTranscript<P>>::challenge_scalar(
                transcript, b"combined_polynomials_evaluated_at_the_same_point");

        // compute the vector composed by (f_{1,1}(z1), f_{2,1}(z1), ..., f_{l,1}(z1))
        //                                (f_{1,2}(z1), f_{2,2}(z1), ..., f_{l,2}(z1))
        //                                 ..........................................
        //                                (f_{1,k}(z1), f_{2,k}(z1), ..., f_{l,k}(z1))
        let mut combined_polynomial_q2 = UnivariatePolynomial::zero();
        let mut linear_factor = P::ScalarField::one();
        // generate q2(Y)
        // compute f_{j,i} (z1) and f_j (z1, Y)
        for j in 0..bivariate_polynomials.len() {
            let evals: Vec<P::ScalarField> = bivariate_polynomials[j].x_polynomials
                .iter()
                .map(|poly| poly.evaluate(&x))
                .collect();

            let combined_polynomial_slice_q2 = &UnivariatePolynomial::from_coefficients_vec(evals) * linear_factor;
            linear_factor *= challenge;
            combined_polynomial_q2 += &combined_polynomial_slice_q2;
        }

        // let polynomial_q2 = &combined_polynomial_q2
        // / &UnivariatePolynomial::from_coefficients_vec(vec![
        //     -y.clone(),
        //     P::ScalarField::one(),
        // ]);
        let coeffs_q2 = combined_polynomial_q2.coeffs.to_vec();
        assert_eq!(y_srs.len(), coeffs_q2.len());
        let evals_q2 = Evaluations::<P::ScalarField>::from_vec_and_domain(coeffs_q2, *domain);
        let coeffs_q2 = KZG::<P>::get_quotient_eval_lagrange(&evals_q2, &y, &domain);
        
        // generate q1(x,y) = \sum_j f_j (x,y)-f_j (z1,y) / (x-z1) = \sum_i gamma^{i-1} \sum_j [(f_{j,i}(x)-f_{j,i}(z1))/(x-z1)] \cdot y^{i-1}

        let mut coeffs_q1: Vec<<P as Pairing>::ScalarField> = Vec::new();
        let mut xy_srs: Vec<<P as Pairing>::G1Affine> = Vec::new();

        for i in 0..y_srs.len() {
            let mut combined_polynomial_slice_for_q1 = UnivariatePolynomial::zero();
            linear_factor = P::ScalarField::one();
            for j in 0..bivariate_polynomials.len() {
                combined_polynomial_slice_for_q1 += &(&bivariate_polynomials[j].x_polynomials[i] * linear_factor);
                linear_factor *= challenge;
            }
            let polynomial_slice_q1 = &combined_polynomial_slice_for_q1
                / &UnivariatePolynomial::from_coefficients_vec(vec![
                    -x.clone(),
                    P::ScalarField::one()
                ]);
            let mut coeffs_slice_q1 = polynomial_slice_q1.coeffs.to_vec();
            coeffs_slice_q1.resize(powers[0].len(), <P::ScalarField>::zero());

            coeffs_q1.extend(&coeffs_slice_q1);
            xy_srs.extend(&powers[i]);
        }

        let proof = (
            P::G1::msm(&xy_srs, &coeffs_q1).unwrap(), 
            P::G1::msm(&y_srs, &coeffs_q2).unwrap());
        
        Ok(proof)
    }

    pub fn open_at_same_y(
        powers: &Vec<Vec<P::G1Affine>>,
        bivariate_polynomials: &Vec<BivariatePolynomial<P::ScalarField>>,
        x_points: &Vec<Vec<P::ScalarField>>,
        y_point: &P::ScalarField,
        transcript: &mut Transcript,
    ) -> Result<(P::G1, Vec<P::ScalarField>, P::ScalarField, (P::G1, P::G1), P::G1), Error> {

        assert_eq!(x_points.len(), bivariate_polynomials.len());
        let gamma = <Transcript as ProofTranscript<P>>::challenge_scalar(
            transcript, b"combined_polynomial_x_beta");
        let x_point_vec = x_points.iter().flatten().cloned().collect();
        let numerator_polynomial = generator_numerator_polynomial::<P>(&x_point_vec);
        
        let mut combined_polynomial = UnivariatePolynomial::zero();
        // challenge
        let mut challenge_gamma = P::ScalarField::one();
        for i in 0..x_points.len() {
            // generate r_i(x) from x_points[i]
            let mut evals = Vec::new();
            for j in 0..x_points[i].len() {
                let point: (<P as Pairing>::ScalarField, <P as Pairing>::ScalarField) = (x_points[i][j], y_point.clone());
                let eval: <P as Pairing>::ScalarField = bivariate_polynomials[i].evaluate(&point);
                evals.push(eval);
            }
            let polynomial_r = interpolate_on_trivial_domain::<P>(&x_points[i], &evals);
            assert_eq!(polynomial_r.degree()+1, x_points[i].len());

            // generate f_i(x, beta)
            let mut polynomial_f_x_beta = UnivariatePolynomial::zero();
            let mut constant_term = P::ScalarField::one();
            for k in 0..bivariate_polynomials[i].x_polynomials.len() {
                polynomial_f_x_beta += (constant_term, &bivariate_polynomials[i].x_polynomials[k]);
                constant_term *= y_point;
            }

            // generate final poynomial with linear combination
            let helper_polynomial = &numerator_polynomial / &(generator_numerator_polynomial::<P>(&x_points[i]));
            let combined_polynomial_slice = &(&polynomial_f_x_beta - &polynomial_r) * &helper_polynomial;
            combined_polynomial += (challenge_gamma, &combined_polynomial_slice);
            challenge_gamma *= gamma;
        }

        let polynomial_q = &combined_polynomial / &numerator_polynomial;
        let mut coeffs_q = polynomial_q.coeffs.to_vec();
        coeffs_q.resize(powers[0].len(), <P::ScalarField>::zero());
        let proof_q = P::G1::msm(&powers[0], &coeffs_q).unwrap();

        // generate eta using fiat-shamir
        <Transcript as ProofTranscript<P>>::append_point(transcript, b"combined_polynomial_x_beta", &proof_q);
        let eta = <Transcript as ProofTranscript<P>>::challenge_scalar(
            transcript, b"random_evaluate_point");
        let point_eta_beta = (eta, y_point.clone());
        let evals_eta_beta: Vec<P::ScalarField> = bivariate_polynomials.iter().map(|poly| poly.evaluate(&point_eta_beta)).collect();
        let eval_q_eta: P::ScalarField = polynomial_q.evaluate(&eta);
        // let proof_eval = (evals_eta_beta, eval_q_eta);

        // update the transcript state
        let mut slice_vector: Vec<P::ScalarField> = evals_eta_beta.clone();
        slice_vector.push(eval_q_eta.clone());
        let slice: &[P::ScalarField] = &slice_vector;
        <Transcript as ProofTranscript<P>>::append_scalars(transcript, b"combined_polynomial_x_beta", slice);
        let proof_q1_q2 = Self::open(&powers, &bivariate_polynomials, &point_eta_beta, transcript).unwrap();
        let proof_q3 = KZG::<P>::open(&powers[0], &polynomial_q, &eta).unwrap();

        let proof = (proof_q, evals_eta_beta, eval_q_eta, proof_q1_q2, proof_q3);

        Ok(proof)
     }

     pub fn open_lagrange_at_same_y(
        powers: &Vec<Vec<P::G1Affine>>,
        bivariate_polynomials: &Vec<BivariatePolynomial<P::ScalarField>>,
        x_points: &Vec<Vec<P::ScalarField>>,
        y_point: &P::ScalarField,
        domain: &GeneralEvaluationDomain<P::ScalarField>,
        transcript: &mut Transcript,
    ) -> Result<(P::G1, Vec<P::ScalarField>, P::ScalarField, (P::G1, P::G1), P::G1), Error> {

        assert_eq!(x_points.len(), bivariate_polynomials.len());
        let gamma = <Transcript as ProofTranscript<P>>::challenge_scalar(
            transcript, b"combined_polynomial_x_beta");
        let x_point_vec = x_points.iter().flatten().cloned().collect();
        let numerator_polynomial = generator_numerator_polynomial::<P>(&x_point_vec);

        // generate x_srs
        let mut result = vec![P::G1::zero(); powers[0].len()];
        for i in 0..powers[0].len() {
            for j in 0..powers.len() {
                result[i] += powers[j][i].into_group();
            }
        }
        assert!(result[0] == P::G1::generator());
        let x_srs = <P as Pairing>::G1::normalize_batch(&result);
        
        let mut combined_polynomial = UnivariatePolynomial::zero();
        // challenge
        let mut challenge_gamma = P::ScalarField::one();
        for i in 0..x_points.len() {
            // generate r_i(x) from x_points[i]
            let mut evals = Vec::new();
            for j in 0..x_points[i].len() {
                let point: (<P as Pairing>::ScalarField, <P as Pairing>::ScalarField) = (x_points[i][j], y_point.clone());
                let eval: <P as Pairing>::ScalarField = bivariate_polynomials[i].evaluate_lagrange(&point, &domain);
                evals.push(eval);
            }
            let polynomial_r = interpolate_on_trivial_domain::<P>(&x_points[i], &evals);
            assert_eq!(polynomial_r.degree()+1, x_points[i].len());

            // generate f_i(x, beta) = \sum_k f_i,k(x) L_k(beta)
            let mut polynomial_f_x_beta = UnivariatePolynomial::zero();
            let evals_y_lagrange = EvaluationDomain::evaluate_all_lagrange_coefficients(&domain.clone(), *y_point);
            for k in 0..bivariate_polynomials[i].x_polynomials.len() {
                polynomial_f_x_beta += (evals_y_lagrange[k], &bivariate_polynomials[i].x_polynomials[k]);
            }

            // generate final poynomial with linear combination
            let helper_polynomial = &numerator_polynomial / &(generator_numerator_polynomial::<P>(&x_points[i]));
            let combined_polynomial_slice = &(&polynomial_f_x_beta - &polynomial_r) * &helper_polynomial;
            combined_polynomial += (challenge_gamma, &combined_polynomial_slice);
            challenge_gamma *= gamma;
        }

        let polynomial_q = &combined_polynomial / &numerator_polynomial;
        let mut coeffs_q = polynomial_q.coeffs.to_vec();
        coeffs_q.resize(powers[0].len(), <P::ScalarField>::zero());
        let proof_q = P::G1::msm(&x_srs, &coeffs_q).unwrap();

        // generate eta using fiat-shamir
        <Transcript as ProofTranscript<P>>::append_point(transcript, b"combined_polynomial_x_beta", &proof_q);
        let eta = <Transcript as ProofTranscript<P>>::challenge_scalar(
            transcript, b"random_evaluate_point");
        let point_eta_beta = (eta, y_point.clone());
        let evals_eta_beta: Vec<P::ScalarField> = bivariate_polynomials.iter().map(|poly| poly.evaluate_lagrange(&point_eta_beta, &domain)).collect();
        let eval_q_eta: P::ScalarField = polynomial_q.evaluate(&eta);
        // let proof_eval = (evals_eta_beta, eval_q_eta);

        // update the transcript state
        let mut slice_vector: Vec<P::ScalarField> = evals_eta_beta.clone();
        slice_vector.push(eval_q_eta.clone());
        let slice: &[P::ScalarField] = &slice_vector;
        <Transcript as ProofTranscript<P>>::append_scalars(transcript, b"combined_polynomial_x_beta", slice);
        let proof_q1_q2 = Self::open_lagrange(&powers, &bivariate_polynomials, &point_eta_beta, &domain, transcript).unwrap();
        let proof_q3 = KZG::<P>::open(&x_srs, &polynomial_q, &eta).unwrap();

        let proof = (proof_q, evals_eta_beta, eval_q_eta, proof_q1_q2, proof_q3);

        Ok(proof)
     }

     pub fn verify_at_same_y(
        v_srs: &VerifierSRS<P>,
        coms: &Vec<P::G1>,
        x_points: &Vec<Vec<P::ScalarField>>,
        y_point: &P::ScalarField,
        evals: &Vec<Vec<P::ScalarField>>,
        proof: &(P::G1, Vec<P::ScalarField>, P::ScalarField, (P::G1, P::G1), P::G1),
        transcript: &mut Transcript
    ) -> Result<bool, Error> {
        assert!(coms.len() >= 1);
        assert_eq!(coms.len(), evals.len());
        assert_eq!(coms.len(), x_points.len());
        
        let gamma = <Transcript as ProofTranscript<P>>::challenge_scalar(
            transcript, b"combined_polynomial_x_beta");
        <Transcript as ProofTranscript<P>>::append_point(transcript, b"combined_polynomial_x_beta", &proof.0);
        let eta = <Transcript as ProofTranscript<P>>::challenge_scalar(
            transcript, b"random_evaluate_point");
        
        // check1: validity of q and q(eta)
        let kzg_v_srs = trivial_kzg::VerifierSRS::<P> {
            g: v_srs.g, 
            h: v_srs.h,
            h_alpha: v_srs.h_alpha
        };
        let check1 = KZG::<P>::verify(&kzg_v_srs, &proof.0, &eta, &proof.2, &proof.4).unwrap();

        // check2: validity of \sum_i \gamma^{i-1} (f_i(X, beta) - r_i(X)) * Z_{T_1\R_i}(X) = q(X)Z_{T_1}(X)
        let x_point_vec = x_points.iter().flatten().cloned().collect();
        let numerator_polynomial = generator_numerator_polynomial::<P>(&x_point_vec);
        let right_check2 = numerator_polynomial.evaluate(&eta) * proof.2;
        let mut left_check2 = P::ScalarField::zero();
        let mut linear_term = P::ScalarField::one();
        for i in 0..x_points.len() {
            let polynomial_r = interpolate_on_trivial_domain::<P>(&x_points[i], &evals[i]);
            assert_eq!(polynomial_r.degree()+1, x_points[i].len());
            let eval_r = polynomial_r.evaluate(&eta);

            let helper_polynomial = &numerator_polynomial / &(generator_numerator_polynomial::<P>(&x_points[i]));
            let eval_helper = helper_polynomial.evaluate(&eta);

            left_check2 += linear_term * eval_helper * (proof.1[i] - eval_r);
            linear_term *= gamma;
        }
        let check2 = left_check2 == right_check2;

        // check3: validity of f_i(eta, beta)
        // update the transcript state
        let mut slice_vector: Vec<P::ScalarField> = proof.1.clone();
        slice_vector.push(proof.2.clone());
        let slice: &[P::ScalarField] = &slice_vector;
        <Transcript as ProofTranscript<P>>::append_scalars(transcript, b"combined_polynomial_x_beta", slice);
        let eta_beta = (eta, y_point.clone());
        let check3 = BivariateBatchKZG::verify(&v_srs, &coms, &eta_beta, &proof.1, &proof.3, transcript).unwrap();

        Ok(check1 && check2 && check3)
    }

    pub fn verify(
        v_srs: &VerifierSRS<P>,
        coms: &Vec<P::G1>,
        point: &(P::ScalarField, P::ScalarField),
        evals: &Vec<P::ScalarField>,
        proof: &(P::G1, P::G1),
        transcript: &mut Transcript
    ) -> Result<bool, Error> {
        assert!(coms.len() >= 1);
        assert!(coms.len() == evals.len());

        let challenge = <Transcript as ProofTranscript<P>>::challenge_scalar(
            transcript, b"combined_polynomials_evaluated_at_the_same_point");

        let mut linear_factor = P::ScalarField::one();
        let mut linear_combination = coms[0].clone() - v_srs.g * evals[0];
        for i in 1..coms.len() {
            linear_factor *= challenge;
            linear_combination += (coms[i].clone() - v_srs.g * evals[i]) * linear_factor;
        }

        let (x, y) = point;
        let left = P::pairing(linear_combination, v_srs.h);
        let right1 = P::pairing(proof.0.clone(), v_srs.h_alpha - v_srs.h * x);
        let right2 = P::pairing(proof.1.clone(), v_srs.h_beta - v_srs.h * y);

        Ok(left == right1 + right2)
    }
}


#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_381::Bls12_381;
    use ark_std::rand::{rngs::StdRng, SeedableRng};
    use ark_poly::polynomial::{
        univariate::DensePolynomial as UnivariatePolynomial, DenseUVPolynomial,
    };
    use ark_std::UniformRand;
    use ark_poly::{EvaluationDomain, GeneralEvaluationDomain};
    const BIVARIATE_X_DEGREE: usize = 255;
    const BIVARIATE_Y_DEGREE: usize = 511;
    const POLYNOMIAL_NUMBER: usize = 10;
    type TestBivariatePolyCommitment = BivariateBatchKZG<Bls12_381>;
    // type TestUnivariatePolyCommitment = UnivariatePolynomialCommitment<Bls12_381, Blake2b>;

    #[test]
    fn bivariate_poly_commit_at_the_same_point_test() {
        let mut rng = StdRng::seed_from_u64(0u64);
        let srs =
            TestBivariatePolyCommitment::setup(&mut rng, BIVARIATE_X_DEGREE, BIVARIATE_Y_DEGREE)
                .unwrap();
        // let v_srs = srs.0.get_verifier_key();

        let mut bivariate_polynomials = Vec::new();
        for _ in 0..POLYNOMIAL_NUMBER {
            let mut x_polynomials = Vec::new();
            for _ in 0..BIVARIATE_Y_DEGREE + 1 {
                let mut x_polynomial_coeffs = vec![];
                for _ in 0..BIVARIATE_X_DEGREE + 1 {
                    x_polynomial_coeffs.push(<Bls12_381 as Pairing>::ScalarField::rand(&mut rng));
                }
                x_polynomials.push(UnivariatePolynomial::from_coefficients_slice(
                    &x_polynomial_coeffs,
                ));
            }
            bivariate_polynomials.push (BivariatePolynomial { x_polynomials });
        }

        // Commit to the polynomials
        let coms =
            TestBivariatePolyCommitment::commit(&srs.0, &bivariate_polynomials).unwrap();
        let mut prover_transcript : Transcript = Transcript::new(b"batch bivariate KZG at the same point");

        // Evaluate at challenge point
        let point = (UniformRand::rand(&mut rng), UniformRand::rand(&mut rng));
        let eval_proof = TestBivariatePolyCommitment::open(
            &srs.0,
            &bivariate_polynomials,
            &point,
            &mut prover_transcript
        )
        .unwrap();

        let mut evals = Vec::new();
        for i in 0..bivariate_polynomials.len() {
            let eval = bivariate_polynomials[i].evaluate(&point);
            evals.push(eval);
        }

        // proof size
        println!("Proof size is {} bytes", size_of_val(&eval_proof));

        // Verify proof
        let mut verifier_transcript : Transcript = Transcript::new(b"batch bivariate KZG at the same point");
        assert!(
            TestBivariatePolyCommitment::verify(&srs.1, &coms, &point, &evals, &eval_proof, &mut verifier_transcript).unwrap()
        );

    }

    #[test]
    fn bivariate_poly_commit_lagrange_at_the_same_point_test() {
        let mut rng = StdRng::seed_from_u64(0u64);
        let domain = <GeneralEvaluationDomain<<Bls12_381 as Pairing>::ScalarField> as EvaluationDomain<<Bls12_381 as Pairing>::ScalarField>>::new(BIVARIATE_Y_DEGREE + 1).unwrap();
        let srs =
            TestBivariatePolyCommitment::setup_lagrange(&mut rng, BIVARIATE_X_DEGREE, BIVARIATE_Y_DEGREE, &domain)
                .unwrap();

        let mut bivariate_polynomials = Vec::new();
        for _ in 0..POLYNOMIAL_NUMBER {
            let mut x_polynomials = Vec::new();
            for _ in 0..BIVARIATE_Y_DEGREE + 1 {
                let mut x_polynomial_coeffs = vec![];
                for _ in 0..BIVARIATE_X_DEGREE + 1 {
                    x_polynomial_coeffs.push(<Bls12_381 as Pairing>::ScalarField::rand(&mut rng));
                }
                x_polynomials.push(UnivariatePolynomial::from_coefficients_slice(
                    &x_polynomial_coeffs,
                ));
            }
            bivariate_polynomials.push (BivariatePolynomial { x_polynomials });
        }

        // Commit to the polynomials
        let coms =
            TestBivariatePolyCommitment::commit(&srs.0, &bivariate_polynomials).unwrap();
        let mut prover_transcript : Transcript = Transcript::new(b"batch bivariate KZG at the same point");

        // Evaluate at challenge point
        let point = (UniformRand::rand(&mut rng), UniformRand::rand(&mut rng));
        let eval_proof = TestBivariatePolyCommitment::open_lagrange(
            &srs.0,
            &bivariate_polynomials,
            &point,
            &domain,
            &mut prover_transcript
        ).unwrap();

        let mut evals = Vec::new();
        for i in 0..bivariate_polynomials.len() {
            let eval = bivariate_polynomials[i].evaluate_lagrange(&point, &domain);
            evals.push(eval);
        }

        // proof size
        println!("Proof size is {} bytes", size_of_val(&eval_proof));

        // Verify proof
        let mut verifier_transcript : Transcript = Transcript::new(b"batch bivariate KZG at the same point");
        assert!(
            TestBivariatePolyCommitment::verify(&srs.1, &coms, &point, &evals, &eval_proof, &mut verifier_transcript).unwrap()
        );

    }

    #[test]
    fn bivariate_poly_commit_at_the_same_y_test() {
        let mut rng = StdRng::seed_from_u64(0u64);
        let srs =
            TestBivariatePolyCommitment::setup(&mut rng, BIVARIATE_X_DEGREE, BIVARIATE_Y_DEGREE)
                .unwrap();
        // let v_srs = srs.0.get_verifier_key();

        let mut bivariate_polynomials = Vec::new();
        for _ in 0..POLYNOMIAL_NUMBER {
            let mut x_polynomials = Vec::new();
            for _ in 0..BIVARIATE_Y_DEGREE + 1 {
                let mut x_polynomial_coeffs = vec![];
                for _ in 0..BIVARIATE_X_DEGREE + 1 {
                    x_polynomial_coeffs.push(<Bls12_381 as Pairing>::ScalarField::rand(&mut rng));
                }
                x_polynomials.push(UnivariatePolynomial::from_coefficients_slice(
                    &x_polynomial_coeffs,
                ));
            }
            bivariate_polynomials.push (BivariatePolynomial { x_polynomials });
        }

        // Commit to the polynomials
        let coms =
            TestBivariatePolyCommitment::commit(&srs.0, &bivariate_polynomials).unwrap();
        let mut prover_transcript : Transcript = Transcript::new(b"batch bivariate KZG at the same y");
        println!("com size is {} bytes", coms.len() * size_of_val(&coms[0]));

        // Evaluate at multiple challenge points
        let y_point = UniformRand::rand(&mut rng);
        let mut x_points = Vec::new();
        for i in 0..bivariate_polynomials.len() {
            if i%2 == 1 {
                // x_points.push(vec![UniformRand::rand(&mut rng)]);
                x_points.push(vec![UniformRand::rand(&mut rng), UniformRand::rand(&mut rng)]);
            }
            else {
                x_points.push(vec![UniformRand::rand(&mut rng), UniformRand::rand(&mut rng), UniformRand::rand(&mut rng)]);
            }
        }

        let eval_proof = TestBivariatePolyCommitment::open_at_same_y(
            &srs.0,
            &bivariate_polynomials,
            &x_points,
            &y_point,
            &mut prover_transcript
        )
        .unwrap();

        let mut evals: Vec<Vec<<Bls12_381 as Pairing>::ScalarField>> = Vec::new();
        for i in 0..POLYNOMIAL_NUMBER {
            let mut eval_i = Vec::new();
            for j in 0..x_points[i].len() {
                let point = (x_points[i][j], y_point);
                let eval = bivariate_polynomials[i].evaluate(&point);
                eval_i.push(eval);
            }
            evals.push(eval_i);
        }

        // proof size
        let proof_size = (eval_proof.1.len() + 1) * size_of_val(&<Bls12_381 as Pairing>::ScalarField::one()) + 4 * size_of_val(&eval_proof.0);
        println!("Proof size is {} bytes", proof_size);

        // Verify proof
        let mut verifier_transcript : Transcript = Transcript::new(b"batch bivariate KZG at the same y");
        assert!(
            TestBivariatePolyCommitment::verify_at_same_y(&srs.1, &coms, &x_points, &y_point, &evals, &eval_proof, &mut verifier_transcript).unwrap()
        );

    }

    #[test]
    fn bivariate_poly_commit_lagrange_at_the_same_y_test() {
        let mut rng = StdRng::seed_from_u64(0u64);
        let domain = <GeneralEvaluationDomain<<Bls12_381 as Pairing>::ScalarField> as EvaluationDomain<<Bls12_381 as Pairing>::ScalarField>>::new(BIVARIATE_Y_DEGREE + 1).unwrap();
        let srs =
            TestBivariatePolyCommitment::setup_lagrange(&mut rng, BIVARIATE_X_DEGREE, BIVARIATE_Y_DEGREE, &domain)
                .unwrap();
        // let v_srs = srs.0.get_verifier_key();

        let mut bivariate_polynomials = Vec::new();
        for _ in 0..POLYNOMIAL_NUMBER {
            let mut x_polynomials = Vec::new();
            for _ in 0..BIVARIATE_Y_DEGREE + 1 {
                let mut x_polynomial_coeffs = vec![];
                for _ in 0..BIVARIATE_X_DEGREE + 1 {
                    x_polynomial_coeffs.push(<Bls12_381 as Pairing>::ScalarField::rand(&mut rng));
                }
                x_polynomials.push(UnivariatePolynomial::from_coefficients_slice(
                    &x_polynomial_coeffs,
                ));
            }
            bivariate_polynomials.push (BivariatePolynomial { x_polynomials });
        }

        // Commit to the polynomials
        let coms =
            TestBivariatePolyCommitment::commit(&srs.0, &bivariate_polynomials).unwrap();
        let mut prover_transcript : Transcript = Transcript::new(b"batch bivariate KZG at the same y");
        println!("com size is {} bytes", coms.len() * size_of_val(&coms[0]));

        // Evaluate at multiple challenge points
        let y_point = UniformRand::rand(&mut rng);
        let mut x_points = Vec::new();
        for i in 0..bivariate_polynomials.len() {
            if i%2 == 1 {
                // x_points.push(vec![UniformRand::rand(&mut rng)]);
                x_points.push(vec![UniformRand::rand(&mut rng), UniformRand::rand(&mut rng)]);
            }
            else {
                x_points.push(vec![UniformRand::rand(&mut rng), UniformRand::rand(&mut rng), UniformRand::rand(&mut rng)]);
            }
        }

        let eval_proof = TestBivariatePolyCommitment::open_lagrange_at_same_y(
            &srs.0,
            &bivariate_polynomials,
            &x_points,
            &y_point,
            &domain,
            &mut prover_transcript
        )
        .unwrap();

        let mut evals: Vec<Vec<<Bls12_381 as Pairing>::ScalarField>> = Vec::new();
        for i in 0..POLYNOMIAL_NUMBER {
            let mut eval_i = Vec::new();
            for j in 0..x_points[i].len() {
                let point = (x_points[i][j], y_point);
                let eval = bivariate_polynomials[i].evaluate_lagrange(&point, &domain);
                eval_i.push(eval);
            }
            evals.push(eval_i);
        }

        // proof size
        let proof_size = (eval_proof.1.len() + 1) * size_of_val(&<Bls12_381 as Pairing>::ScalarField::one()) + 4 * size_of_val(&eval_proof.0);
        println!("Proof size is {} bytes", proof_size);

        // Verify proof
        let mut verifier_transcript : Transcript = Transcript::new(b"batch bivariate KZG at the same y");
        assert!(
            TestBivariatePolyCommitment::verify_at_same_y(&srs.1, &coms, &x_points, &y_point, &evals, &eval_proof, &mut verifier_transcript).unwrap()
        );

    }

}
