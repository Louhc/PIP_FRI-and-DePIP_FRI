use ark_ec::{
    pairing::Pairing,
    CurveGroup, 
    Group,
    scalar_mul::variable_base::VariableBaseMSM,
    // scalar_mul::fixed_base::FixedBase,
};
use ark_ff::{One, Field, UniformRand, Zero};
use ark_poly::polynomial::{
    univariate::DensePolynomial as UnivariatePolynomial, DenseUVPolynomial, Polynomial,
};
use merlin::Transcript;

use crate::{transcript::ProofTranscript, trivial_kzg::structured_generators_scalar_power};

// use merlin::Transcript;
use std::marker::PhantomData;

use ark_std::rand::Rng;
// use digest::Digest;

use crate::{
    // transcript::ProofTranscript, 
    Error};

pub struct VerifierSRS<P: Pairing> {
    pub g: P::G1,
    pub h: P::G2,
    pub h_alpha: P::G2,
    pub h_beta: P::G2
}

pub struct BivariatePolynomial<F: Field> {
    pub x_polynomials: Vec<UnivariatePolynomial<F>>,
}

// We want \sum_i f_i(X) Y^{i-1}
impl<F: Field> BivariatePolynomial<F> {
    pub fn evaluate(&self, point: &(F, F)) -> F {
        let (x, y) = point;
        let mut point_y_powers = vec![];
        let mut cur = F::one();
        for _ in 0..(self.x_polynomials.len()) {
            point_y_powers.push(cur);
            cur *= y;
        }
        point_y_powers
            .iter()
            .zip(&self.x_polynomials)
            .map(|(y_power, x_polynomial)| y_power.clone() * x_polynomial.evaluate(&x))
            .sum()
    }
}

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
        let alpha = <P::ScalarField>::rand(rng);
        let beta = <P::ScalarField>::rand(rng);
        let g = <P::G1>::generator();
        let h = <P::G2>::generator();

        let mut final_srs: Vec<Vec<P::G1Affine>> = Vec::new();
        let mut temp = g;
        for _ in 0..(y_degree + 1) {
            let temp_srs = structured_generators_scalar_power(
                x_degree + 1,
                &temp,
                &alpha,
            );
            final_srs.push( <P as Pairing>::G1::normalize_batch(&temp_srs));
            temp *= beta;
        }

        Ok((final_srs,
            VerifierSRS {
                g: g.clone(),
                h: h.clone(),
                h_alpha: h * alpha,
                h_beta: h * beta
        }))
    }

    pub fn commit(
        powers: &Vec<Vec<P::G1Affine>>,
        bivariate_polynomials: &Vec<BivariatePolynomial<P::ScalarField>>,
    ) -> Result<Vec<P::G1>, Error> {
        assert!(powers.len() == bivariate_polynomials[0].x_polynomials.len());
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
        let mut evals_z1 = Vec::new();
        let mut combined_polynomial_q2 = UnivariatePolynomial::zero();
        let mut linear_factor = P::ScalarField::one();
        // generate q2(Y)
        // compute f_{j,i} (z1) and f_j (z1, Y)
        for j in 0..bivariate_polynomials.len() {
            let evals: Vec<P::ScalarField> = bivariate_polynomials[j].x_polynomials
                .iter()
                .map(|poly| poly.evaluate(&x))
                .collect();
            evals_z1.push(evals.clone());

            let combined_polynomial_slice_q2 = &UnivariatePolynomial::from_coefficients_vec(evals.clone()) * linear_factor;
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
        let left = P::pairing(linear_combination.clone(), v_srs.h.clone());
        let right1 = P::pairing(proof.0.clone(), v_srs.h_alpha.clone() - v_srs.h * x);
        let right2 = P::pairing(proof.1.clone(), v_srs.h_beta.clone() - v_srs.h * y);

        Ok(left == right1 + right2)
    }
}


#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_381::Bls12_381;
    use ark_std::rand::{rngs::StdRng, SeedableRng};
    use ark_poly::DenseUVPolynomial;
    // use blake2::Blake2b;

    const BIVARIATE_X_DEGREE: usize = 8;
    const BIVARIATE_Y_DEGREE: usize = 6;
    const POLYNOMIAL_NUMBER: usize = 3;
    //const UNIVARIATE_DEGREE: usize = 56;
    //const UNIVARIATE_DEGREE: usize = 65535;
    //const UNIVARIATE_DEGREE: usize = 1048575;

    type TestBivariatePolyCommitment = BivariateBatchKZG<Bls12_381>;
    // type TestUnivariatePolyCommitment = UnivariatePolynomialCommitment<Bls12_381, Blake2b>;

    #[test]
    fn bivariate_poly_commit_test() {
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

}
