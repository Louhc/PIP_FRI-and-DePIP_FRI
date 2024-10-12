use ark_ec::{
    pairing::Pairing,
    CurveGroup, 
    Group,
    scalar_mul::variable_base::VariableBaseMSM,
    // scalar_mul::fixed_base::FixedBase,
};
use ark_ff::{One, Field, UniformRand, Zero, FftField};
use ark_poly::{polynomial::{
    univariate::DensePolynomial as UnivariatePolynomial, Polynomial,
    }, DenseUVPolynomial, EvaluationDomain, 
    Evaluations, 
    GeneralEvaluationDomain};

use crate::trivial_kzg::structured_generators_scalar_power;
use crate::trivial_kzg::KZG;

use std::marker::PhantomData;

use ark_std::rand::Rng;
// use ark_std::rand::{rngs::StdRng, SeedableRng};
// use digest::Digest;

use crate::Error;

pub struct VerifierSRS<P: Pairing> {
    pub g: P::G1,
    pub h: P::G2,
    pub h_alpha: P::G2,
    pub h_beta: P::G2
}

pub struct BivariatePolynomial<F: Field> {
    pub x_polynomials: Vec<UnivariatePolynomial<F>>,
}

// Here is \sum_i f_i(X) Y^{i-1}
// We want sum_i f_i(X) L_i(Y)
impl<F: FftField> BivariatePolynomial<F> {
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

    pub fn evaluate_lagrange(&self, point: &(F, F), domain: &GeneralEvaluationDomain<F>) -> F {
        let (x, y) = point;
        let y_evals = EvaluationDomain::evaluate_all_lagrange_coefficients(domain, *y);

        y_evals
            .iter()
            .zip(&self.x_polynomials)
            .map(|(y_eval, x_polynomial)| y_eval.clone() * x_polynomial.evaluate(&x))
            .sum()
    }

    pub fn evaluate_at_y_lagrange(&self, point: &F, domain: &GeneralEvaluationDomain<F>) -> UnivariatePolynomial<F> {
        let y = point;
        let y_evals = EvaluationDomain::evaluate_all_lagrange_coefficients(domain, *y);
        let mut result_polynomial = UnivariatePolynomial::from_coefficients_vec(vec![F::zero()]);

        for i in 0..self.x_polynomials.len() {
            result_polynomial += (y_evals[i], &self.x_polynomials[i]);
        }
        result_polynomial
    }
}

pub struct BivariateKZG<P: Pairing> {
    _pairing: PhantomData<P>,
}

impl<P: Pairing> BivariateKZG<P> {
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

    pub fn setup_lagrange<R: Rng>(
        rng: &mut R,
        x_degree: usize,
        y_degree: usize,
        domain: &GeneralEvaluationDomain<P::ScalarField>
    ) -> Result<(Vec<Vec<P::G1Affine>>, VerifierSRS<P>), Error> {
        let beta = EvaluationDomain::sample_element_outside_domain(domain, rng);
        let alpha = <P::ScalarField>::rand(rng);
        let g = <P::G1>::generator();
        let h = <P::G2>::generator();
        assert!((y_degree + 1).is_power_of_two());

        let mut final_srs: Vec<Vec<P::G1Affine>> = Vec::new();
        let y_evals = EvaluationDomain::evaluate_all_lagrange_coefficients(domain, beta);
        assert_eq!(y_evals.len(), y_degree+1);
        for i in 0..(y_degree + 1) {
            let temp_srs = structured_generators_scalar_power(
                x_degree + 1,
                &(g * y_evals[i]),
                &alpha,
            );
            final_srs.push( <P as Pairing>::G1::normalize_batch(&temp_srs));
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
        bivariate_polynomial: &BivariatePolynomial<P::ScalarField>,
    ) -> Result<P::G1, Error> {
        assert!(powers.len() == bivariate_polynomial.x_polynomials.len());
        assert!(powers[0].len() >= bivariate_polynomial.x_polynomials[0].degree() + 1);

        let mut extended_coeff: Vec<<P as Pairing>::ScalarField> = Vec::new();
        let mut extended_powers: Vec<<P as Pairing>::G1Affine> = Vec::new();

        for i in 0..powers.len() {
            let mut coeffs = bivariate_polynomial.x_polynomials[i].coeffs.to_vec();
            coeffs.resize(powers[0].len(), <P::ScalarField>::zero());
            extended_coeff.extend(&coeffs);

            extended_powers.extend(&powers[i]);
        }
        
        Ok(P::G1::msm(&extended_powers, &extended_coeff).unwrap())
    }

    /// Seems no changes
    pub fn commit_lagrange(
        powers: &Vec<Vec<P::G1Affine>>,
        bivariate_polynomial: &BivariatePolynomial<P::ScalarField>,
    ) -> Result<P::G1, Error> {
        assert!(powers.len() == bivariate_polynomial.x_polynomials.len());
        assert!(powers.len().is_power_of_two());
        assert!(powers[0].len() >= bivariate_polynomial.x_polynomials[0].degree() + 1);

        let mut extended_coeff: Vec<<P as Pairing>::ScalarField> = Vec::new();
        let mut extended_powers: Vec<<P as Pairing>::G1Affine> = Vec::new();

        for i in 0..powers.len() {
            let mut coeffs = bivariate_polynomial.x_polynomials[i].coeffs.to_vec();
            coeffs.resize(powers[0].len(), <P::ScalarField>::zero());
            extended_coeff.extend(&coeffs);

            extended_powers.extend(&powers[i]);
        }
        
        Ok(P::G1::msm(&extended_powers, &extended_coeff).unwrap())
    }

    pub fn open(
        powers: &Vec<Vec<P::G1Affine>>,
        bivariate_polynomial: &BivariatePolynomial<P::ScalarField>,
        point: &(P::ScalarField, P::ScalarField),
    ) -> Result<(P::G1, P::G1), Error> {
        // generate q1(x,y) and q2(y)
        // see f(x,y) - f(z1,z2) = f(x,y) - f(z1,y) + f(z1,y) - f(z1,z2)
        // q1(x,y) = f(x,y)-f(z1,y)/(x-z1) = \sum_i [(f_{i}(x)-f_{i}(z1))/(x-z1)] \cdot y^{i-1}
        // q2(y) = f(z1,y) - f(z1,z2) / (y - z2)

        let (x, y) = point;
        let y_srs: Vec<<P as Pairing>::G1Affine> = powers.iter()
            .filter_map(|row| row.get(0))
            .cloned()
            .collect();

        // compute the vector composed by (f_1(z1), f_2(z1), ..., f_l(z1))
        let evals_z1: Vec<P::ScalarField> = bivariate_polynomial.x_polynomials
            .iter()
            .map(|poly| poly.evaluate(&x))
            .collect();

        // the concatenation of the q1(x,y)
        let mut coeffs_q1: Vec<<P as Pairing>::ScalarField> = Vec::new();
        let mut xy_srs: Vec<<P as Pairing>::G1Affine> = Vec::new();

        for i in 0..y_srs.len() {
            // f_i(x) / (x-z1), trick: no need to divide f_i(z1)
            let polynomial_slice_q1 = &bivariate_polynomial.x_polynomials[i]
                / &UnivariatePolynomial::from_coefficients_vec(vec![
                    -x.clone(),
                    P::ScalarField::one()
                ]);
            let mut coeffs_slice_q1 = polynomial_slice_q1.coeffs.to_vec();
            coeffs_slice_q1.resize(powers[0].len(), <P::ScalarField>::zero());
            
            coeffs_q1.extend(&coeffs_slice_q1);
            xy_srs.extend(&powers[i]);
        }
        // let quotient_polynomial_y = BivariatePolynomial { x_polynomials };

        let polynomial_q2 = &UnivariatePolynomial::from_coefficients_vec(evals_z1) 
            / &UnivariatePolynomial::from_coefficients_vec(vec![
                -y.clone(),
                P::ScalarField::one(),
            ]);
        let mut coeffs_q2 = polynomial_q2.coeffs.to_vec();
        coeffs_q2.resize(y_srs.len(), <P::ScalarField>::zero());

        let proof = (
            P::G1::msm(&xy_srs, &coeffs_q1).unwrap(), 
            P::G1::msm(&y_srs, &coeffs_q2).unwrap());
        
        Ok(proof)
    }

    pub fn open_lagrange(
        powers: &Vec<Vec<P::G1Affine>>,
        bivariate_polynomial: &BivariatePolynomial<P::ScalarField>,
        point: &(P::ScalarField, P::ScalarField),
        domain: &GeneralEvaluationDomain<P::ScalarField>,
    ) -> Result<(P::G1, P::G1), Error> {
        // generate q1(x,y) and q2(y)
        // see f(x,y) - f(z1,z2) = f(x,y) - f(z1,y) + f(z1,y) - f(z1,z2)
        // q1(x,y) = f(x,y)-f(z1,y)/(x-z1) = \sum_i [(f_{i}(x)-f_{i}(z1))/(x-z1)] \cdot L_i(Y)
        // f2(y) is defined by [f_i(z1)], should invoke the KZG::open_lagrange

        let (x, y) = point;
        let y_srs: Vec<<P as Pairing>::G1Affine> = powers.iter()
            .filter_map(|row| row.get(0))
            .cloned()
            .collect();
        assert_eq!(y_srs.len(), domain.size());
        assert_eq!(y_srs.len(), powers.len());

        // the concatenation of the q1(x,y)
        let mut coeffs_q1: Vec<<P as Pairing>::ScalarField> = Vec::new();
        let mut xy_srs: Vec<<P as Pairing>::G1Affine> = Vec::new();

        for i in 0..y_srs.len() {
            // f_i(x) / (x-z1), trick: no need to divide f_i(z1)
            let polynomial_slice_q1 = &bivariate_polynomial.x_polynomials[i]
                / &UnivariatePolynomial::from_coefficients_vec(vec![
                    -x.clone(),
                    P::ScalarField::one()
                ]);
            let mut coeffs_slice_q1 = polynomial_slice_q1.coeffs.to_vec();
            coeffs_slice_q1.resize(powers[0].len(), <P::ScalarField>::zero());
            
            coeffs_q1.extend(&coeffs_slice_q1);
            xy_srs.extend(&powers[i]);
        }

        // compute the vector composed by (f_1(z1), f_2(z1), ..., f_l(z1))
        let evals_z1: Vec<P::ScalarField> = bivariate_polynomial.x_polynomials
            .iter()
            .map(|poly| poly.evaluate(&x))
            .collect();
        let evals_z1_eval = Evaluations::<P::ScalarField>::from_vec_and_domain(evals_z1.clone(), domain.clone());
     
        let coeffs_q2 = KZG::<P>::get_quotient_eval_lagrange(&evals_z1_eval, &y, &domain);
        assert_eq!(coeffs_q2.len(), y_srs.len());
        let proof = (
            P::G1::msm(&xy_srs, &coeffs_q1).unwrap(), 
            P::G1::msm(&y_srs, &coeffs_q2).unwrap());
        
        Ok(proof)
    }

    pub fn verify(
        v_srs: &VerifierSRS<P>,
        com: &P::G1,
        point: &(P::ScalarField, P::ScalarField),
        eval: &P::ScalarField,
        proof: &(P::G1, P::G1),
    ) -> Result<bool, Error> {
        let (x, y) = point;
        let left = P::pairing(com.clone() - v_srs.g * eval, v_srs.h.clone());
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
    const BIVARIATE_X_DEGREE: usize = 10;
    const BIVARIATE_Y_DEGREE: usize = 15;

    type TestBivariatePolyCommitment = BivariateKZG<Bls12_381>;
    // type TestUnivariatePolyCommitment = UnivariatePolynomialCommitment<Bls12_381, Blake2b>;

    #[test]
    fn bivariate_poly_commit_test() {
        let mut rng = StdRng::seed_from_u64(0u64);
        let srs =
            TestBivariatePolyCommitment::setup(&mut rng, BIVARIATE_X_DEGREE, BIVARIATE_Y_DEGREE)
                .unwrap();

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
        let bivariate_polynomial = BivariatePolynomial { x_polynomials };

        // Commit to polynomial
        let com =
            TestBivariatePolyCommitment::commit(&srs.0, &bivariate_polynomial).unwrap();

        // Evaluate at challenge point
        let point = (UniformRand::rand(&mut rng), UniformRand::rand(&mut rng));
        let eval_proof = TestBivariatePolyCommitment::open(
            &srs.0,
            &bivariate_polynomial,
            &point
        )
        .unwrap();
        let eval = bivariate_polynomial.evaluate(&point);

        // proof size
        println!("Proof size is {} bytes", size_of_val(&eval_proof));

        // Verify proof
        assert!(
            TestBivariatePolyCommitment::verify(&srs.1, &com, &point, &eval, &eval_proof).unwrap()
        );
    }

    #[test]
    fn bivariate_poly_commit_lagrange_test() {
        let mut rng = StdRng::seed_from_u64(0u64);
        let domain = <GeneralEvaluationDomain<<Bls12_381 as Pairing>::ScalarField> as EvaluationDomain<<Bls12_381 as Pairing>::ScalarField>>::new(BIVARIATE_Y_DEGREE+1).unwrap();
        let srs =
            TestBivariatePolyCommitment::setup_lagrange(&mut rng, BIVARIATE_X_DEGREE, BIVARIATE_Y_DEGREE, &domain).unwrap();
        // let v_srs = srs.0.get_verifier_key();

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
        let bivariate_polynomial = BivariatePolynomial { x_polynomials };

        // Commit to polynomial
        let com =
            TestBivariatePolyCommitment::commit_lagrange(&srs.0, &bivariate_polynomial).unwrap();

        // Evaluate at challenge point
        let point = (UniformRand::rand(&mut rng), UniformRand::rand(&mut rng));
        let eval = bivariate_polynomial.evaluate_lagrange(&point, &domain);
        let eval_proof = TestBivariatePolyCommitment::open_lagrange(
            &srs.0,
            &bivariate_polynomial,
            &point,
            &domain,
        ).unwrap();

        // proof size
        println!("Proof size is {} bytes", size_of_val(&eval_proof));

        // Verify proof
        assert!(
            TestBivariatePolyCommitment::verify(&srs.1, &com, &point, &eval, &eval_proof).unwrap()
        );

    }

}
