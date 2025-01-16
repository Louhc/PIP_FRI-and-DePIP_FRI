use ark_ec::pairing::Pairing;
use ark_bls12_381::Bls12_381;
use ark_poly::polynomial::{univariate::DensePolynomial as UnivariatePolynomial, DenseUVPolynomial};
use ark_std::rand::{rngs::StdRng, SeedableRng};
use ark_std::UniformRand;
use my_snark::par_join_4;
use std::time::Instant;
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain};

fn main() {

let log_sizes = vec![12, 14, 16, 18, 20];
    let mut rng = StdRng::seed_from_u64(0u64);

    for &log_size in &log_sizes {
        let x_degree = (1 << log_size) - 1;
        let x_domain = <GeneralEvaluationDomain<<Bls12_381 as Pairing>::ScalarField> as EvaluationDomain<<Bls12_381 as Pairing>::ScalarField>>::new(x_degree).unwrap();

        // generate bivariate polynomials
        let mut x_polynomial_coeffs = vec![];
        for _ in 0..x_degree + 1 {
            x_polynomial_coeffs.push(<Bls12_381 as Pairing>::ScalarField::rand(&mut rng));
        }
        let x_polynomial = UnivariatePolynomial::from_coefficients_slice(
            &x_polynomial_coeffs
        );  
        let x_polynomial_coeffs = x_polynomial.coeffs.to_vec();

        // trivial fft
        let time = Instant::now();
        let _ = x_polynomial.evaluate_over_domain(x_domain);
        println!("Trivial fft time is: {:?}", time.elapsed());

        let l = (x_degree + 1) / 4;
        let sub_domain  = <GeneralEvaluationDomain<<Bls12_381 as Pairing>::ScalarField> as EvaluationDomain<<Bls12_381 as Pairing>::ScalarField>>::new(x_degree / 4).unwrap();
        let coeffs_0 = x_polynomial_coeffs[0..l].to_vec();
        let coeffs_1 = x_polynomial_coeffs[l..2 * l].to_vec();
        let coeffs_2 = x_polynomial_coeffs[2 * l..3 * l].to_vec();
        let coeffs_3 = x_polynomial_coeffs[3 * l..4 * l].to_vec();

        let poly_0 = UnivariatePolynomial::from_coefficients_vec(coeffs_0);
        let poly_1 = UnivariatePolynomial::from_coefficients_vec(coeffs_1);
        let poly_2 = UnivariatePolynomial::from_coefficients_vec(coeffs_2);
        let poly_3 = UnivariatePolynomial::from_coefficients_vec(coeffs_3);

        // sub-ffts without multicores
        let time = Instant::now();
        let (_, _, _, _) = par_join_4!(
            || poly_0.evaluate_over_domain(sub_domain),
            || poly_1.evaluate_over_domain(sub_domain),
            || poly_2.evaluate_over_domain(sub_domain),
            || poly_3.evaluate_over_domain(sub_domain)
        );
        println!("Multi core fft time is: {:?}", time.elapsed());

    }

}