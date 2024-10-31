use ark_bls12_381::Bls12_381;
use ark_ec::pairing::Pairing;
use ark_ff::UniformRand;
use my_kzg::biv_trivial_kzg::{BivariateKZG, BivariatePolynomial};
use ark_poly::polynomial::{
    univariate::DensePolynomial as UnivariatePolynomial, DenseUVPolynomial
};

use ark_std::rand::{rngs::StdRng, SeedableRng};

use std::time::{Duration, Instant};

fn main() {

    const BIVARIATE_X_LOG_DEGREE: usize = 10;
    const BIVARIATE_Y_LOG_DEGREE: usize = 10;
    let log_x_degree = 1 << BIVARIATE_X_LOG_DEGREE - 1;
    let log_y_degree = 1 << BIVARIATE_Y_LOG_DEGREE - 1;
    
    println!("Bivariate KZG, log_x_degree: {}, log_y_degree: {}", log_x_degree, log_y_degree);

    let mut rng = StdRng::seed_from_u64(0u64);

    let setup_start = Instant::now();
    let (g_alpha_powers, v_srs) =
        BivariateKZG::<Bls12_381>::setup(&mut rng, log_x_degree, log_y_degree).unwrap();
    let time = setup_start.elapsed().as_millis();
    println!("Bivariate KZG setup time: {:} ms", time);

    let mut x_polynomials = Vec::new();
    for _ in 0..log_y_degree + 1 {
        let mut x_polynomial_coeffs = vec![];
        for _ in 0..log_x_degree + 1 {
            x_polynomial_coeffs.push(<Bls12_381 as Pairing>::ScalarField::rand(&mut rng));
        }
        x_polynomials.push(UnivariatePolynomial::from_coefficients_slice(
            &x_polynomial_coeffs,
        ));
    }

    let x_poly_refs = x_polynomials.iter().collect::<Vec<_>>();
    let bivariate_polynomial = BivariatePolynomial { x_polynomials: &x_poly_refs };

    let point = (UniformRand::rand(&mut rng), UniformRand::rand(&mut rng));
    let eval = bivariate_polynomial.evaluate(&point);

    // Commit
    let com_start = Instant::now();
    let com = BivariateKZG::<Bls12_381>::commit(&g_alpha_powers, bivariate_polynomial).unwrap();
    let time = com_start.elapsed().as_millis();
    println!("Bivariate KZG commi time, {:?} ms", time);

    // Open
    let open_start = Instant::now();
    let proof = BivariateKZG::<Bls12_381>::open(&g_alpha_powers, bivariate_polynomial, &point).unwrap();
    let time = open_start.elapsed().as_millis();
    println!("Bivariate KZG open  time: {:?} ms", time);

    // Proof size
    let proof_size = size_of_val(&proof);
    println!("Bivariate KZG proof size: {:?} bytes", proof_size);

    // Verify
    std::thread::sleep(Duration::from_millis(5000));
    let verify_start = Instant::now();
    for _ in 0..50 {
        let is_valid =
            BivariateKZG::<Bls12_381>::verify(&v_srs, &com, &point, &eval, &proof).unwrap();
        assert!(is_valid);
    }
    let verify_time = verify_start.elapsed().as_millis() / 50;
    println!("Bivariate KZG verif time: {:?} ms", verify_time);
}

