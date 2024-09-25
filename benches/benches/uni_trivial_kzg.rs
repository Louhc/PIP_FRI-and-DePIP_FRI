use ark_bls12_381::Bls12_381;
use ark_ec::pairing::Pairing;
use ark_ff::UniformRand;
use my_kzg::trivial_kzg::KZG;
use ark_poly::polynomial::{
    univariate::DensePolynomial as UnivariatePolynomial, DenseUVPolynomial, Polynomial,
};

use ark_std::rand::{rngs::StdRng, SeedableRng};

use std::time::{Duration, Instant};

fn main() {

    let log_degree = 20;
    let degree = (1 << log_degree) - 1;
    // let repeat: usize = 1;
    let mut rng = StdRng::seed_from_u64(0u64);

    let setup_start = Instant::now();
    let (g_alpha_powers, v_srs) = KZG::<Bls12_381>::setup(&mut rng, degree).unwrap();
    let time = setup_start.elapsed().as_millis();
    println!("KZG setup time, {:} log_degree: {:} ms", log_degree, time);

    // for _ in 0..repeat {
    let polynomial = UnivariatePolynomial::rand(degree, &mut rng);
    let point = <Bls12_381 as Pairing>::ScalarField::rand(&mut rng);
    let eval = polynomial.evaluate(&point);

    // Commit
    let com_start = Instant::now();
    let com = KZG::<Bls12_381>::commit(&g_alpha_powers, &polynomial).unwrap();
    let time = com_start.elapsed().as_millis();
    println!("KZG commi time, {:} log_degree: {:?} ms", log_degree, time);

    // Open
    let open_start = Instant::now();
    let proof = KZG::<Bls12_381>::open(&g_alpha_powers, &polynomial, &point).unwrap();
    let time = open_start.elapsed().as_millis();
    println!("KZG open  time, {:} log_degree: {:?} ms", log_degree, time);

    // Proof size
    let proof_size = size_of_val(&proof);
    println!("KZG proof size, {:} log_degree: {:?} bytes", log_degree, proof_size);

    // Verify
    std::thread::sleep(Duration::from_millis(5000));
    let verify_start = Instant::now();
    for _ in 0..50 {
        let is_valid =
            KZG::<Bls12_381>::verify(&v_srs, &com, &point, &eval, &proof).unwrap();
        assert!(is_valid);
    }
    let verify_time = verify_start.elapsed().as_millis() / 50;
    println!("KZG verif time, {:} log_degree: {:?} ms", log_degree, verify_time);
}

