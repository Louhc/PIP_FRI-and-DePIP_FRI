use ark_bls12_381::Bls12_381;
use ark_ec::pairing::Pairing;
use ark_ff::UniformRand;
use my_kzg::batch_kzg::BatchKZG;
use ark_poly::polynomial::{
    univariate::DensePolynomial as UnivariatePolynomial, DenseUVPolynomial, Polynomial,
};

use ark_std::rand::{rngs::StdRng, SeedableRng};

use std::time::{Duration, Instant};
use merlin::Transcript;

// This is the benchmark for univariate batch KZG on opening one point on multiple polynomials
fn main() {

    let log_degree = 12;
    let poly_num = 4;
    let degree = (1 << log_degree) - 1;
    // let repeat: usize = 1;
    let mut rng = StdRng::seed_from_u64(0u64);

    let setup_start = Instant::now();
    let (g_alpha_powers, v_srs) = BatchKZG::<Bls12_381>::setup(&mut rng, degree).unwrap();
    let time = setup_start.elapsed().as_millis();
    println!("BatchKZG setup time, {:} log_degree: {:} ms", log_degree, time);

    let mut polynomials = Vec::new();
    let mut evals = Vec::new();
    let point = <Bls12_381 as Pairing>::ScalarField::rand(&mut rng);

    for _ in 0..poly_num {
        let polynomial = UnivariatePolynomial::rand(degree, &mut rng);
        let eval = polynomial.evaluate(&point);
        polynomials.push(polynomial);
        evals.push(eval);
    }

    // Commit
    let com_start = Instant::now();
    let coms = BatchKZG::<Bls12_381>::commit(&g_alpha_powers, &polynomials).unwrap();
    
    // let com = KZG::<Bls12_381>::commit(&g_alpha_powers, &polynomial).unwrap();
    println!("BatchKZG commi time, {:} log_degree: {:?} ms", log_degree, com_start.elapsed().as_millis());
    println!("BatchKZG commi size, {:} log_degree: {:?} bytes", log_degree, size_of_val(&coms[0])*coms.len());

    // Open
    let mut prover_transcript: Transcript = Transcript::new(b"batch univariate KZG");
    let open_start = Instant::now();
    let proofs = BatchKZG::<Bls12_381>::open(&g_alpha_powers, &polynomials, &point, &mut prover_transcript).unwrap();
    // let proof = KZG::<Bls12_381>::open(&g_alpha_powers, &polynomial, &point,).unwrap();
    println!("BatchKZG open  time, {:} log_degree: {:?} ms", log_degree, open_start.elapsed().as_millis());

    // Proof size
    let proof_size = size_of_val(&proofs);
    println!("BatchKZG proof size, {:} log_degree: {:?} bytes", log_degree, proof_size);

    // Verify
    std::thread::sleep(Duration::from_millis(5000));
    let verifier_transcript: Transcript = Transcript::new(b"batch univariate KZG");
    let verify_start = Instant::now();
    for _ in 0..50 {
        let is_valid =
            BatchKZG::<Bls12_381>::verify(&v_srs, &coms, &point, &evals, &proofs, &mut verifier_transcript.clone()).unwrap();
        assert!(is_valid);
    }
    let verify_time = verify_start.elapsed().as_millis() / 50;
    println!("BatchKZG verif time, {:} log_degree: {:?} ms", log_degree, verify_time);
}

