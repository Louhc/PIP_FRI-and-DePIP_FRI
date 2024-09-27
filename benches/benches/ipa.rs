use ark_bls12_381::Bls12_381;
use ark_ec::pairing::Pairing;
use my_ipa::sumcheck::SUMCHECK;
use my_kzg::{
    batch_kzg::BatchKZG,
    trivial_kzg::KZG
};
use ark_poly::{
    univariate::DensePolynomial as UnivariatePolynomial, DenseUVPolynomial, EvaluationDomain,
    GeneralEvaluationDomain
};

use ark_std::rand::{rngs::StdRng, SeedableRng};

use std::time::{Duration, Instant};
use merlin::Transcript;

// This is the benchmark for univariate batch KZG on opening one point on multiple polynomials
fn main() {

    let size: usize = 1 << 19;
    let degree: usize = (1 << 20) - 1;
    let mut rng = StdRng::seed_from_u64(0u64);
    let domain = 
        <GeneralEvaluationDomain<<Bls12_381 as Pairing>::ScalarField> as EvaluationDomain<<Bls12_381 as Pairing>::ScalarField>>::new(size).unwrap();
    let polynomial = UnivariatePolynomial::rand(degree, &mut rng);
    let sum = SUMCHECK::<Bls12_381>::get_sum_on_domain(&polynomial, &domain);
    let (g_alpha_powers, v_srs) = BatchKZG::<Bls12_381>::setup(&mut rng, degree).unwrap();

    // Sumcheck prover
    let prover_start = Instant::now();
    let mut prover_transcript : Transcript = Transcript::new(b"Trivial sumcheck");
    let com = SUMCHECK::<Bls12_381>::sumcheck_commit(&g_alpha_powers, &polynomial).unwrap();

    let proof = SUMCHECK::<Bls12_381>::sumcheck_prove(&g_alpha_powers, &polynomial, &com, &sum, &domain, &mut prover_transcript).unwrap();
    println!("Trivial sumcheck prover time: {:?} ms", prover_start.elapsed().as_millis());

    // Sumcheck proof size
    let proof_size = SUMCHECK::<Bls12_381>::get_proof_size(&proof);
    println!("Trivial sumcheck proof size: {:?} bytes", proof_size);

    // Sumcheck verifier
    std::thread::sleep(Duration::from_millis(5000));
    let verify_start = Instant::now();
    for _ in 0..50 {
        let mut verifier_transcript : Transcript = Transcript::new(b"Trivial sumcheck");
        let is_valid = 
            SUMCHECK::<Bls12_381>::sumcheck_verify(&v_srs, &com, &domain, &sum, &proof, &mut verifier_transcript).unwrap();
        assert!(is_valid);
    }
    let verify_time = verify_start.elapsed().as_millis() / 50;
    println!("Trivial sumcheck verifier time: {:?} ms", verify_time);

    // Below is the Sumcheck without ldt
    // (x-u)f(x) = x*g(x) + sum/|domain| (x-u) + Z_H(x)h(x)(x-u)
    // Sumcheck prover
    let prover_start = Instant::now();
    let mut transcript : Transcript = Transcript::new(b"No_ldt sumcheck");
    let com = KZG::<Bls12_381>::commit(&g_alpha_powers, &polynomial).unwrap();

    let proof = SUMCHECK::<Bls12_381>::sumcheck_no_ldt_prove(&g_alpha_powers, &polynomial, &com, &sum, &domain, &mut transcript).unwrap();
    println!("No_ldt sumcheck prover time: {:?} ms", prover_start.elapsed().as_millis());

    // Sumcheck proof size
    let proof_size = SUMCHECK::<Bls12_381>::get_proof_size(&proof);
    println!("No_ldt sumcheck proof size: {:?} bytes", proof_size);

    // Sumcheck verifier
    std::thread::sleep(Duration::from_millis(5000));
    let verify_start = Instant::now();
    for _ in 0..50 {
        let mut transcript : Transcript = Transcript::new(b"No_ldt sumcheck");
        let is_valid =
            SUMCHECK::<Bls12_381>::sumcheck_no_ldt_verify(&v_srs, &com, &domain, &sum, &proof, &mut transcript).unwrap();
        assert!(is_valid);
    }

    let verify_time = verify_start.elapsed().as_millis()/50;
    println!("No_ldt sumcheck verifier time: {:?} ms", verify_time);
}

