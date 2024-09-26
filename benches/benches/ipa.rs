use ark_bls12_381::Bls12_381;
use ark_ec::pairing::Pairing;
use my_ipa::sumcheck::SUMCHECK;
use my_kzg::{
    batch_kzg::BatchKZG,
    trivial_kzg::KZG,
    transcript::ProofTranscript,
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
    let degree: usize = 1 << 20 - 1;
    let mut rng = StdRng::seed_from_u64(0u64);
    let domain = 
        <GeneralEvaluationDomain<<Bls12_381 as Pairing>::ScalarField> as EvaluationDomain<<Bls12_381 as Pairing>::ScalarField>>::new(size).unwrap();
    let polynomial = UnivariatePolynomial::rand(degree, &mut rng);
    let sum = SUMCHECK::<Bls12_381>::get_sum_on_domain(&polynomial, &domain);
    let (g_alpha_powers, v_srs) = BatchKZG::<Bls12_381>::setup(&mut rng, degree).unwrap();

    // Sumcheck prover
    let prover_start = Instant::now();
    let mut prover_transcript : Transcript = Transcript::new(b"Trivial sumcheck");
    let com = KZG::<Bls12_381>::commit(&g_alpha_powers, &polynomial).unwrap();

    let (g, h, g_prime) = SUMCHECK::<Bls12_381>::get_g_h_g_prime(&polynomial, &sum, &domain);
    let helper_polynomials = vec![g, h, g_prime];
    let helper_coms = BatchKZG::<Bls12_381>::commit(&g_alpha_powers, &helper_polynomials).unwrap();

    // generate eta using fiat-shamir
    let mut slice_vector = helper_coms.clone();
    slice_vector.push(com.clone());
    let slice: &[<Bls12_381 as Pairing>::G1] = &slice_vector;
    <Transcript as ProofTranscript<Bls12_381>>::append_points(&mut prover_transcript, b"add commitments", slice);
    let alpha = <Transcript as ProofTranscript<Bls12_381>>::challenge_scalar(
        &mut prover_transcript, b"random_evaluate_point");

    let proof = SUMCHECK::<Bls12_381>::prove(&g_alpha_powers, &polynomial, &helper_polynomials, &alpha, &mut prover_transcript).unwrap();
    println!("Trivial sumcheck prover time: {:?} ms", prover_start.elapsed().as_millis());

    // Sumcheck proof size
    let proof_size = SUMCHECK::<Bls12_381>::get_proof_size(&proof);
    println!("Trivial sumcheck proof size: {:?} bytes", proof_size);

    // Sumcheck verifier
    std::thread::sleep(Duration::from_millis(5000));
    let verify_start = Instant::now();
    for _ in 0..50 {
        let mut verifier_transcript : Transcript = Transcript::new(b"Trivial sumcheck");
        let mut slice_vector = helper_coms.clone();
        slice_vector.push(com.clone());
        let slice: &[<Bls12_381 as Pairing>::G1] = &slice_vector;
        <Transcript as ProofTranscript<Bls12_381>>::append_points(&mut verifier_transcript, b"add commitments", slice);
        let alpha = <Transcript as ProofTranscript<Bls12_381>>::challenge_scalar(
            &mut verifier_transcript, b"random_evaluate_point");
        let is_valid =
            SUMCHECK::<Bls12_381>::verify(&v_srs, &com, &helper_coms, &alpha, &domain, &sum, &proof, &mut verifier_transcript).unwrap();
        assert!(is_valid);
    }
    let verify_time = verify_start.elapsed().as_millis() / 50;
    println!("Trivial sumcheck verifier time: {:?} ms", verify_time);

     // (x-u)f(x) = x*g(x) + sum/|domain| (x-u) + Z_H(x)h(x)(x-u)
    // Sumcheck prover
    let prover_start = Instant::now();
    let mut transcript : Transcript = Transcript::new(b"No_ldt sumcheck");
    let com = KZG::<Bls12_381>::commit(&g_alpha_powers, &polynomial).unwrap();

    <Transcript as ProofTranscript<Bls12_381>>::append_point(&mut transcript, b"add the first commitment", &com);
    let u = <Transcript as ProofTranscript<Bls12_381>>::challenge_scalar(
        &mut transcript, b"generate challenge u to eliminate ldt");
    
    let (g_u, h) = SUMCHECK::<Bls12_381>::get_g_mul_u_and_h(&polynomial, &u, &sum, &domain);
    let helper_polynomials = vec![g_u.clone(), h.clone()];
    let helper_coms = BatchKZG::<Bls12_381>::commit(&g_alpha_powers, &helper_polynomials).unwrap();

    // generate alpha using fiat-shamir
    let mut slice_vector = helper_coms.clone();
    slice_vector.push(com.clone());
    let slice: &[<Bls12_381 as Pairing>::G1] = &slice_vector;
    <Transcript as ProofTranscript<Bls12_381>>::append_points(&mut transcript, b"add commitments", slice);
    let alpha = <Transcript as ProofTranscript<Bls12_381>>::challenge_scalar(
        &mut transcript, b"generate challenge alpha for evaluation");

    let proof = SUMCHECK::<Bls12_381>::prove(&g_alpha_powers, &polynomial, &helper_polynomials, &alpha, &mut transcript).unwrap();
    println!("No_ldt sumcheck prover time: {:?} ms", prover_start.elapsed().as_millis());

    // Sumcheck proof size
    let proof_size = SUMCHECK::<Bls12_381>::get_proof_size(&proof);
    println!("No_ldt sumcheck proof size: {:?} bytes", proof_size);

    // Sumcheck verifier
    std::thread::sleep(Duration::from_millis(5000));
    let verify_start = Instant::now();
    for _ in 0..50 {
        let mut transcript : Transcript = Transcript::new(b"No_ldt sumcheck");
        <Transcript as ProofTranscript<Bls12_381>>::append_point(&mut transcript, b"add the first commitment", &com);
        let u = <Transcript as ProofTranscript<Bls12_381>>::challenge_scalar(
            &mut transcript, b"generate challenge u to eliminate ldt");
        let mut slice_vector = helper_coms.clone();
        slice_vector.push(com.clone());
        let slice: &[<Bls12_381 as Pairing>::G1] = &slice_vector;
        <Transcript as ProofTranscript<Bls12_381>>::append_points(&mut transcript, b"add commitments", slice);
        let alpha = <Transcript as ProofTranscript<Bls12_381>>::challenge_scalar(
            &mut transcript, b"generate challenge alpha for evaluation");
        let is_valid =
            SUMCHECK::<Bls12_381>::verify_no_ldt(&v_srs, &com, &helper_coms, &u, &alpha, &domain, &sum, &proof, &mut transcript).unwrap();
        assert!(is_valid);
    }

    let verify_time = verify_start.elapsed().as_millis()/50;
    println!("No_ldt sumcheck verifier time: {:?} ms", verify_time);
}

