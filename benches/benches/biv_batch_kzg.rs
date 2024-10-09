use ark_ec::pairing::Pairing;
use ark_bls12_381::Bls12_381;
use ark_ff::{UniformRand, One};
use my_kzg::biv_trivial_kzg::{BivariateKZG, BivariatePolynomial};
use my_kzg::biv_batch_kzg::BivBatchKZG;
use ark_poly::polynomial::{
    univariate::DensePolynomial as UnivariatePolynomial, DenseUVPolynomial,
};
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain};
use ark_std::rand::{rngs::StdRng, SeedableRng};
use my_kzg::helper::get_x_srs;
use std::time::{Duration, Instant};
use merlin::Transcript;
use my_kzg::transcript::ProofTranscript;

fn main() {

    const BIVARIATE_X_LOG_DEGREE: usize = 10;
    const BIVARIATE_Y_LOG_DEGREE: usize = 7;
    const POLYNOMIAL_NUMBER: usize = 4;
    const X_POINT_NUMBER: usize = 2;
    let log_x_degree = (1 << BIVARIATE_X_LOG_DEGREE) - 1;
    let log_y_degree = (1 << BIVARIATE_Y_LOG_DEGREE) - 1;
    let total_point_number = POLYNOMIAL_NUMBER * X_POINT_NUMBER;
    
    println!("Bivariate KZG, log_x_degree: {}, log_y_degree: {}, polynomial_number: {}, total_points: {}",
        log_x_degree, log_y_degree, POLYNOMIAL_NUMBER, total_point_number);

    let mut rng = StdRng::seed_from_u64(0u64);
    let domain = <GeneralEvaluationDomain<<Bls12_381 as Pairing>::ScalarField> as EvaluationDomain<<Bls12_381 as Pairing>::ScalarField>>::new(log_y_degree + 1).unwrap();

    // Setup
    let setup_start = Instant::now();
    let (g_alpha_powers, v_srs) =
        BivariateKZG::<Bls12_381>::setup(&mut rng, log_x_degree, log_y_degree).unwrap();
    let powers = &g_alpha_powers;
    let x_srs = get_x_srs::<Bls12_381>(&powers);
    let time = setup_start.elapsed().as_millis();
    println!("Bivariate KZG setup time: {:} ms", time);

    // Commit
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
    let bivariate_polynomial = BivariatePolynomial { x_polynomials };
    let com_start = Instant::now();
    let com = BivariateKZG::<Bls12_381>::commit(&g_alpha_powers, &bivariate_polynomial).unwrap();
    let time = com_start.elapsed().as_millis();
    println!("Bivariate KZG commi time, {:?} ms", time * POLYNOMIAL_NUMBER as u128);

    // Open
    let point = (UniformRand::rand(&mut rng), UniformRand::rand(&mut rng));
    let eval = bivariate_polynomial.evaluate(&point);

    let open_start = Instant::now();
    let proof = BivariateKZG::<Bls12_381>::open(&g_alpha_powers, &bivariate_polynomial, &point).unwrap();
    let time = open_start.elapsed().as_millis();
    println!("Bivariate KZG open  time: {:?} ms", time * total_point_number as u128);

    // Proof size
    let proof_size = size_of_val(&proof);
    println!("Bivariate KZG proof size: {:?} bytes", proof_size * total_point_number);

    // Verify
    std::thread::sleep(Duration::from_millis(5000));
    let verify_start = Instant::now();
    for _ in 0..50 {
        let is_valid =
            BivariateKZG::<Bls12_381>::verify(&v_srs, &com, &point, &eval, &proof).unwrap();
        assert!(is_valid);
    }
    let verify_time = verify_start.elapsed().as_millis() / 50;
    println!("Bivariate KZG verif time: {:?} ms", verify_time * total_point_number as u128);

    // Setup for batch
    let setup_start = Instant::now();
    let srs =
        BivBatchKZG::<Bls12_381>::setup(&mut rng, log_x_degree, log_y_degree).unwrap();
    let time = setup_start.elapsed().as_millis();
    println!("Bivariate batch KZG setup time: {:} ms", time);

    // Commit for batch
    let mut bivariate_polynomials = Vec::new();
    for _ in 0..POLYNOMIAL_NUMBER {
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
        bivariate_polynomials.push (BivariatePolynomial { x_polynomials });
    }

    let com_start = Instant::now();
    let coms = BivBatchKZG::<Bls12_381>::commit(&srs.0, &bivariate_polynomials).unwrap();
    let time = com_start.elapsed().as_millis();
    println!("Bivariate batch KZG commi time, {:?} ms", time);

    // Open for batch
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

    let mut prover_transcript : Transcript = Transcript::new(b"batch bivariate KZG at the same y");
    let open_start = Instant::now();
    let gamma = <Transcript as ProofTranscript<Bls12_381>>::challenge_scalar(
            &mut prover_transcript, b"combined_polynomial_x_beta");
    let proof_batch = BivBatchKZG::<Bls12_381>::open_at_same_y(
        &srs.0,
        &bivariate_polynomials,
        &x_points,
        &y_point,
        &mut prover_transcript,
        &gamma
    ).unwrap();
    let time = open_start.elapsed().as_millis();
    println!("Bivariate batch KZG open  time: {:?} ms", time);

    // Proof size for batch
    let proof_size_batch = (proof_batch.1.len() + 1) * size_of_val(&<Bls12_381 as Pairing>::ScalarField::one()) + 4 * size_of_val(&proof_batch.0);
    println!("Bivariate batch KZG proof size: {:?} bytes", proof_size_batch);

    // Verify for batch
    std::thread::sleep(Duration::from_millis(5000));
    let verify_start = Instant::now();
    for _ in 0..50 {
        let mut verifier_transcript : Transcript = Transcript::new(b"batch bivariate KZG at the same y");
        let gamma = <Transcript as ProofTranscript<Bls12_381>>::challenge_scalar(
            &mut verifier_transcript, b"combined_polynomial_x_beta");
        let is_valid =
            BivBatchKZG::<Bls12_381>::verify_at_same_y(&srs.1, &coms, &x_points, &y_point, &evals, &proof_batch, &mut verifier_transcript, &gamma).unwrap();
        assert!(is_valid);
    }
    let verify_time = verify_start.elapsed().as_millis() / 50;
    println!("Bivariate batch KZG verif time: {:?} ms", verify_time);

    // Setup for batch lagrange
    let setup_start = Instant::now();
    let srs = BivBatchKZG::<Bls12_381>::setup_lagrange(&mut rng, log_x_degree, log_y_degree, &domain)
        .unwrap();
    let time = setup_start.elapsed().as_millis();
    println!("Bivariate batch lagrange KZG setup time: {:} ms", time);

    // Com for batch lagrange
    let coms = BivBatchKZG::<Bls12_381>::commit(&srs.0, &bivariate_polynomials).unwrap();
    let mut prover_transcript : Transcript = Transcript::new(b"batch bivariate KZG at the same y");
    let gamma = <Transcript as ProofTranscript<Bls12_381>>::challenge_scalar(
        &mut prover_transcript, b"combined_polynomial_x_beta");

    // Open for batch lagrange
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

    let open_start = Instant::now();
    let proof_batch = BivBatchKZG::<Bls12_381>::open_lagrange_at_same_y(
        &srs.0,
        &x_srs,
        &bivariate_polynomials,
        &x_points,
        &y_point,
        &domain,
        &mut prover_transcript,
        &gamma
    )
    .unwrap();
    let time = open_start.elapsed().as_millis();
    println!("Bivariate batch lagrange KZG open  time: {:?} ms", time);

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

    // Proof size for batch lagrange
    let proof_size_batch_lagrange = (proof_batch.1.len() + 1) * size_of_val(&<Bls12_381 as Pairing>::ScalarField::one()) + 4 * size_of_val(&proof_batch.0);
    println!("Bivariate batch KZG proof size: {:?} bytes", proof_size_batch_lagrange);

    // Verify for batch lagrange
    std::thread::sleep(Duration::from_millis(5000));
    let mut verifier_transcript : Transcript = Transcript::new(b"batch bivariate KZG at the same y");
    let gamma = <Transcript as ProofTranscript<Bls12_381>>::challenge_scalar(
        &mut verifier_transcript, b"combined_polynomial_x_beta");
    let verify_start = Instant::now();
    for _ in 0..50 {
        let is_valid =
            BivBatchKZG::<Bls12_381>::verify_at_same_y(&srs.1, &coms, &x_points, &y_point, &evals, &proof_batch, &mut verifier_transcript.clone(), &gamma).unwrap();
        assert!(is_valid);
    }
    let verify_time = verify_start.elapsed().as_millis() / 50;
    println!("Bivariate batch lagrange KZG verif time: {:?} ms", verify_time);
}

