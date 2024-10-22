use ark_ec::pairing::Pairing;
use ark_bls12_381::Bls12_381;
use ark_ff::{UniformRand, One};
use my_kzg::biv_trivial_kzg::{BivariateKZG, BivariatePolynomial};
use my_kzg::biv_batch_kzg::BivBatchKZG;
use ark_poly::polynomial::{
    univariate::DensePolynomial as UnivariatePolynomial, DenseUVPolynomial,
};
use ark_std::rand::{rngs::StdRng, SeedableRng};
use std::time::Duration;
use merlin::Transcript;
use my_kzg::transcript::ProofTranscript;
use criterion::{criterion_group, criterion_main, Criterion};

fn configure_criterion() -> Criterion {
    Criterion::default()
        .measurement_time(Duration::new(10, 0)) 
        .sample_size(10) 
}

const POLYNOMIAL_NUMBER: usize = 5;
const X_POINT_NUMBER: usize = 2;
const BIVARIATE_Y_LOG_DEGREE: usize = 3;

fn biv_batch_kzg_prove_and_verify_benchmark(c: &mut Criterion) {
    let log_sizes = vec![12, 14, 16, 18, 20, 22, 24];
    let mut rng = StdRng::seed_from_u64(0u64);

    let log_y_degree = (1 << BIVARIATE_Y_LOG_DEGREE) - 1;
    let total_point_number = POLYNOMIAL_NUMBER * X_POINT_NUMBER;

    for &log_size in &log_sizes {
        let log_x_degree = (1 << log_size) - 1;
        
        // Setup
        let srs = BivBatchKZG::<Bls12_381>::setup(&mut rng, log_x_degree, log_y_degree).unwrap();

        // generate bivariate polynomials
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

        // pick random x_points and compute the evals
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

        // commits 
        let coms = BivBatchKZG::<Bls12_381>::commit(&srs.0, &bivariate_polynomials).unwrap();

        // trivial open
        c.bench_function(&format!("Trivial Bivariate KZG open, log_vector_length: {}", log_size), |b| {
            b.iter(|| {
                for i in 0..POLYNOMIAL_NUMBER {
                    let _ = BivariateKZG::<Bls12_381>::open(
                        &srs.0, 
                        &bivariate_polynomials[i], 
                        &(x_points[i][0], y_point));

                    let _ = BivariateKZG::<Bls12_381>::open(
                        &srs.0, 
                        &bivariate_polynomials[i], 
                        &(x_points[i][1], y_point));
                }
            });
        });
        let proof = BivariateKZG::<Bls12_381>::open(
            &srs.0, 
            &bivariate_polynomials[0], 
            &(x_points[0][0], y_point)).unwrap();
        let proof_size = size_of_val(&proof);
        println!("Trival Bivariate KZG proof size: {:?} bytes", proof_size * total_point_number);

        // batch open
        c.bench_function(&format!("Batch Bivariate KZG open, log_vector_length: {}", log_size), |b| {
            b.iter(|| {
                let mut prover_transcript : Transcript = Transcript::new(b"batch bivariate KZG at the same y");
                let gamma = <Transcript as ProofTranscript<Bls12_381>>::challenge_scalar(
                        &mut prover_transcript, b"combined_polynomial_x_beta");
                let _ = BivBatchKZG::<Bls12_381>::open_at_same_y(
                    &srs.0,
                    &bivariate_polynomials,
                    &x_points,
                    &y_point,
                    &mut prover_transcript,
                    &gamma
                ).unwrap();
            });
        });
        let mut prover_transcript : Transcript = Transcript::new(b"batch bivariate KZG at the same y");
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
        let proof_size_batch = (proof_batch.1.len() + 1) * size_of_val(&<Bls12_381 as Pairing>::ScalarField::one()) + 4 * size_of_val(&proof_batch.0);
        println!("Batch Bivariate KZG proof size: {:?} bytes", proof_size_batch);

        // trivial bivariate kzg verify
        let mut proofs = Vec::new();
        for i in 0..POLYNOMIAL_NUMBER {
            let proof_1 = BivariateKZG::<Bls12_381>::open(
                &srs.0, 
                &bivariate_polynomials[i], 
                &(x_points[i][0], y_point)).unwrap();

            let proof_2 = BivariateKZG::<Bls12_381>::open(
                &srs.0, 
                &bivariate_polynomials[i], 
                &(x_points[i][1], y_point)).unwrap();
            
            proofs.push(vec![proof_1, proof_2]);
        }

        c.bench_function(&format!("Trivial Bivariate KZG verify, log_vector_length: {}", log_size), |b| {
            b.iter(|| {
                for i in 0..POLYNOMIAL_NUMBER {
                    let is_valid =
                        BivariateKZG::<Bls12_381>::verify(&srs.1, &coms[i], &(x_points[i][0], y_point), &evals[i][0], &proofs[i][0]).unwrap();
                    assert!(is_valid);
        
                    let is_valid =
                        BivariateKZG::<Bls12_381>::verify(&srs.1, &coms[i], &(x_points[i][1], y_point), &evals[i][1], &proofs[i][1]).unwrap();
                    assert!(is_valid);
                }
            });
        });

        // batch bivariate kzg verify
        c.bench_function(&format!("Batch Bivariate KZG verify, log_vector_length: {}", log_size), |b| {
            b.iter(|| {
                let mut verifier_transcript : Transcript = Transcript::new(b"batch bivariate KZG at the same y");
                let gamma = <Transcript as ProofTranscript<Bls12_381>>::challenge_scalar(
                    &mut verifier_transcript, b"combined_polynomial_x_beta");
                let is_valid =
                    BivBatchKZG::<Bls12_381>::verify_at_same_y(&srs.1, &coms, &x_points, &y_point, &evals, &proof_batch, &mut verifier_transcript, &gamma).unwrap();
                assert!(is_valid);
            });
        });
    }
}

criterion_group!{
    name = benches;
    config = configure_criterion();
    targets = 
    biv_batch_kzg_prove_and_verify_benchmark,
}
criterion_main!(benches);