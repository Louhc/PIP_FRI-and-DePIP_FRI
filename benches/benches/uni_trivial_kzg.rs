use ark_bls12_381::Bls12_381;
use ark_ec::pairing::Pairing;
use ark_ff::UniformRand;
use my_kzg::uni_trivial_kzg::KZG;
use ark_poly::polynomial::{
    univariate::DensePolynomial as UnivariatePolynomial, DenseUVPolynomial, Polynomial
};
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain};
use ark_std::rand::{rngs::StdRng, SeedableRng};
use std::time::Duration;
use criterion::{criterion_group, criterion_main, Criterion};

fn configure_criterion() -> Criterion {
    Criterion::default()
        .measurement_time(Duration::new(10, 0)) 
        .sample_size(10) 
}

fn kzg_setup_benchmark(c: &mut Criterion) {
    let log_sizes = vec![10, 12, 14, 16, 18, 20];
    let mut rng = StdRng::seed_from_u64(0u64);
    for &log_size in &log_sizes {
        let size = 1 << log_size;
        let degree = size - 1;
        let domain = <GeneralEvaluationDomain<<Bls12_381 as Pairing>::ScalarField> as EvaluationDomain<<Bls12_381 as Pairing>::ScalarField>>::new(size).unwrap();
        c.bench_function(&format!("KZG_setup, log_degree {}", log_size), |b| {
            b.iter(|| {
                let _ = KZG::<Bls12_381>::setup(
                    &mut rng,
                    degree,
                );
            });
        });

        c.bench_function(&format!("KZG_lagrange_setup, log_degree {}", log_size), |b| {
            b.iter(|| {
                let _ = KZG::<Bls12_381>::setup_lagrange(
                    &mut rng,
                    degree,
                    &domain,
                );
            });
        });
    }
}

fn kzg_commit_benchmark(c: &mut Criterion) {
    let log_sizes = vec![10, 12, 14, 16, 18, 20];
    let mut rng = StdRng::seed_from_u64(0u64);
    for &log_size in &log_sizes {
        let size = 1 << log_size;
        let degree = size - 1;
        let domain = <GeneralEvaluationDomain<<Bls12_381 as Pairing>::ScalarField> as EvaluationDomain<<Bls12_381 as Pairing>::ScalarField>>::new(size).unwrap();
        let (g_alpha_powers, _v_srs) = KZG::<Bls12_381>::setup(&mut rng, degree).unwrap();
        let polynomial = UnivariatePolynomial::rand(degree, &mut rng);
        // let point = <Bls12_381 as Pairing>::ScalarField::rand(&mut rng);
        // let eval = polynomial.evaluate(&point);
        c.bench_function(&format!("KZG_commit, log_degree {}", log_size), |b| {
            b.iter(|| {
                let _ = KZG::<Bls12_381>::commit(
                    &g_alpha_powers,
                    &polynomial,
                );
            });
        });

        let (g_alpha_powers, _v_srs) = KZG::<Bls12_381>::setup_lagrange(&mut rng, degree, &domain).unwrap();
        let evals = polynomial.evaluate_over_domain_by_ref(domain).evals;
        c.bench_function(&format!("KZG_lagrange_commit, log_degree {}", log_size), |b| {
            b.iter(|| {
                let _ = KZG::<Bls12_381>::commit_lagrange(
                    &g_alpha_powers,
                    &evals,
                );
            });
        });
    }
}

fn kzg_open_benchmark(c: &mut Criterion) {
    let log_sizes = vec![10, 12, 14, 16, 18, 20];
    let mut rng = StdRng::seed_from_u64(0u64);
    for &log_size in &log_sizes {
        let size = 1 << log_size;
        let degree = size - 1;
        let domain = <GeneralEvaluationDomain<<Bls12_381 as Pairing>::ScalarField> as EvaluationDomain<<Bls12_381 as Pairing>::ScalarField>>::new(size).unwrap();
        let (g_alpha_powers, _v_srs) = KZG::<Bls12_381>::setup(&mut rng, degree).unwrap();
        let polynomial = UnivariatePolynomial::rand(degree, &mut rng);
        let point = <Bls12_381 as Pairing>::ScalarField::rand(&mut rng);
        //let eval = polynomial.evaluate(&point);
        // let com = KZG::<Bls12_381>::commit(&g_alpha_powers, &polynomial).unwrap();
        c.bench_function(&format!("KZG_open, log_degree {}", log_size), |b| {
            b.iter(|| {
                let _ = KZG::<Bls12_381>::open(
                    &g_alpha_powers,
                    &polynomial,
                    &point,
                );
            });
        });

        let (g_alpha_powers, _v_srs) = KZG::<Bls12_381>::setup_lagrange(&mut rng, degree, &domain).unwrap();
        let evals = polynomial.evaluate_over_domain_by_ref(domain).evals;
        c.bench_function(&format!("KZG_lagrange_open, log_degree {}", log_size), |b| {
            b.iter(|| {
                let _ = KZG::<Bls12_381>::open_lagrange(
                    &g_alpha_powers,
                    &evals,
                    &point,
                    &domain,
                );
            });
        });
    }
}

fn kzg_verify_benchmark(c: &mut Criterion) {
    let log_sizes = vec![10, 12, 14, 16, 18, 20];
    let mut rng = StdRng::seed_from_u64(0u64);
    for &log_size in &log_sizes {
        let size = 1 << log_size;
        let degree = size - 1;
        let domain = <GeneralEvaluationDomain<<Bls12_381 as Pairing>::ScalarField> as EvaluationDomain<<Bls12_381 as Pairing>::ScalarField>>::new(size).unwrap();
        let (g_alpha_powers, v_srs) = KZG::<Bls12_381>::setup(&mut rng, degree).unwrap();
        let polynomial = UnivariatePolynomial::rand(degree, &mut rng);
        let point = <Bls12_381 as Pairing>::ScalarField::rand(&mut rng);
        let eval = polynomial.evaluate(&point);
        let com = KZG::<Bls12_381>::commit(&g_alpha_powers, &polynomial).unwrap();
        let proof = KZG::<Bls12_381>::open(&g_alpha_powers, &polynomial, &point).unwrap();
        c.bench_function(&format!("KZG_verify, log_degree {}", log_size), |b| {
            b.iter(|| {
                let _ = KZG::<Bls12_381>::verify(
                    &v_srs,
                    &com,
                    &point,
                    &eval,
                    &proof,
                );
            });
        });


        let (g_alpha_powers, v_srs) = KZG::<Bls12_381>::setup_lagrange(&mut rng, degree, &domain).unwrap();
        let evals = polynomial.evaluate_over_domain_by_ref(domain).evals;
        let eval = polynomial.evaluate(&point);
        let proof = KZG::<Bls12_381>::open_lagrange(
            &g_alpha_powers,
            &evals,
            &point,
            &domain,
        ).unwrap();
        c.bench_function(&format!("KZG_lagrange_verify, log_degree {}", log_size), |b| {
            b.iter(|| {
                let _ = KZG::<Bls12_381>::verify(
                    &v_srs,
                    &com,
                    &point,
                    &eval,
                    &proof,
                );
            });
        });
    }
}

criterion_group!{
    name = benches;
    config = configure_criterion();
    targets = 
    kzg_setup_benchmark,
    kzg_commit_benchmark,
    kzg_open_benchmark,
    kzg_verify_benchmark
}
criterion_main!(benches);
