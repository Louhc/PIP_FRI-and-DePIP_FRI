// usage: 
// RAYON_NUM_THREADS=1 cargo bench --bench fft --no-default-features -- --nocapture
// RAYON_NUM_THREADS=4 cargo bench --bench fft --no-default-features --features "parallel asm" -- --nocapture

use ark_ec::pairing::Pairing;
use ark_bls12_381::Bls12_381;
use ark_poly::polynomial::{univariate::DensePolynomial as UnivariatePolynomial, DenseUVPolynomial};
use ark_std::rand::{rngs::StdRng, SeedableRng};
use ark_std::UniformRand;
use std::time::Duration;
use criterion::{criterion_group, criterion_main, Criterion};
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain};

#[macro_export] macro_rules! par_join_4 {
    ($task1:expr, $task2:expr, $task3:expr, $task4:expr) => {{
        let ((result1, result2), (result3, result4)) = rayon::join(
            || rayon::join($task1, $task2),
            || rayon::join($task3, $task4)
        );
        (result1, result2, result3, result4)
    }};
}

fn configure_criterion() -> Criterion {
    Criterion::default()
        .measurement_time(Duration::new(10, 0)) 
        .sample_size(10) 
}

fn trivial_fft_benchmark(c: &mut Criterion) {
    let log_sizes = vec![14, 16, 18, 20, 22, 24];
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
    
        // trivial fft
        c.bench_function(&format!("Trivial fft, log_vector_length: {}", log_size), |b| {
            b.iter(|| {
                let _ = x_polynomial.evaluate_over_domain_by_ref(x_domain);
            });
        });

    }
}

fn multicores_fft_benchmark(c: &mut Criterion) {
    let log_sizes = vec![14, 16, 18, 20, 22, 24];
    let mut rng = StdRng::seed_from_u64(0u64);

    for &log_size in &log_sizes {
        let x_degree = (1 << log_size) - 1;

        // generate bivariate polynomials
        let mut x_polynomial_coeffs = vec![];
        for _ in 0..x_degree + 1 {
            x_polynomial_coeffs.push(<Bls12_381 as Pairing>::ScalarField::rand(&mut rng));
        }
        let x_polynomial = UnivariatePolynomial::from_coefficients_slice(
            &x_polynomial_coeffs
        );  

        // generate sub-polynomials
        let l = (x_degree + 1) / 4;
        let sub_domain  = <GeneralEvaluationDomain<<Bls12_381 as Pairing>::ScalarField> as EvaluationDomain<<Bls12_381 as Pairing>::ScalarField>>::new(x_degree / 4).unwrap();
        let x_polynomial_coeffs = x_polynomial.coeffs.to_vec();
        let coeffs_0 = x_polynomial_coeffs[0..l].to_vec();
        let coeffs_1 = x_polynomial_coeffs[l..2 * l].to_vec();
        let coeffs_2 = x_polynomial_coeffs[2 * l..3 * l].to_vec();
        let coeffs_3 = x_polynomial_coeffs[3 * l..4 * l].to_vec();

        let poly_0 = UnivariatePolynomial::from_coefficients_vec(coeffs_0);
        let poly_1 = UnivariatePolynomial::from_coefficients_vec(coeffs_1);
        let poly_2 = UnivariatePolynomial::from_coefficients_vec(coeffs_2);
        let poly_3 = UnivariatePolynomial::from_coefficients_vec(coeffs_3);

        // sub ffts without multicores
        // c.bench_function(&format!("Sub fft without multi-cores, log_vector_length: {}", log_size), |b| {
        //     b.iter(|| {
        //         let _ = poly_0.evaluate_over_domain_by_ref(sub_domain);
        //         let _ = poly_1.evaluate_over_domain_by_ref(sub_domain);
        //         let _ = poly_2.evaluate_over_domain_by_ref(sub_domain);
        //         let _ = poly_3.evaluate_over_domain_by_ref(sub_domain);
        //     });
        // });

        // sub ffts with multicores
        // c.bench_function(&format!("Sub fft with multi-cores, log_vector_length: {}", log_size), |b| {
        //     b.iter(|| {
        //         let (_, _, _, _) = par_join_4!(
        //             || poly_0.evaluate_over_domain_by_ref(sub_domain),
        //             || poly_1.evaluate_over_domain_by_ref(sub_domain), 
        //             || poly_2.evaluate_over_domain_by_ref(sub_domain), 
        //             || poly_3.evaluate_over_domain_by_ref(sub_domain)
        //         );
                // let ((_, _), (_, _)) = rayon::join(
                //     || (
                //         poly_0.evaluate_over_domain_by_ref(sub_domain),
                //         poly_1.evaluate_over_domain_by_ref(sub_domain)
                //     ), 
                //     || (
                //         poly_2.evaluate_over_domain_by_ref(sub_domain),
                //         poly_3.evaluate_over_domain_by_ref(sub_domain)
                //     )
                // );
        //     });
        // });
    }
}

criterion_group!{
    name = benches;
    config = configure_criterion();
    targets = 
    trivial_fft_benchmark,
    // multicores_fft_benchmark
}
criterion_main!(benches);