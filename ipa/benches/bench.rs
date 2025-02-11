extern crate criterion;
use criterion::*;
use ark_poly::{
    EvaluationDomain,
    GeneralEvaluationDomain, Polynomial, Evaluations,
    DenseUVPolynomial, univariate::DensePolynomial as UnivariatePolynomial,
};
use fri::prover::BatchProver;
use fri::verifier::BatchVerifier;
use utils::{
    CODE_RATE, SECURITY_BITS, fiat_shamir::RandomOracle, 
    helper::Helper, merkle_tree::MERKLE_ROOT_SIZE,
};
use my_ipa::ipa_fri::FRIIPA;
use ark_std::rand::{rngs::StdRng, SeedableRng};
use ark_ff::PrimeField;
// use ark_bls12_381::Bls12_381;
// use ark_ec::pairing::Pairing;
// type T = <Bls12_381 as Pairing>::ScalarField;
use utils::goldilocks::Goldilocks as T;

fn trivial_commit_and_prove<T: PrimeField>(criterion: &mut Criterion, variable_num: usize) {
    let mut rng = StdRng::seed_from_u64(0u64);
    let length: usize = 1 << variable_num;
    let domain = <GeneralEvaluationDomain<T> as EvaluationDomain<T>>::new(length).unwrap();
    let mut vector_left = Vec::new();
    let mut vector_right = Vec::new();
    for _ in 0..length {
        vector_left.push(T::rand(&mut rng));
        vector_right.push(T::rand(&mut rng));
    }
    let _inner_product: T = vector_left
        .iter()
        .zip(vector_right.iter())
        .map(|(left, right)| *left * *right)
        .sum();
        // generate the commitment of f1 and f2
        let mut interpolate_cosets = vec![EvaluationDomain::new_coset(1 << (variable_num + CODE_RATE), T::one()).unwrap()];
        for i in 1..variable_num {
            interpolate_cosets.push(Helper::pow(&interpolate_cosets[i-1], 2));
        }

    criterion.bench_function(&format!("trivial ipa commit and prove {}", variable_num), move |b| {
        b.iter( || {
                 // generate the polynomials f1(x) and f2(x)
                let coeffs_left = vector_left.clone();
                let evals_left = Evaluations::<T, GeneralEvaluationDomain<T>>::from_vec_and_domain(coeffs_left, domain);
                let polynomial_left = evals_left.interpolate_by_ref();
                let coeffs_right = vector_right.clone();
                let evals_right = Evaluations::<T, GeneralEvaluationDomain<T>>::from_vec_and_domain(coeffs_right, domain);
                let polynomial_right = evals_right.interpolate();

                // compute the target polynomial
                let ifft_domain = <GeneralEvaluationDomain<T> as EvaluationDomain<T>>::new(domain.size() * 2).unwrap();
                let evals_left = polynomial_left.evaluate_over_domain_by_ref(ifft_domain);
                let evals_right = polynomial_right.evaluate_over_domain_by_ref(ifft_domain);
                let evals_target = &evals_left * &evals_right;
                let polynomial_target = evals_target.interpolate();

                // compute polynomials g and h, and their evaluations
                let oracle = RandomOracle::new(variable_num, SECURITY_BITS / CODE_RATE);
                let (g, h, _g_prime) = FRIIPA::get_g_h_g_prime(&polynomial_target, &domain);
                let alpha = T::rand(&mut rng);
                let points = vec![alpha; 2];
                let evals_f = vec![polynomial_left.evaluate(&alpha), polynomial_right.evaluate(&alpha)];
                let evals_g_h = vec![g.evaluate(&alpha), h.evaluate(&alpha)];

                let mut prover_f = BatchProver::new(variable_num, &interpolate_cosets, &[polynomial_left, polynomial_right], &oracle);
                let coms_f = prover_f.commit_polynomial();
                let helper_polynomials = [g, h];
                let mut prover_g_h = BatchProver::new(variable_num, &interpolate_cosets, &helper_polynomials, &oracle);
                let coms_g_h = prover_g_h.commit_polynomial();

                // generate the evals and proofs and verifier
                let mut verifier_f = BatchVerifier::new(variable_num, &interpolate_cosets, coms_f, &oracle, &points);
                let mut verifier_g_h = BatchVerifier::new(variable_num, &interpolate_cosets, coms_g_h, &oracle, &points);
                let _ = prover_f.open(&points, &evals_f, &mut verifier_f);
                let _ = prover_g_h.open(&points, &evals_g_h, &mut verifier_g_h);
            },
        )
    });
}

fn improved_commit_and_prove<T: PrimeField>(criterion: &mut Criterion, variable_num: usize) {
    let mut rng = StdRng::seed_from_u64(0u64);
    let length: usize = 1 << variable_num;
    let domain = <GeneralEvaluationDomain<T> as EvaluationDomain<T>>::new(length).unwrap();
    let mut vector_left = Vec::new();
    let mut vector_right = Vec::new();
    for _ in 0..length {
        vector_left.push(T::rand(&mut rng));
        vector_right.push(T::rand(&mut rng));
    }
    let _inner_product: T = vector_left
        .iter()
        .zip(vector_right.iter())
        .map(|(left, right)| *left * *right)
        .sum();

    // generate the commitment of f1 and f2
    let mut interpolate_cosets = vec![EvaluationDomain::new_coset(1 << (variable_num + CODE_RATE), T::one()).unwrap()];
    for i in 1..variable_num {
        interpolate_cosets.push(Helper::pow(&interpolate_cosets[i-1], 2));
    }

    criterion.bench_function(&format!("improved ipa commit and prove {}", variable_num), move |b| {
        b.iter( || {
                // generate the polynomials f1(x) and f2(x)
                let coeffs_left = vector_left.clone();
                let polynomial_left: UnivariatePolynomial<T> = UnivariatePolynomial::from_coefficients_vec(coeffs_left);
                let mut coeffs_right = vec![vector_right[0].clone()];
                let mut rest = vector_right.clone().split_off(1);
                rest.reverse();
                coeffs_right.extend(rest);
                let polynomial_right = UnivariatePolynomial::from_coefficients_vec(coeffs_right);

                // compute the target polynomial
                let ifft_domain = <GeneralEvaluationDomain<T> as EvaluationDomain<T>>::new(domain.size() * 2).unwrap();
                let evals_left = polynomial_left.evaluate_over_domain_by_ref(ifft_domain);
                let evals_right = polynomial_right.evaluate_over_domain_by_ref(ifft_domain);
                let evals_target = &evals_left * &evals_right;
                let polynomial_target = evals_target.interpolate();

                // compute polynomials g and h, and their evaluations
                let oracle = RandomOracle::new(variable_num, SECURITY_BITS / CODE_RATE);
                let (g, h, _g_prime) = FRIIPA::get_g_h_g_prime(&polynomial_target, &domain);
                let alpha = T::rand(&mut rng);
                let points = vec![alpha; 2];
                let evals_f = vec![polynomial_left.evaluate(&alpha), polynomial_right.evaluate(&alpha)];
                let evals_g_h = vec![g.evaluate(&alpha), h.evaluate(&alpha)];

                let mut prover_f = BatchProver::new(variable_num, &interpolate_cosets, &[polynomial_left, polynomial_right], &oracle);
                let coms_f = prover_f.commit_polynomial();
                let helper_polynomials = [g, h];
                let mut prover_g_h = BatchProver::new(variable_num, &interpolate_cosets, &helper_polynomials, &oracle);
                let coms_g_h = prover_g_h.commit_polynomial();

                // generate the evals and proofs and verifier
                let mut verifier_f = BatchVerifier::new(variable_num, &interpolate_cosets, coms_f, &oracle, &points);
                let mut verifier_g_h = BatchVerifier::new(variable_num, &interpolate_cosets, coms_g_h, &oracle, &points);
                let _ = prover_f.open(&points, &evals_f, &mut verifier_f);
                let _ = prover_g_h.open(&points, &evals_g_h, &mut verifier_g_h);
            },
        )
    });
}


fn bench_commit(c: &mut Criterion) {
    for i in 15..=20 {
        improved_commit_and_prove::<T>(c, i);
        trivial_commit_and_prove::<T>(c, i);
    }
}

fn trivial_verify<T: PrimeField>(criterion: &mut Criterion, variable_num: usize) {
    let mut rng = StdRng::seed_from_u64(0u64);
    let length: usize = 1 << variable_num;
    let domain = <GeneralEvaluationDomain<T> as EvaluationDomain<T>>::new(length).unwrap();
    let mut vector_left = Vec::new();
    let mut vector_right = Vec::new();
    for _ in 0..length {
        vector_left.push(T::rand(&mut rng));
        vector_right.push(T::rand(&mut rng));
    }
    let inner_product: T = vector_left
        .iter()
        .zip(vector_right.iter())
        .map(|(left, right)| *left * *right)
        .sum();

    let coeffs_left = vector_left.clone();
    let evals_left = Evaluations::<T, GeneralEvaluationDomain<T>>::from_vec_and_domain(coeffs_left, domain);
    let polynomial_left = evals_left.interpolate_by_ref();
    let coeffs_right = vector_right.clone();
    let evals_right = Evaluations::<T, GeneralEvaluationDomain<T>>::from_vec_and_domain(coeffs_right, domain);
    let polynomial_right = evals_right.interpolate();

    // generate the commitment of f1 and f2
    let mut interpolate_cosets = vec![EvaluationDomain::new_coset(1 << (variable_num + CODE_RATE), T::one()).unwrap()];
    for i in 1..variable_num {
        interpolate_cosets.push(Helper::pow(&interpolate_cosets[i-1], 2));
    }

    // compute the target polynomial
    let ifft_domain = <GeneralEvaluationDomain<T> as EvaluationDomain<T>>::new(domain.size() * 2).unwrap();
    let evals_left = polynomial_left.evaluate_over_domain_by_ref(ifft_domain);
    let evals_right = polynomial_right.evaluate_over_domain_by_ref(ifft_domain);
    let evals_target = &evals_left * &evals_right;
    let polynomial_target = evals_target.interpolate();

    // compute polynomials g and h, and their evaluations
    let oracle = RandomOracle::new(variable_num, SECURITY_BITS / CODE_RATE);
    let (g, h, _g_prime) = FRIIPA::get_g_h_g_prime(&polynomial_target, &domain);
    let alpha = T::rand(&mut rng);
    let points = vec![alpha; 2];
    let evals_f = vec![polynomial_left.evaluate(&alpha), polynomial_right.evaluate(&alpha)];
    let evals_g_h = vec![g.evaluate(&alpha), h.evaluate(&alpha)];

    let mut prover_f = BatchProver::new(variable_num, &interpolate_cosets, &[polynomial_left, polynomial_right], &oracle);
    let coms_f = prover_f.commit_polynomial();
    let helper_polynomials = [g, h];
    let mut prover_g_h = BatchProver::new(variable_num, &interpolate_cosets, &helper_polynomials, &oracle);
    let coms_g_h = prover_g_h.commit_polynomial();

    // generate the evals and proofs and verifier
    let mut verifier_f = BatchVerifier::new(variable_num, &interpolate_cosets, coms_f, &oracle, &points);
    let mut verifier_g_h = BatchVerifier::new(variable_num, &interpolate_cosets, coms_g_h, &oracle, &points);
    let proof_f = prover_f.open(&points, &evals_f, &mut verifier_f);
    let proof_g_h = prover_g_h.open(&points, &evals_g_h, &mut verifier_g_h);

    let proof_size = 2 * (proof_f.0.proof_size()
        + proof_f.1
            .iter()
            .map(|x| x.proof_size())
            .sum::<usize>()
        + (variable_num - 1) * MERKLE_ROOT_SIZE);
    println!("proof size is: {:?} KB", proof_size / 1024);

    criterion.bench_function(&format!("fri-pcs ipa trivial verify {}", variable_num), move |b| {
        b.iter(|| {
            assert!(verifier_f.verify(&proof_f, &evals_f));
            assert!(verifier_g_h.verify(&proof_g_h, &evals_g_h));
            let eval_left = evals_f[0] * evals_f[1];
            let eval_right = alpha * evals_g_h[0] + inner_product / domain.size_as_field_element() + domain.evaluate_vanishing_polynomial(alpha) * evals_g_h[1];
            assert_eq!(eval_left, eval_right);
        })
    });
}

fn improved_verify<T: PrimeField>(criterion: &mut Criterion, variable_num: usize) {
    let mut rng = StdRng::seed_from_u64(0u64);
    let length: usize = 1 << variable_num;
    let domain = <GeneralEvaluationDomain<T> as EvaluationDomain<T>>::new(length).unwrap();
    let mut vector_left = Vec::new();
    let mut vector_right = Vec::new();
    for _ in 0..length {
        vector_left.push(T::rand(&mut rng));
        vector_right.push(T::rand(&mut rng));
    }
    let inner_product: T = vector_left
        .iter()
        .zip(vector_right.iter())
        .map(|(left, right)| *left * *right)
        .sum();

    // generate the polynomials f1(x) and f2(x)
    let coeffs_left = vector_left.clone();
    let polynomial_left: UnivariatePolynomial<T> = UnivariatePolynomial::from_coefficients_vec(coeffs_left);
    let mut coeffs_right = vec![vector_right[0].clone()];
    let mut rest = vector_right.clone().split_off(1);
    rest.reverse();
    coeffs_right.extend(rest);
    let polynomial_right = UnivariatePolynomial::from_coefficients_vec(coeffs_right);

    // generate the commitment of f1 and f2
    let mut interpolate_cosets = vec![EvaluationDomain::new_coset(1 << (variable_num + CODE_RATE), T::one()).unwrap()];
    for i in 1..variable_num {
        interpolate_cosets.push(Helper::pow(&interpolate_cosets[i-1], 2));
    }

    // compute the target polynomial
    let ifft_domain = <GeneralEvaluationDomain<T> as EvaluationDomain<T>>::new(domain.size() * 2).unwrap();
    let evals_left = polynomial_left.evaluate_over_domain_by_ref(ifft_domain);
    let evals_right = polynomial_right.evaluate_over_domain_by_ref(ifft_domain);
    let evals_target = &evals_left * &evals_right;
    let polynomial_target = evals_target.interpolate();

    // compute polynomials g and h, and their evaluations
    let oracle = RandomOracle::new(variable_num, SECURITY_BITS / CODE_RATE);
    let (g, h, _g_prime) = FRIIPA::get_g_h_g_prime(&polynomial_target, &domain);
    let alpha = T::rand(&mut rng);
    let points = vec![alpha; 2];
    let evals_f = vec![polynomial_left.evaluate(&alpha), polynomial_right.evaluate(&alpha)];
    let evals_g_h = vec![g.evaluate(&alpha), h.evaluate(&alpha)];

    let mut prover_f = BatchProver::new(variable_num, &interpolate_cosets, &[polynomial_left, polynomial_right], &oracle);
    let coms_f = prover_f.commit_polynomial();
    let helper_polynomials = [g, h];
    let mut prover_g_h = BatchProver::new(variable_num, &interpolate_cosets, &helper_polynomials, &oracle);
    let coms_g_h = prover_g_h.commit_polynomial();

    // generate the evals and proofs and verifier
    let mut verifier_f = BatchVerifier::new(variable_num, &interpolate_cosets, coms_f, &oracle, &points);
    let mut verifier_g_h = BatchVerifier::new(variable_num, &interpolate_cosets, coms_g_h, &oracle, &points);
    let proof_f = prover_f.open(&points, &evals_f, &mut verifier_f);
    let proof_g_h = prover_g_h.open(&points, &evals_g_h, &mut verifier_g_h);

    let proof_size = 2 * (proof_f.0.proof_size()
    + proof_f.1
        .iter()
        .map(|x| x.proof_size())
        .sum::<usize>()
    + (variable_num - 1) * MERKLE_ROOT_SIZE);
    println!("proof size is: {:?} KB", proof_size / 1024);

    criterion.bench_function(&format!("fri-pcs ipa improved verify {}", variable_num), move |b| {
        b.iter(|| {
            assert!(verifier_f.verify(&proof_f, &evals_f));
            assert!(verifier_g_h.verify(&proof_g_h, &evals_g_h));
            let eval_left = evals_f[0] * evals_f[1];
            let eval_right = alpha * evals_g_h[0] + inner_product + domain.evaluate_vanishing_polynomial(alpha) * evals_g_h[1];
            assert_eq!(eval_left, eval_right);
        })
    });
}


fn bench_verify(c: &mut Criterion) {
    for i in 15..=20 {
        trivial_verify::<T>(c, i);
        improved_verify::<T>(c, i);
    }
}

criterion_group! {
    name = benches;
    config = Criterion::default().sample_size(10);
    targets = 
    bench_commit, 
    bench_verify
}

criterion_main!(benches);
