extern crate criterion;
use criterion::*;

use polyfrim::{prover::One2ManyProver, verifier::One2ManyVerifier};
use ark_ff::{Field, UniformRand};
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain};
use utils::helper::MultilinearPolynomial;
use utils::fiat_shamir::RandomOracle;
use utils::merkle_tree::MERKLE_ROOT_SIZE;
use utils::{CODE_RATE, SECURITY_BITS};
use utils::goldilocks::Goldilocks as T;
use utils::helper::Helper;
use rand::rngs::StdRng;
use rand::SeedableRng;

const SMALL: usize = 20;
const SIZE: usize = 25;

// usage:
// RAYON_NUM_THREADS=4 cargo bench --features "parallel" -p polyfrim

fn commit(criterion: &mut Criterion, variable_num: usize) {
    let mut rng = StdRng::seed_from_u64(0u64);
    let polynomial = MultilinearPolynomial::rand(variable_num);
    let point = (0..variable_num)
        .map(|_| T::rand(&mut rng))
        .collect::<Vec<T>>();
    let _eval = polynomial.evaluate(&point);
    // setup
    let mut interpolate_cosets = vec![EvaluationDomain::new_coset(1 << (variable_num + CODE_RATE), T::rand(&mut rng)).unwrap()];
    for i in 1..variable_num {
        interpolate_cosets.push(Helper::pow(&interpolate_cosets[i-1], 2));
    }
    let oracle = RandomOracle::new(variable_num, SECURITY_BITS / CODE_RATE);

    criterion.bench_function(&format!("polyfrim commit {}", variable_num), move |b| {
        b.iter_batched(
            || polynomial.clone(),
            |p| {
                let prover = One2ManyProver::new(
                    variable_num,
                    &interpolate_cosets,
                    p,
                    &oracle,
                );
                prover.commit_polynomial();
            },
            BatchSize::SmallInput,
        )
    });
}

fn bench_commit(c: &mut Criterion) {
    for i in SMALL..=SIZE {
        commit(c, i);
    }
}

fn open(criterion: &mut Criterion, variable_num: usize) {
    let mut rng = StdRng::seed_from_u64(0u64);
    let polynomial = MultilinearPolynomial::rand(variable_num);
    let point = (0..variable_num)
        .map(|_| T::rand(&mut rng))
        .collect::<Vec<T>>();
    let _eval = polynomial.evaluate(&point);

    // setup
    let mut interpolate_cosets = vec![EvaluationDomain::new_coset(1 << (variable_num + CODE_RATE), T::from(1)).unwrap()];
    for i in 1..variable_num {
        interpolate_cosets.push(Helper::pow(&interpolate_cosets[i-1], 2));
    }

    let oracle = RandomOracle::new(variable_num, SECURITY_BITS / CODE_RATE);
    let prover = One2ManyProver::new(variable_num, &interpolate_cosets, polynomial, &oracle);

    // commit
    let commit = prover.commit_polynomial();
    let mut verifier = One2ManyVerifier::new(
        variable_num,
        &interpolate_cosets,
        commit,
        &oracle,
        &point,
    );

    criterion.bench_function(&format!("polyfrim open {}", variable_num), move |b| {
        b.iter_batched(
            || prover.clone(),
            |mut p| {
                p.open(&mut verifier, &point)
            },
            BatchSize::SmallInput,
        )
    });
}

fn bench_open(c: &mut Criterion) {
    for i in SMALL..=SIZE {
        open(c, i);
    }
}

fn verify(criterion: &mut Criterion, variable_num: usize) {
    let variable_num: usize = 14;
    let mut rng = StdRng::seed_from_u64(0u64);
    let polynomial = MultilinearPolynomial::rand(variable_num);
    let point = (0..variable_num)
        .map(|_| T::rand(&mut rng))
        .collect::<Vec<T>>();
    let eval = polynomial.evaluate(&point);

    // setup
    let mut interpolate_cosets = vec![EvaluationDomain::new_coset(1 << (variable_num + CODE_RATE), T::from(1)).unwrap()];
    for i in 1..variable_num {
        interpolate_cosets.push(Helper::pow(&interpolate_cosets[i-1], 2));
    }

    let oracle = RandomOracle::new(variable_num, SECURITY_BITS / CODE_RATE);
    let mut prover = One2ManyProver::new(variable_num, &interpolate_cosets, polynomial, &oracle);

    // commit
    let commit = prover.commit_polynomial();
    let mut verifier = One2ManyVerifier::new(
        variable_num,
        &interpolate_cosets,
        commit,
        &oracle,
        &point,
    );

    // open
    let (folding_proof, function_proof) = prover.open(&mut verifier, &point);

    // proof size
    let proof_size = folding_proof.iter().map(|x| x.proof_size()).sum::<usize>()
        + function_proof.iter().map(|x| x.proof_size()).sum::<usize>()
        // p only has \mu - 1 polynomials, and \mu - 2 roots
        // f involve \mu polynomials, and \mu - 1 roots
        + (2 * variable_num - 3) * MERKLE_ROOT_SIZE
        + size_of::<T>() * 2;
    println!("proof size for {} variable is {:?} KB", variable_num, proof_size / 1024);

    criterion.bench_function(&format!("polyfrim verify {}", variable_num), move |b| {
        b.iter(|| {
            verifier.verify(&folding_proof, &function_proof, eval);
            // assert_eq!(verifier.get_evaluation(), eval);
        })
    });
}

fn bench_verify(c: &mut Criterion) {
    for i in SMALL..=SIZE {
        verify(c, i);
    }
}

criterion_group! {
    name = benches;
    config = Criterion::default().sample_size(10);
    targets = 
    bench_commit, 
    bench_open, 
    bench_verify
}

criterion_main!(benches);
