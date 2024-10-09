use ark_bls12_381::Bls12_381;
use ark_ec::pairing::Pairing;
use ark_ff::UniformRand;
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain};
use ark_std::rand::{rngs::StdRng, SeedableRng};
use merlin::Transcript;
use my_ipa::{ipa::IPA, ipa_from_laurent};
use my_kzg::batch_kzg::BatchKZG;
use std::time::Duration;

use criterion::{criterion_group, criterion_main, Criterion};

fn configure_criterion() -> Criterion {
    Criterion::default()
        .measurement_time(Duration::new(10, 0)) 
        .sample_size(10) 
}


fn ipa_commit_and_prove_benchmark(c: &mut Criterion) {
    let log_sizes = vec![12, 14, 16, 18, 20, 22, 24];
    let mut rng = StdRng::seed_from_u64(0u64);
    for &log_size in &log_sizes {
        let size = 1 << log_size;
        let degree = size - 1;
        let domain = <GeneralEvaluationDomain<<Bls12_381 as Pairing>::ScalarField> as EvaluationDomain<
            <Bls12_381 as Pairing>::ScalarField>>::new(size).unwrap();
        let mut vector_left = Vec::new();
        let mut vector_right = Vec::new();
        for _ in 0..size {
            vector_left.push(<Bls12_381 as Pairing>::ScalarField::rand(&mut rng));
            vector_right.push(<Bls12_381 as Pairing>::ScalarField::rand(&mut rng));
        }
        let inner_product = vector_left
            .iter()
            .zip(vector_right.iter())
            .map(|(left, right)| left * right)
            .sum();
        let (g_alpha_powers, _v_srs) = BatchKZG::<Bls12_381>::setup(&mut rng, degree).unwrap();

        c.bench_function(&format!("Trivial_IPA_commit_and_prove, log_vector_length: {}", log_size), |b| {
            b.iter(|| {
                let mut transcript = Transcript::new(b"IPA_commit_and_prove");
                let _ = IPA::<Bls12_381>::trivial_ipa_commit_and_prove(
                    &g_alpha_powers,
                    &vector_left,
                    &vector_right,
                    &domain,
                    &mut transcript,
                );
            });
        });
        let mut transcript = Transcript::new(b"IPA_commit_and_prove");
        let proof = IPA::<Bls12_381>::trivial_ipa_commit_and_prove(
            &g_alpha_powers,
            &vector_left,
            &vector_right,
            &domain,
            &mut transcript,
        ).unwrap();
        println!("Trivial IPA proof size is {} bytes", IPA::<Bls12_381>::get_proof_size(&proof));

        c.bench_function(&format!("Laurent_IPA_commit_and_prove, log_vector_length: {}", log_size), |b| {
            b.iter(|| {
                let mut transcript = Transcript::new(b"IPA_commit_and_prove");
                let _ = ipa_from_laurent::IPA::<Bls12_381>::ipa_from_laurent_commit_and_prove(
                    &g_alpha_powers,
                    &vector_left,
                    &vector_right,
                    &inner_product,
                    &domain,
                    &mut transcript,
                );
            });
        });
        let mut transcript = Transcript::new(b"IPA_commit_and_prove");
        let proof = ipa_from_laurent::IPA::<Bls12_381>::ipa_from_laurent_commit_and_prove(
            &g_alpha_powers,
            &vector_left,
            &vector_right,
            &inner_product,
            &domain,
            &mut transcript,
        ).unwrap();
        println!("Laurent IPA proof size is {} bytes", ipa_from_laurent::IPA::<Bls12_381>::get_proof_size(&proof));

        c.bench_function(&format!("Improved_IPA_commit_and_prove, log_vector_length: {}", log_size), |b| {
            b.iter(|| {
                let mut transcript = Transcript::new(b"IPA_commit_and_prove");
                let _ = IPA::<Bls12_381>::ipa_improved_commit_and_prove(
                    &g_alpha_powers,
                    &vector_left,
                    &vector_right,
                    &domain,
                    &mut transcript,
                );
                // println!("Improved IPA proof size is {} bytes", IPA::<Bls12_381>::get_proof_size(&proof));
            });
        });

        let mut transcript = Transcript::new(b"IPA_commit_and_prove");
        let proof = IPA::<Bls12_381>::ipa_improved_commit_and_prove(
            &g_alpha_powers,
            &vector_left,
            &vector_right,
            &domain,
            &mut transcript,
        ).unwrap();
        println!("Improved IPA proof size is {} bytes", IPA::<Bls12_381>::get_proof_size(&proof));
    }
}

fn ipa_verifier_benchmark(c: &mut Criterion) {
    let log_sizes = vec![10, 12, 14, 16, 18, 20];
    let mut rng = StdRng::seed_from_u64(0u64);
    for &log_size in &log_sizes {
        let size = 1 << log_size;
        let degree = size - 1;
        let domain = <GeneralEvaluationDomain<<Bls12_381 as Pairing>::ScalarField> as EvaluationDomain<
            <Bls12_381 as Pairing>::ScalarField>>::new(size).unwrap();
        let mut vector_left = Vec::new();
        let mut vector_right = Vec::new();
        for _ in 0..size {
            vector_left.push(<Bls12_381 as Pairing>::ScalarField::rand(&mut rng));
            vector_right.push(<Bls12_381 as Pairing>::ScalarField::rand(&mut rng));
        }
        let inner_product = vector_left
            .iter()
            .zip(vector_right.iter())
            .map(|(left, right)| left * right)
            .sum();
        let (g_alpha_powers, v_srs) = BatchKZG::<Bls12_381>::setup(&mut rng, degree).unwrap();

        let mut transcript = Transcript::new(b"IPA_commit_and_prove");
        let proof = IPA::<Bls12_381>::trivial_ipa_commit_and_prove(
            &g_alpha_powers,
            &vector_left,
            &vector_right,
            &domain,
            &mut transcript,
        ).unwrap();

        std::thread::sleep(Duration::from_millis(5000));
        c.bench_function(&format!("Trivial_IPA_verifier, log_vector_length: {}", log_size), |b| {
            b.iter(|| {
                let mut transcript = Transcript::new(b"IPA_commit_and_prove");
                let _ = IPA::<Bls12_381>::trivial_ipa_verify(
                    &v_srs,
                    &domain,
                    &inner_product,
                    &proof,
                    &mut transcript,
                );
            });
        });

        let mut transcript = Transcript::new(b"IPA_commit_and_prove");
        let proof = ipa_from_laurent::IPA::<Bls12_381>::ipa_from_laurent_commit_and_prove(
            &g_alpha_powers,
            &vector_left,
            &vector_right,
            &inner_product,
            &domain,
            &mut transcript,
        ).unwrap();
        println!("Laurent IPA proof size is {} bytes", ipa_from_laurent::IPA::<Bls12_381>::get_proof_size(&proof));

        std::thread::sleep(Duration::from_millis(5000));
        c.bench_function(&format!("Laurent_IPA_verifier, log_vector_length: {}", log_size), |b| {
            b.iter(|| {
                let mut transcript = Transcript::new(b"IPA_commit_and_prove");
                let _ = ipa_from_laurent::IPA::<Bls12_381>::ipa_from_laurent_verify(
                    &v_srs,
                    &proof,
                    &inner_product,
                    &domain,
                    &mut transcript,
                );
            });
        });

        let mut transcript: Transcript = Transcript::new(b"IPA_commit_and_prove");
        let proof = IPA::<Bls12_381>::ipa_improved_commit_and_prove(
            &g_alpha_powers,
            &vector_left,
            &vector_right,
            &domain,
            &mut transcript
        ).unwrap();

        std::thread::sleep(Duration::from_millis(5000));
        c.bench_function(&format!("Improved_IPA_verify, log_vector_length: {}", log_size), |b| {
            b.iter(|| {
                let mut transcript = Transcript::new(b"IPA_commit_and_prove");
                let _ = IPA::<Bls12_381>::ipa_improved_verify(
                    &v_srs,
                    &domain,
                    &inner_product,
                    &proof,
                    &mut transcript,
                );
            });
        });

        // c.bench_function(&format!("Trivial_IPA_commit_and_prove, log_vector_length: {}", log_size), |b| {
        //     b.iter(|| {
        //         let mut transcript = Transcript::new(b"IPA_commit_and_prove");
        //         let _ = IPA::<Bls12_381>::trivial_ipa_commit_and_prove(
        //             &g_alpha_powers,
        //             &vector_left,
        //             &vector_right,
        //             &inner_product,
        //             &domain,
        //             &mut transcript,
        //         );
        //     });
        // });

        // c.bench_function(&format!("Improved_IPA_commit_and_prove, log_vector_length: {}", log_size), |b| {
        //     b.iter(|| {
        //         let mut transcript = Transcript::new(b"IPA_commit_and_prove");
        //         let _ = IPA::<Bls12_381>::ipa_improved_commit_and_prove(
        //             &g_alpha_powers,
        //             &vector_left,
        //             &vector_right,
        //             &inner_product,
        //             &domain,
        //             &mut transcript,
        //         );
        //     });
        // });
    }
}

criterion_group!{
    name = benches;
    config = configure_criterion();
    targets = 
    ipa_commit_and_prove_benchmark, 
    ipa_verifier_benchmark,
}
criterion_main!(benches);

// This is the benchmark for univariate batch KZG on opening one point on multiple polynomials
// fn main() {
//     let size: usize = 1 << 20;
//     let degree: usize = (1 << 20) - 1;
//     let mut rng = StdRng::seed_from_u64(0u64);
//     let domain =
//         <GeneralEvaluationDomain<<Bls12_381 as Pairing>::ScalarField> as EvaluationDomain<
//             <Bls12_381 as Pairing>::ScalarField,
//         >>::new(size)
//         .unwrap();
//     let mut vector_left = Vec::new();
//     let mut vector_right = Vec::new();
//     for _ in 0..size {
//         vector_left.push(<Bls12_381 as Pairing>::ScalarField::rand(&mut rng));
//         vector_right.push(<Bls12_381 as Pairing>::ScalarField::rand(&mut rng));
//     }
//     let inner_product = vector_left
//         .iter()
//         .zip(vector_right.iter())
//         .map(|(left, right)| left * right)
//         .sum();
//     let (g_alpha_powers, v_srs) = BatchKZG::<Bls12_381>::setup(&mut rng, degree).unwrap();

//     // Trivial IPA_from_sumcheck prover
//     let prover_start = Instant::now();
//     let mut transcript: Transcript = Transcript::new(b"Trivial IPA from sumcheck");
//     let proof = IPA::<Bls12_381>::trivial_ipa_commit_and_prove(
//         &g_alpha_powers,
//         &vector_left,
//         &vector_right,
//         &inner_product,
//         &domain,
//         &mut transcript,
//     )
//     .unwrap();
//     println!(
//         "Trivial IPA prover time: {:?} ms",
//         prover_start.elapsed().as_millis()
//     );

//     // Trivial IPA_from_sumcheck proof size
//     let proof_size = IPA::<Bls12_381>::get_proof_size(&proof);
//     println!("Trivial IPA proof size: {:?} bytes", proof_size);

//     // Trivial IPA_from_sumcheck verifier
//     std::thread::sleep(Duration::from_millis(5000));
//     let verify_start = Instant::now();
//     for _ in 0..50 {
//         let mut transcript: Transcript = Transcript::new(b"Trivial IPA from sumcheck");
//         let is_valid = IPA::<Bls12_381>::trivial_ipa_verify(
//             &v_srs,
//             &domain,
//             &inner_product,
//             &proof,
//             &mut transcript,
//         )
//         .unwrap();
//         assert!(is_valid);
//     }
//     let verify_time = verify_start.elapsed().as_millis() / 50;
//     println!("Trivial IPA verifier time: {:?} ms", verify_time);

//     // Improved IPA_from_sumcheck prover
//     let prover_start = Instant::now();
//     let mut transcript: Transcript = Transcript::new(b"Trivial IPA from sumcheck");
//     let proof = IPA::<Bls12_381>::ipa_improved_commit_and_prove(
//         &g_alpha_powers,
//         &vector_left,
//         &vector_right,
//         &inner_product,
//         &domain,
//         &mut transcript,
//     )
//     .unwrap();
//     println!(
//         "Improved IPA prover time: {:?} ms",
//         prover_start.elapsed().as_millis()
//     );

//     // Improved IPA_from_sumcheck proof size
//     let proof_size = IPA::<Bls12_381>::get_proof_size(&proof);
//     println!("Improved IPA proof size: {:?} bytes", proof_size);

//     // Improved IPA_from_sumcheck verifier
//     std::thread::sleep(Duration::from_millis(5000));
//     let verify_start = Instant::now();
//     for _ in 0..50 {
//         let mut transcript: Transcript = Transcript::new(b"Trivial IPA from sumcheck");
//         let is_valid = IPA::<Bls12_381>::ipa_improved_verify(
//             &v_srs,
//             &domain,
//             &inner_product,
//             &proof,
//             &mut transcript,
//         )
//         .unwrap();
//         assert!(is_valid);
//     }
//     let verify_time = verify_start.elapsed().as_millis() / 50;
//     println!("Improved IPA verifier time: {:?} ms", verify_time);
// }
