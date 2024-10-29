// usage
// RAYON_NUM_THREADS=32 cargo build --release --example snark_linear_verifier_test --no-default-features --features "parallel"
// RAYON_NUM_THREADS=32 ./snark_linear_verifier_test 2 ../../../snark/data/4

use ark_poly::{EvaluationDomain, GeneralEvaluationDomain};
use ark_ec::pairing::Pairing;
use ark_std::log2;
use my_kzg::{biv_batch_kzg::BivBatchKZG, helper::get_x_srs};
use merlin::Transcript;
use my_ipa::{helper::generate_r1cs_de_polynomials, r1cs::RandomCircuit};
use de_network::{DeMultiNet as Net, DeNet};
use rayon::iter::IntoParallelRefIterator;
use std::path::PathBuf;
use structopt::StructOpt;
use ark_std::rand::{rngs::StdRng, SeedableRng};
use ark_bls12_381::Bls12_381;
use ark_ff::UniformRand;
type MyField = <Bls12_381 as Pairing>::ScalarField;
use std::time::Instant;
// use my_ipa::r1cs::{RandomCircuit, R1CSVectors};
use ark_relations::r1cs::{ConstraintSystem, ConstraintSynthesizer};
use rayon::prelude::*;
use my_snark::prover_pre::{DeLowerAandBEvals, DeLowerAandBPolys};
use my_snark::snark_log::DeSNARKLog;
use my_snark::indexer::Indexer;
use my_ipa::r1cs::R1CSVectors;

#[derive(Debug, StructOpt)]
#[structopt(name = "example", about = "An example of StructOpt usage.")]
struct Opt {
    /// Id
    id: usize,

    /// Input file
    #[structopt(parse(from_os_str))]

    input: PathBuf,
}

fn init() -> (usize, usize, usize) {
    let opt = Opt::from_args();
    println!("{:?}", opt);
    Net::init_from_file(opt.input.to_str().unwrap(), opt.id);
    let l = Net::n_parties();
    let sub_prover_id = Net::party_id();
    let m = 1 << 10;
    (m, l, sub_prover_id)
}

// update to true r1cs
fn main() {
    let (m, l, sub_prover_id) = init();

    let time = Instant::now();
    let c = RandomCircuit::<Bls12_381>::new(m * l, m * l);
    let cs = ConstraintSystem::<<Bls12_381 as Pairing>::ScalarField>::new_ref();
    c.generate_constraints(cs.clone()).unwrap();
    assert!(cs.is_satisfied().unwrap());
    println!("Generate R1CS instances time: {:?}", time.elapsed());

    let mut rng = StdRng::seed_from_u64(0u64);
    let (_de_row_index_vecs, _de_col_index_vecs, _de_val_evals_vecs, pow_of_two): (Vec<_>, Vec<_>, Vec<_>, usize) = Indexer::<Bls12_381>::build_de_r1cs_index(l, m, &cs).unwrap();
    let m_prime: usize = pow_of_two;
    assert!(m_prime.is_power_of_two());
    println!("log m_prime: {:?}", log2(pow_of_two));

    let time = Instant::now();
    let challenge_r = MyField::rand(&mut rng);
    let domain_x = <GeneralEvaluationDomain<MyField> as EvaluationDomain<MyField>>::new(m).unwrap();
    let domain_y = <GeneralEvaluationDomain<MyField> as EvaluationDomain<MyField>>::new(l).unwrap();
    let domain_m = <GeneralEvaluationDomain<MyField> as EvaluationDomain<MyField>>::new(m_prime).unwrap();

    let x_degree = m - 1;
    let y_degree = l - 1;
    let m_degree = m_prime - 1;
    let (powers, v_srs) = BivBatchKZG::<Bls12_381>::setup_lagrange(&mut rng, x_degree, y_degree, &domain_y).unwrap();
    let x_srs = get_x_srs::<Bls12_381>(&powers);
    // Note that y_srs is lagrange-based
    let y_srs: Vec<<Bls12_381 as Pairing>::G1Affine> = powers.iter()
        .filter_map(|row| row.get(0))
        .cloned()
        .collect();

    let (m_powers, m_v_srs) = {
        if x_degree == m_degree {
            (powers.clone(), v_srs.clone())
        } else {
            BivBatchKZG::<Bls12_381>::setup_lagrange(&mut rng, m_degree, y_degree, &domain_y).unwrap()
        }
    };
    let m_srs = get_x_srs::<Bls12_381>(&m_powers);
    println!("Setup time: {:?}", time.elapsed());

    // Someone does to generate the R1CS distributed vectors
    let time = Instant::now(); 
    let r1cs_vecs_all: Vec<R1CSVectors<Bls12_381>> = (0..l).map(|sub_prover_id| {
        R1CSVectors::<Bls12_381>::build(sub_prover_id, m, l, challenge_r, &cs).unwrap()
        }).collect();
    println!("Generate the R1CS de-vectors time: {:?}", time.elapsed());

    // indexer works
    let time = Instant::now();
    let (de_row_index_vecs, de_col_index_vecs, de_val_evals_vecs, _pow_of_two): (Vec<_>, Vec<_>, Vec<_>, usize) = Indexer::<Bls12_381>::build_de_r1cs_index(l, m, &cs).unwrap();
    let (upper_r_polys, com_upper_r) = Indexer::<Bls12_381>::compute_and_commit_poly_upper_r(&powers, l);
    let val_polys = Indexer::<Bls12_381>::compute_val_polys(l, &domain_m, &de_val_evals_vecs);
    let coms_val = Indexer::<Bls12_381>::commit_val_polys(&m_powers, &val_polys);
    let total_lower_a_b_evals_and_polys: Vec<(DeLowerAandBEvals<Bls12_381>, DeLowerAandBPolys<Bls12_381>)> = {
        (0..Net::n_parties()).into_par_iter().map(|i| Indexer::<Bls12_381>::compute_lower_a_b_evals_and_polys(i, &de_row_index_vecs, &de_col_index_vecs, &domain_m, &domain_x)).collect()
    };
    let (total_lower_a_b_evals, total_lower_a_b_polys): (Vec<DeLowerAandBEvals<Bls12_381>>, Vec<DeLowerAandBPolys<Bls12_381>>) = {
        (
            total_lower_a_b_evals_and_polys.par_iter().map(|eval_poly| eval_poly.0.clone()).collect(), 
            total_lower_a_b_evals_and_polys.par_iter().map(|eval_poly| eval_poly.1.clone()).collect(), 
        )
    };
    let (lower_a_b_evals, lower_a_b_polys) = (total_lower_a_b_evals[sub_prover_id].clone(), total_lower_a_b_polys[sub_prover_id].clone());
    let coms_lower_a_b = Indexer::<Bls12_381>::commit_lower_a_b_polys(&m_powers, &total_lower_a_b_polys);
    let n_evals = Indexer::<Bls12_381>::build_n_evals(&de_row_index_vecs, &de_col_index_vecs, l, m, m_prime);
    let n_polys = Indexer::<Bls12_381>::compute_n_polys(&domain_x, &n_evals);
    let coms_n = Indexer::<Bls12_381>::commit_n_polys(&x_srs, &n_polys);
    let com_l = Indexer::<Bls12_381>::commit_poly_upper_l(&powers, l, &domain_y);
    println!("Indexer time: {:?}", time.elapsed());

    // prover
    let total_time = Instant::now();
    let time = Instant::now();
    let mut transcript : Transcript = Transcript::new(b"R1CS inner product");
    let r1cs_de_vecs = r1cs_vecs_all[sub_prover_id].clone();
    let (sub_pub_polys, sub_wit_polys) = generate_r1cs_de_polynomials::<Bls12_381>(m, l, &r1cs_de_vecs);
    println!("Prover {:?} generates de secret polynomials time: {:?}", sub_prover_id, time.elapsed());
    let proof = DeSNARKLog::<Bls12_381>::de_r1cs_prove(sub_prover_id, &powers, 
        &m_powers, &x_srs, &y_srs, &m_srs, &sub_wit_polys, &sub_pub_polys, &upper_r_polys[sub_prover_id],
        &de_row_index_vecs[sub_prover_id], &de_col_index_vecs[sub_prover_id], &val_polys[sub_prover_id], 
        &lower_a_b_evals, &lower_a_b_polys, &n_evals, &n_polys,
        &challenge_r, &domain_x, &domain_y, &domain_m, &mut transcript);
    println!("Prover {:?} prove total time: {:?}", sub_prover_id, total_time.elapsed());

    if Net::am_master() {
        let proof_size = DeSNARKLog::<Bls12_381>::get_proof_size(proof.as_ref().unwrap());
        println!("Proof size is {:?} bytes", proof_size);
    }

    let time = Instant::now();
    if Net::am_master() {
        let mut transcript : Transcript = Transcript::new(b"R1CS inner product");
        let is_valid = DeSNARKLog::<Bls12_381>::r1cs_verify_preprocess(&v_srs, &m_v_srs, &com_upper_r, &coms_val, 
            &coms_lower_a_b, 
            &com_l, &coms_n, &proof.unwrap(), &domain_x, &domain_y, &domain_m, &challenge_r, &mut transcript);
        assert!(is_valid);
    }
    println!("Verify time: {:?}", time.elapsed());
}