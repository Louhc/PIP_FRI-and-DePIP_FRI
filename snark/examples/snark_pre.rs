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
use std::path::PathBuf;
use structopt::StructOpt;
use ark_std::rand::{rngs::StdRng, SeedableRng};
use ark_bls12_381::Bls12_381;
use ark_ff::UniformRand;
type MyField = <Bls12_381 as Pairing>::ScalarField;
use std::time::Instant;
use ark_relations::r1cs::{ConstraintSystem, ConstraintSynthesizer};
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
    let m = 1 << 22;
    (m, l, sub_prover_id)
}

fn main() {
    let (m, l, sub_prover_id) = init();

    let time = Instant::now();
    let c = RandomCircuit::<Bls12_381>::new(m * l, m * l, m, l);
    let cs = ConstraintSystem::<<Bls12_381 as Pairing>::ScalarField>::new_ref();
    c.generate_constraints(cs.clone()).unwrap();
    assert!(cs.is_satisfied().unwrap());
    println!("Generate R1CS instances time: {:?}", time.elapsed());

    let mut rng = StdRng::seed_from_u64(0u64);
    let (_de_row_index_vecs, _de_col_index_vecs, _de_val_evals_vecs, pow_of_two): (Vec<_>, Vec<_>, Vec<_>, usize) = Indexer::<Bls12_381>::build_de_r1cs_index(l, m, &cs).unwrap();
    let m_prime: usize = pow_of_two;
    println!("log m_prime: {:?}", log2(pow_of_two));

    let time = Instant::now();
    let challenge_r = MyField::rand(&mut rng);
    let domain_x = <GeneralEvaluationDomain<MyField> as EvaluationDomain<MyField>>::new(m).unwrap();
    let domain_y = <GeneralEvaluationDomain<MyField> as EvaluationDomain<MyField>>::new(l).unwrap();
    let domain_m = if m == m_prime {
        domain_x.clone()
    } else {
        <GeneralEvaluationDomain<MyField> as EvaluationDomain<MyField>>::new(m_prime).unwrap()
    };

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

    // indexer works
    // common preprocess
    // let (pre_mes_prover, pre_mes_verifier) = Indexer::<Bls12_381>::preprocess(m, l, &cs, &powers, &m_powers, &x_srs, &domain_x, &domain_y, &domain_m);
    // new preprocess to file
    // let (pre_mes_prover, pre_mes_verifier) = if Net::am_master() {
    //      let time = Instant::now();
    //      Indexer::<Bls12_381>::new_preprocess_to_file(m, l, &cs, &powers, &m_powers, &x_srs, &domain_x, &domain_y, &domain_m)
    //      println!("Prover {:?} Indexer time: {:?}", sub_prover_id, time.elapsed());
    // } else {
    //     Indexer::<Bls12_381>::preprocess_from_file(m, l)
    // };
    // preprocess from file
    let (pre_mes_prover, pre_mes_verifier) = Indexer::<Bls12_381>::preprocess_from_file(m, l);

    // prover
    println!("Prover {:?} starts to prove", sub_prover_id);
    let total_time = Instant::now();
    let mut transcript : Transcript = Transcript::new(b"Random R1CS");
    let time = Instant::now();
    let r1cs_de_vecs: R1CSVectors<Bls12_381> = R1CSVectors::<Bls12_381>::build(sub_prover_id, m, l, challenge_r, &cs).unwrap();
    let (sub_pub_polys, sub_wit_polys) = generate_r1cs_de_polynomials::<Bls12_381>(m, l, &r1cs_de_vecs);
    println!("Prover {:?} generates de secret polynomials time: {:?}", sub_prover_id, time.elapsed());
    let proof = DeSNARKLog::<Bls12_381>::de_r1cs_prove(sub_prover_id, &powers, 
        &m_powers, &x_srs, &y_srs, &m_srs, &sub_wit_polys, &sub_pub_polys, &pre_mes_prover,
        &challenge_r, &domain_x, &domain_y, &domain_m, &mut transcript);
    println!("Prover {:?} prove total time: {:?}", sub_prover_id, total_time.elapsed());

    if Net::am_master() {
        let proof_size = DeSNARKLog::<Bls12_381>::get_proof_size(proof.as_ref().unwrap());
        println!("Proof size is {:?} bytes", proof_size);
    }

    let time = Instant::now();
    if Net::am_master() {
        let mut transcript : Transcript = Transcript::new(b"Random R1CS");
        let is_valid = DeSNARKLog::<Bls12_381>::r1cs_verify_preprocess(&v_srs, &m_v_srs, 
            &pre_mes_verifier, &proof.unwrap(), &domain_x, &domain_y, &domain_m, &challenge_r, &mut transcript);
        assert!(is_valid);
    }
    println!("Verify time: {:?}", time.elapsed());
}