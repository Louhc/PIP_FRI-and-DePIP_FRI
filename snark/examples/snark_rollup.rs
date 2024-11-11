// usage
// RAYON_NUM_THREADS=N RUSTFLAGS='-C target-cpu=native' cargo build --release --example snark_pre --no-default-features --features "parallel asm"
// RAYON_NUM_THREADS=32 ./snark_linear_verifier_test 2 ../../../snark/data/4

use ark_poly::{EvaluationDomain, GeneralEvaluationDomain};
use ark_std::log2;
use my_kzg::biv_batch_kzg::BivBatchKZG;
use merlin::Transcript;
use my_ipa::helper::generate_r1cs_de_polynomials;
use de_network::{DeMultiNet as Net, DeNet, DeSerNet};
use std::path::PathBuf;
use structopt::StructOpt;
use ark_std::rand::{rngs::StdRng, SeedableRng};
use ark_ff::UniformRand;
use std::time::Instant;
use ark_relations::r1cs::{ConstraintSystem, ConstraintSynthesizer};
use my_snark::snark_log::DeSNARKLog;
use my_snark::indexer::Indexer;
use my_ipa::r1cs::R1CSVectors;
use ark_rollup::de_rollup::build_multi_tx_circuit;
use ark_std::{start_timer, end_timer};

use ark_simple_payments::{ConstraintF, ConstraintP};

#[derive(Debug, StructOpt)]
#[structopt(name = "example", about = "An example of StructOpt usage.")]
struct Opt {
    /// Id
    id: usize,

    /// Input file
    #[structopt(parse(from_os_str))]

    input: PathBuf,
}

const NUM_TX: usize = 1 << 5;
const L: usize = 4;

fn init() -> (usize, usize) {
    let opt = Opt::from_args();
    println!("{:?}", opt);
    Net::init_from_file(opt.input.to_str().unwrap(), opt.id);
    let l = Net::n_parties();
    assert_eq!(l, L);
    let sub_prover_id = Net::party_id();
    (l, sub_prover_id)
}

fn test_helper(l: usize, sub_prover_id: usize) {
    let time = Instant::now();
    // In Pianist repo, 3 rollup transaction R1CS constraint number is 1<<18, which is 1 tx of ours
    let num_tx_in_pianist = NUM_TX * 3;
    if NUM_TX % Net::n_parties() != 0 {
        println!("The transaction number is not enough to assign each sub-prover distributedly!");
    }
    let cs = ConstraintSystem::<ConstraintF>::new_ref();
    let _circuit = build_multi_tx_circuit::<NUM_TX, L>().generate_constraints(cs.clone()).unwrap();
    // assert!(cs.is_satisfied().unwrap());
    assert!(cs.is_satisfied().unwrap());

    let cs_matrix = {
        let mut cs = cs.borrow_mut().unwrap();
        cs.finalize();
        cs.to_matrices().unwrap()
    };

    println!("Generate R1CS of {:?} transactions time: {:?}", num_tx_in_pianist, time.elapsed());
    let m = cs.num_constraints() / Net::n_parties();
    println!("number of constraints: {:?}", cs.num_constraints());
    println!("number of variables: {:?}", cs.num_witness_variables() + cs.num_instance_variables());

    let mut rng = StdRng::seed_from_u64(0u64);
    let (_de_row_index_vecs, _de_col_index_vecs, _de_val_evals_vecs, m_prime): (Vec<_>, Vec<_>, Vec<_>, usize) = Indexer::<ConstraintP>::build_de_r1cs_index(l, m, &cs_matrix).unwrap();
    println!("log m_prime: {:?}", log2(m_prime));

    let time = Instant::now();
    let challenge_r = ConstraintF::rand(&mut rng);
    let domain_x = <GeneralEvaluationDomain<ConstraintF> as EvaluationDomain<ConstraintF>>::new(m).unwrap();
    let domain_y = <GeneralEvaluationDomain<ConstraintF> as EvaluationDomain<ConstraintF>>::new(l).unwrap();
    let domain_m = if m == m_prime {
        domain_x.clone()
    } else {
        <GeneralEvaluationDomain<ConstraintF> as EvaluationDomain<ConstraintF>>::new(m_prime).unwrap()
    };

    let x_degree = m - 1;
    let y_degree = l - 1;
    let m_degree = m_prime - 1;
    let ((powers, x_srs, y_srs), v_srs) = BivBatchKZG::<ConstraintP>::setup_lagrange(&mut rng, x_degree, y_degree, &domain_y).unwrap();

    let ((m_powers, m_srs, m_y_srs), m_v_srs) = {
        if x_degree == m_degree {
            ((powers.clone(), x_srs.clone(), y_srs.clone()), v_srs.clone())
        } else {
            BivBatchKZG::<ConstraintP>::setup_lagrange(&mut rng, m_degree, y_degree, &domain_y).unwrap()
        }
    };
    println!("Setup time: {:?}", time.elapsed());

    // indexer works
    // common preprocess
    let time = Instant::now();
    let (pre_mes_prover, pre_mes_verifier) = Indexer::<ConstraintP>::preprocess(sub_prover_id, m, l, &cs_matrix, &powers, &m_powers, &x_srs, &domain_x, &domain_y, &domain_m);
    // new preprocess to file
    // let (pre_mes_prover, pre_mes_verifier) = Indexer::<ConstraintP>::new_preprocess_to_file(m, l, &cs, &powers, &m_powers, &x_srs, &domain_x, &domain_y, &domain_m);
    // println!("Prover {:?} Indexer time: {:?}", sub_prover_id, time.elapsed());
    // preprocess from file
    // let (pre_mes_prover, pre_mes_verifier) = match Indexer::<ConstraintP>::preprocess_from_file(m, l) {
    //     Ok(pre) => pre,
    //     Err(_) => Indexer::<ConstraintP>::new_preprocess_to_file(m, l, &cs, &powers, &m_powers, &x_srs, &domain_x, &domain_y, &domain_m)
    // };
    println!("Indexer time: {:?}", time.elapsed());

    // Synchronize everyone
    Net::recv_from_master(if Net::am_master() {
        Some(vec![0usize; Net::n_parties()])
    } else {
        None
    });

    // prover
    println!("Prover {:?} starts to prove", sub_prover_id);
    let timer1 = start_timer!(|| "Prover starts to prove");
    let mut transcript : Transcript = Transcript::new(b"Random R1CS");
    let timer2 = start_timer!(|| "Build r1cs vecs and polys");
    let r1cs_de_vecs: R1CSVectors<ConstraintP> = R1CSVectors::<ConstraintP>::build(sub_prover_id, m, l, challenge_r, &cs, &cs_matrix).unwrap();

    //self tets
    // let vec_r = generate_powers(&challenge_r, m * l);
    // assert_eq!(inner_product::<ConstraintP>(&r1cs_de_vecs.vec_x, &r1cs_de_vecs.vec_w), inner_product::<ConstraintP>(&r1cs_de_vecs.vec_a, &vec_r));
    // assert_eq!(inner_product::<ConstraintP>(&r1cs_de_vecs.vec_y, &r1cs_de_vecs.vec_w), inner_product::<ConstraintP>(&r1cs_de_vecs.vec_b, &vec_r));
    // assert_eq!(inner_product::<ConstraintP>(&r1cs_de_vecs.vec_z, &r1cs_de_vecs.vec_w), inner_product::<ConstraintP>(&r1cs_de_vecs.vec_c, &vec_r));
    //self test over

    let (sub_pub_polys, sub_wit_polys) = generate_r1cs_de_polynomials::<ConstraintP>(m, l, r1cs_de_vecs);
    end_timer!(timer2);
    let proof = DeSNARKLog::<ConstraintP>::de_r1cs_prove(sub_prover_id, &powers, 
        &m_powers, &x_srs, &y_srs, &m_srs, &m_y_srs,  &sub_wit_polys, &sub_pub_polys, &pre_mes_prover,
        &challenge_r, &domain_x, &domain_y, &domain_m, &mut transcript);
    end_timer!(timer1);

    if Net::am_master() {
        let proof_size = DeSNARKLog::<ConstraintP>::get_proof_size(proof.as_ref().unwrap());
        println!("Proof size is {:?} bytes", proof_size);
    }

    let time = Instant::now();
    if Net::am_master() {
        let mut transcript : Transcript = Transcript::new(b"Random R1CS");
        let is_valid = DeSNARKLog::<ConstraintP>::r1cs_verify_preprocess(&v_srs, &m_v_srs, 
            &pre_mes_verifier, &proof.unwrap(), &domain_x, &domain_y, &domain_m, &challenge_r, &mut transcript);
        assert!(is_valid);
    }
    println!("Verify time: {:?}", time.elapsed());
}

fn main() {
    let (l, sub_prover_id) = init();
    // test_helper::<ConstraintP>(num_tx, l, sub_prover_id);
    test_helper(l, sub_prover_id);
    Net::deinit();
}