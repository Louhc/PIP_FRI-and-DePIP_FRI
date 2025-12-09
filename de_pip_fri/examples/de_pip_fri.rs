use ark_ff::One;
use ark_ff::UniformRand;
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain};
use de_network::{DeMultiNet as Net, DeNet, DeSerNet};
use de_pip_fri::deprover::DeProver;
use de_pip_fri::verifier::Verifier;
use rand::rngs::StdRng;
use rand::SeedableRng;
use std::fs;
use std::mem::size_of;
use std::path::PathBuf;
use std::time::Instant;
use structopt::StructOpt;
use time_logger::LOGGER;
use utils::fiat_shamir::RandomOracle;
use utils::goldilocks::Goldilocks as T;
use utils::helper::nearest_power_of_two;
use utils::helper::Helper;
use utils::helper::MultilinearPolynomial;
use utils::interpolate_vecs_value::*;
use utils::merkle_tree::MERKLE_ROOT_SIZE;
use utils::time_logger;
use utils::{CODE_RATE, SECURITY_BITS};

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
    let num_parties = Net::n_parties();
    assert!(num_parties.is_power_of_two());
    assert!(num_parties != 1);

    let sub_prover_id = Net::party_id();
    let variable_num: usize = 20;

    (variable_num, num_parties, sub_prover_id)
}

fn main() {
    let (variable_num, _num_parties, sub_prover_id) = init();

    fs::create_dir_all("data").unwrap();
    let output_file = format!("data/{}.txt", sub_prover_id);
    LOGGER.lock().unwrap().init(output_file);

    let n = Net::n_parties();

    let (_poly, sub_polys, eval, sub_variable_num, sub_open_point, tensor) = if Net::am_master() {
        let mut rng = StdRng::seed_from_u64(0u64);

        let polynomial = MultilinearPolynomial::rand(variable_num);
        let point = (0..variable_num)
            .map(|_| T::rand(&mut rng))
            .collect::<Vec<T>>();
        let eval = polynomial.evaluate(&point);

        // Divide and generate public informations
        let poly_num = get_poly_num(&polynomial);
        let sub_polynomials = polynomial.chunks(poly_num);

        let mut sub_polys_coeffs = Vec::new();
        for i in 0..n {
            let tmp: Vec<T> = (i * (poly_num / n)..(i + 1) * (poly_num / n))
                .flat_map(|j| sub_polynomials[j].coefficients().to_vec())
                .collect();
            sub_polys_coeffs.push(tmp);
        }

        let sub_variable_num = get_sub_variable_num(&polynomial);
        let (sub_open_point, remaining_var) = point.split_at(sub_variable_num);
        let tensor = get_tensor(&remaining_var.to_vec());

        (
            Some(polynomial),
            Net::recv_from_master(Some(sub_polys_coeffs)),
            Net::recv_from_master(Some(vec![eval; n])),
            Net::recv_from_master(Some(vec![sub_variable_num; n])),
            Net::recv_from_master(Some(vec![sub_open_point.to_vec(); n])),
            Net::recv_from_master(Some(vec![tensor; n])),
        )
    } else {
        (
            None,
            Net::recv_from_master(None),
            Net::recv_from_master(None),
            Net::recv_from_master(None),
            Net::recv_from_master(None),
            Net::recv_from_master(None),
        )
    };

    let setup_size_bytes_recv = Net::stats().bytes_recv;
    let setup_size_bytes_sent = Net::stats().bytes_sent;

    // Setup
    let mut interpolate_cosets =
        vec![
            GeneralEvaluationDomain::new_coset(1 << (sub_variable_num + CODE_RATE), T::one())
                .unwrap(),
        ];
    for i in 1..sub_variable_num {
        interpolate_cosets.push(Helper::pow(&interpolate_cosets[i - 1], 2));
    }

    let oracle = if Net::am_master() {
        Some(RandomOracle::new(
            sub_variable_num,
            SECURITY_BITS / CODE_RATE,
        ))
    } else {
        None
    };

    let total_poly_num = nearest_power_of_two(variable_num * 4);
    let poly_num_per_party = total_poly_num / n;
    let chunk_size = sub_polys.len() / poly_num_per_party;
    assert_eq!(chunk_size, 1 << sub_variable_num);

    if Net::am_master() {
        println!("poly_num_per_party: {}", poly_num_per_party);
        println!("sub_variable_num: {}", sub_variable_num);
        println!("chunk_size: {}", chunk_size);
    }

    let sub_polys: Vec<MultilinearPolynomial<T>> = (0..poly_num_per_party)
        .map(|i| {
            MultilinearPolynomial::new(sub_polys[i * chunk_size..(i + 1) * chunk_size].to_vec())
        })
        .collect();

    let mut de_prover = DeProver::new(
        sub_variable_num,
        sub_prover_id,
        &interpolate_cosets,
        sub_polys,
        oracle.as_ref(),
        &tensor,
    );

    // println!(
    //     "id: {}, Net::stats().bytes_recv: {}",
    //     sub_prover_id,
    //     Net::stats().bytes_recv - setup_size_bytes_recv
    // );
    // println!(
    //     "id: {}, Net::stats().bytes_sent: {}",
    //     sub_prover_id,
    //     Net::stats().bytes_sent - setup_size_bytes_sent
    // );

    let commit_2_time = Instant::now();
    let (com, sub_com) = de_prover.de_commit_polynomial();
    LOGGER
        .lock()
        .unwrap()
        .record(commit_2_time.elapsed().as_secs_f64());

    let mut verifier = if Net::am_master() {
        Some(Verifier::new(
            sub_variable_num,
            com.unwrap(),
            &interpolate_cosets,
            &oracle.as_ref().unwrap(),
            &sub_open_point,
            &tensor,
        ))
    } else {
        None
    };

    let open_time = Instant::now();
    let (polynomial_proof, folding_proof, function_proof) =
        de_prover.de_open(&sub_com, &sub_open_point, verifier.as_mut());
    LOGGER
        .lock()
        .unwrap()
        .record(open_time.elapsed().as_secs_f64());

    // this is indeed larger than the actual communication

    // println!(
    //     "id: {}, Net::stats().bytes_recv: {}",
    //     sub_prover_id,
    //     Net::stats().bytes_recv - setup_size_bytes_recv
    // );
    // println!(
    //     "id: {}, Net::stats().bytes_sent: {}",
    //     sub_prover_id,
    //     Net::stats().bytes_sent - setup_size_bytes_sent
    // );

    let sent_bytes = Net::stats().bytes_sent - setup_size_bytes_sent;

    // verify
    if Net::am_master() {
        let proof_size = folding_proof.iter().map(|x| x.proof_size()).sum::<usize>()
            + polynomial_proof.proof_size()
            + function_proof.iter().map(|x| x.proof_size()).sum::<usize>()
            + (2 * sub_variable_num - 3) * MERKLE_ROOT_SIZE
            + 2 * size_of::<T>();
        LOGGER.lock().unwrap().record((proof_size as f64 / 1024.0 / 1024.0) as f64);
        println!("proof size is: {:?}", (proof_size / 1024) as f64);
        let time = Instant::now();
        assert!(verifier
            .unwrap()
            .verify(&polynomial_proof, &folding_proof, &function_proof, eval));
        println!("Verify time: {:?}", time.elapsed());
        LOGGER.lock().unwrap().record(time.elapsed().as_secs_f64());
    }

    LOGGER.lock().unwrap().record((sent_bytes as f64 / 1024.0 / 1024.0) as f64);

    LOGGER.lock().unwrap().flush();
}
