use ark_bls12_381::Bls12_381;
use ark_ec::pairing::Pairing;
use ark_ff::Zero;
use my_kzg::trivial_kzg::{KZG, DeKZG};
use ark_poly::polynomial::{
    univariate::DensePolynomial as UnivariatePolynomial, DenseUVPolynomial
};
use ark_std::rand::{rngs::StdRng, SeedableRng};
use ark_ff::UniformRand;
use std::time::{
    Instant,
    // Duration
};
use std::path::PathBuf;
use structopt::StructOpt;
use de_network::{DeMultiNet as Net, DeNet, DeSerNet};

#[derive(Debug, StructOpt)]
#[structopt(name = "example", about = "An example of StructOpt usage.")]
struct Opt {
    /// Id
    id: usize,

    /// Input file
    #[structopt(parse(from_os_str))]
    input: PathBuf,
}

fn init() -> (usize, usize) {
    let opt = Opt::from_args();
    println!("{:?}", opt);
    Net::init_from_file(opt.input.to_str().unwrap(), opt.id);
    // let l = Net::n_parties();
    let sub_prover_id = Net::party_id();
    let m = 10;

    println!("log_degree: {:?}", m);

    (m, sub_prover_id)
}

fn main() {
    let (m, sub_prover_id) = init();
    let degree = (1usize << m) - 1;
    let mut rng = StdRng::seed_from_u64(0u64);
    let setup_start = Instant::now();
    let (g_alpha_powers, v_srs) = KZG::<Bls12_381>::setup(&mut rng, degree).unwrap();
    println!("Prover {:?} setup time: {:?}", sub_prover_id, setup_start.elapsed());

    let point = if Net::am_master() {
        let point = <Bls12_381 as Pairing>::ScalarField::rand(&mut rng);
        Net::recv_from_master(Some(vec![point.clone(); Net::n_parties()]));
        point
    } else {
        Net::recv_from_master(None)
    };

    let sub_polynomials = if Net::am_master() {
        let polynomial = UnivariatePolynomial::rand(degree, &mut rng);
        let mut sub_polynomials = Vec::new();
        let mut sum_polynomial = UnivariatePolynomial::from_coefficients_vec(vec![<Bls12_381 as Pairing>::ScalarField::zero()]);
    
        for _ in 0..Net::n_parties()-1 {
            let current_polynomial = UnivariatePolynomial::rand(degree, &mut rng);
            sum_polynomial += &current_polynomial;
            sub_polynomials.push(current_polynomial);
        }
        sub_polynomials.push(&polynomial - &sum_polynomial);
        assert_eq!(sub_polynomials.len(), Net::n_parties());

        Net::recv_from_master(Some(vec![sub_polynomials.clone(); Net::n_parties()]));
        sub_polynomials
    } else {
        Net::recv_from_master(None)
    };

    let time = Instant::now();
    let com = DeKZG::<Bls12_381>::de_commit(&g_alpha_powers, &sub_polynomials[sub_prover_id]);
    println!("Prover {:?} committing time: {:?}", sub_prover_id, time.elapsed());

    let eval = DeKZG::<Bls12_381>::de_evaluate(&sub_polynomials[sub_prover_id], &point);

    let proof = DeKZG::<Bls12_381>::de_open(&g_alpha_powers, &sub_polynomials[sub_prover_id], &point);

    if Net::am_master() {
        let time = Instant::now();
        let is_valid =
        KZG::<Bls12_381>::verify(&v_srs, &com.unwrap(), &point, &eval.unwrap(), &proof.unwrap()).unwrap();
        assert!(is_valid);
        println!("verify time: {:?}", time.elapsed());
    }

}
