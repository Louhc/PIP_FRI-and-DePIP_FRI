use ark_bls12_381::Bls12_381;
use ark_ec::pairing::Pairing;
use my_kzg::biv_batch_kzg::BivBatchKZG;
use ark_poly::polynomial::{
    univariate::DensePolynomial as UnivariatePolynomial, DenseUVPolynomial, Polynomial
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
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain};
use merlin::Transcript;
use my_kzg::transcript::ProofTranscript;

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
    let m = 15;
    (m, l, sub_prover_id)
}

fn main() {
    let (m, l, sub_prover_id) = init();
    let x_degree = (1usize << m) - 1;
    assert!(l.is_power_of_two());
    let y_degree = l - 1;
    let polynomial_number: usize = 4;
    
    let mut rng = StdRng::seed_from_u64(0u64);
    let domain = <GeneralEvaluationDomain<<Bls12_381 as Pairing>::ScalarField> as EvaluationDomain<<Bls12_381 as Pairing>::ScalarField>>::new(l).unwrap();

    let setup_start = Instant::now();
    let srs = BivBatchKZG::<Bls12_381>::setup_lagrange(&mut rng, x_degree, y_degree, &domain).unwrap();
    // generate x_srs
    println!("Prover {:?} setup time: {:?}", sub_prover_id, setup_start.elapsed());

    // let time = Instant::now();
    let polys_x_polynomials = if Net::am_master() {
        let mut polys_x_polynomials = Vec::new();
        for _ in 0..polynomial_number {
            let mut x_polynomials = Vec::new();
            for _ in 0..y_degree + 1 {
                let mut x_polynomial_coeffs = vec![];
                for _ in 0..(x_degree + 1)/2 {
                    x_polynomial_coeffs.push(<Bls12_381 as Pairing>::ScalarField::rand(&mut rng));
                }
                x_polynomials.push(UnivariatePolynomial::from_coefficients_slice(
                    &x_polynomial_coeffs,
                ));
            }
            polys_x_polynomials.push(x_polynomials);
        }
        Net::recv_from_master(Some(vec![polys_x_polynomials.clone(); Net::n_parties()]));
        polys_x_polynomials
    } else {
        Net::recv_from_master(None)
    };
    let sub_polynomials : Vec<_> = polys_x_polynomials.iter().map(|x_polynomials| &x_polynomials[sub_prover_id]).collect();

    let (y_point, x_point) = if Net::am_master() {
        let y_point = <Bls12_381 as Pairing>::ScalarField::rand(&mut rng);
        let x_point = <Bls12_381 as Pairing>::ScalarField::rand(&mut rng);

        Net::recv_from_master(Some(vec![(y_point.clone(), x_point.clone()); Net::n_parties()]));
        (y_point, x_point)
    } else {
        Net::recv_from_master(None)
    };
    // println!("Prover {:?} generates random polynomials and evaluation time: {:?}", sub_prover_id, time.elapsed());

    let time = Instant::now();
    let coms = BivBatchKZG::<Bls12_381>::de_commit(sub_prover_id, &srs.0, &sub_polynomials);
    println!("Prover {:?} committing time: {:?}", sub_prover_id, time.elapsed());

    // de-eval
    let evals_slice: Vec<<Bls12_381 as Pairing>::ScalarField> = sub_polynomials.iter().map(|poly| poly.evaluate(&x_point)).collect();

    // de-eval, equlivantly
    // let mut evals_slice: Vec<<Bls12_381 as Pairing>::ScalarField> = Vec::new();
    // for i in 0..polynomial_number {
    //     let eval = sub_polynomials[i].evaluate(&x_point);
    //     evals_slice.push(eval);
    // }
    // let evals_vec = Net::send_to_master(&evals_slice);
    // let evals = if Net::am_master() {
    //     let mut evals: Vec<<Bls12_381 as Pairing>::ScalarField> = Vec::new();
    //     let evals_vec = evals_vec.unwrap();
    //     let evals_lagrange = EvaluationDomain::evaluate_all_lagrange_coefficients(&domain, y_point);
    //     for i in 0..polynomial_number {
    //         let eval = evals_vec.iter().zip(evals_lagrange.iter()).map(|(eval_slice, eval_lagrange)| eval_slice[i] * eval_lagrange).sum();
    //         evals.push(eval);
    //     }
    //     evals
    // } else {
    //     Vec::new()
    // };

    // de-open
    let time = Instant::now();
    let mut prover_transcript : Transcript = Transcript::new(b"batch bivariate KZG at the same y");
    let gamma = <Transcript as ProofTranscript<Bls12_381>>::challenge_scalar(
        &mut prover_transcript, b"combined_polynomial_x_beta");
    let proof = BivBatchKZG::<Bls12_381>::de_open_lagrange_with_eval(sub_prover_id, &srs.0, &sub_polynomials, &evals_slice, &(x_point, y_point), &domain, &gamma);
    println!("Prover {:?} open time: {:?}", sub_prover_id, time.elapsed());

    // verify
    if Net::am_master() {
        let time = Instant::now();
        let (evals, proof) = proof.unwrap();
        for _ in 0..50 {
            let mut verifier_transcript : Transcript = Transcript::new(b"batch bivariate KZG at the same y");
            let gamma = <Transcript as ProofTranscript<Bls12_381>>::challenge_scalar(
                &mut verifier_transcript, b"combined_polynomial_x_beta");
            let is_valid = BivBatchKZG::<Bls12_381>::verify(&srs.1, &coms.clone().unwrap(), &(x_point, y_point), &evals, &proof.clone(), &gamma).unwrap();
            assert!(is_valid);
        }
        println!("Verifier time: {:?}", time.elapsed()/50);
    }

}
