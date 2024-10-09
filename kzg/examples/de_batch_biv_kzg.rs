use ark_bls12_381::Bls12_381;
use ark_ec::pairing::Pairing;
use ark_ff::Zero;
use my_kzg::{biv_trivial_kzg::BivariatePolynomial, biv_batch_kzg::BivBatchKZG};
use my_kzg::trivial_kzg::{KZG, DeKZG};
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
    let m = 10;
    (m, l, sub_prover_id)
}

// Test for simple multiplications
fn main () {
    let (m, l, sub_prover_id) = init();
    let degree = (1usize << m) - 1;
    assert!(l.is_power_of_two());
    let mut rng = StdRng::seed_from_u64(0u64);
    let times = 1000;
    let time = Instant::now();
    let mut polynomials: Vec<UnivariatePolynomial<<Bls12_381 as Pairing>::ScalarField>> = Vec::new();
    for _ in 0..times {
        let poly1: UnivariatePolynomial<<Bls12_381 as Pairing>::ScalarField> = UnivariatePolynomial::rand(degree, &mut rng);
        let poly2: UnivariatePolynomial<<Bls12_381 as Pairing>::ScalarField> = UnivariatePolynomial::rand(degree, &mut rng);
        let poly = &poly1 * &poly2;
        polynomials.push(poly);
    }
    println!("Prover {:?} time: {:?}", sub_prover_id, time.elapsed());
    let polynomials_collect = Net::send_to_master(&polynomials);
    let polynomials = if Net::am_master() {
        let polynomials_sum = polynomials_collect.unwrap();
        let mut target_poly = vec![UnivariatePolynomial::from_coefficients_vec(vec![<Bls12_381 as Pairing>::ScalarField::zero()]); times];
        for i in 0..polynomials_sum.len() {
            for j in 0..polynomials_sum[i].len() {
                target_poly[j] += &polynomials_sum[i][j];
            }
        }
        Some(target_poly)
    } else {
        None
    };
    if Net::am_master() {
        let time = Instant::now();
        let mut polynomials: Vec<UnivariatePolynomial<<Bls12_381 as Pairing>::ScalarField>> = Vec::new();
        for _ in 0..times * Net::n_parties() {
            let poly1: UnivariatePolynomial<<Bls12_381 as Pairing>::ScalarField> = UnivariatePolynomial::rand(degree, &mut rng);
            let poly2: UnivariatePolynomial<<Bls12_381 as Pairing>::ScalarField> = UnivariatePolynomial::rand(degree, &mut rng);
            let poly = &poly1 * &poly2;
            polynomials.push(poly);
        }
        println!("Prover individually time: {:?}", time.elapsed());
        let mut target_poly = vec![UnivariatePolynomial::from_coefficients_vec(vec![<Bls12_381 as Pairing>::ScalarField::zero()]); times * Net::n_parties()];
        for i in 0..polynomials.len() {
            target_poly[i] += &polynomials[i];
        }
    }
}

// fn main() {
//     let (m, l, sub_prover_id) = init();
//     let x_degree = (1usize << m) - 1;
//     assert!(l.is_power_of_two());
//     let y_degree = l - 1;
//     let polynomial_number: usize = 10;
    
//     let mut rng = StdRng::seed_from_u64(0u64);
//     let domain = <GeneralEvaluationDomain<<Bls12_381 as Pairing>::ScalarField> as EvaluationDomain<<Bls12_381 as Pairing>::ScalarField>>::new(l).unwrap();

//     let setup_start = Instant::now();
//     let srs = BivBatchKZG::<Bls12_381>::setup_lagrange(&mut rng, x_degree, y_degree, &domain).unwrap();
//     println!("Prover {:?} setup time: {:?}", sub_prover_id, setup_start.elapsed());

//     let time = Instant::now();
//     let polys_x_polynomials = if Net::am_master() {
//         let mut polys_x_polynomials = Vec::new();
//         for _ in 0..polynomial_number {
//             let mut x_polynomials = Vec::new();
//             for _ in 0..y_degree + 1 {
//                 let mut x_polynomial_coeffs = vec![];
//                 for _ in 0..x_degree + 1 {
//                     x_polynomial_coeffs.push(<Bls12_381 as Pairing>::ScalarField::rand(&mut rng));
//                 }
//                 x_polynomials.push(UnivariatePolynomial::from_coefficients_slice(
//                     &x_polynomial_coeffs,
//                 ));
//             }
//             polys_x_polynomials.push(x_polynomials);
//         }
//         Net::recv_from_master(Some(vec![polys_x_polynomials.clone(); Net::n_parties()]));
//         polys_x_polynomials
//     } else {
//         Net::recv_from_master(None)
//     };
//     let sub_polynomials = polys_x_polynomials.iter().map(|x_polynomials| x_polynomials[sub_prover_id].clone()).collect();

//     let (y_point, x_points) = if Net::am_master() {
//         let y_point = <Bls12_381 as Pairing>::ScalarField::rand(&mut rng);

//         let mut x_points = Vec::new();
//         for i in 0..polynomial_number {
//             if i%2 == 1 {
//                 // x_points.push(vec![UniformRand::rand(&mut rng)]);
//                 x_points.push(vec![<Bls12_381 as Pairing>::ScalarField::rand(&mut rng), <Bls12_381 as Pairing>::ScalarField::rand(&mut rng)]);
//             }
//             else {
//                 x_points.push(vec![<Bls12_381 as Pairing>::ScalarField::rand(&mut rng), <Bls12_381 as Pairing>::ScalarField::rand(&mut rng), <Bls12_381 as Pairing>::ScalarField::rand(&mut rng)]);
//             }
//         }

//         Net::recv_from_master(Some(vec![(y_point.clone(), x_points.clone()); Net::n_parties()]));
//         (y_point, x_points)
//     } else {
//         Net::recv_from_master(None)
//     };
//     println!("Prover {:?} generates random polynomials and evaluation time: {:?}", sub_prover_id, time.elapsed());

//     // let time = Instant::now();
//     let coms = BivBatchKZG::<Bls12_381>::de_commit(sub_prover_id, &srs.0, &sub_polynomials);
//     // println!("Prover {:?} committing time: {:?}", sub_prover_id, time.elapsed());

//     // de-open
//     let time = Instant::now();
//     let mut prover_transcript : Transcript = Transcript::new(b"batch bivariate KZG at the same y");
//     let gamma = <Transcript as ProofTranscript<Bls12_381>>::challenge_scalar(
//         &mut prover_transcript, b"combined_polynomial_x_beta");
//     let proof = BivBatchKZG::<Bls12_381>::de_open_lagrange_at_same_y(sub_prover_id, &srs.0, &sub_polynomials, &x_points, &y_point, &domain, &mut prover_transcript, &gamma);
//     println!("Prover {:?} open time: {:?}", sub_prover_id, time.elapsed());

//     // de-eval
//     let time = Instant::now();
//     let mut evals: Vec<Vec<<Bls12_381 as Pairing>::ScalarField>> = Vec::new();
//     for i in 0..polynomial_number {
//         let mut eval_i = Vec::new();
//         for j in 0..x_points[i].len() {
//             let point = x_points[i][j];
//             let eval = sub_polynomials[i].evaluate(&point);
//             eval_i.push(eval);
//         }
//         evals.push(eval_i);
//     }
//     let evals_slice = Net::send_to_master(&evals);
//     let evals = if Net::am_master() {
//         let mut evals: Vec<Vec<<Bls12_381 as Pairing>::ScalarField>> = Vec::new();
//         let evals_vec = evals_slice.unwrap();
//         let evals_lagrange = EvaluationDomain::evaluate_all_lagrange_coefficients(&domain, y_point);
//         for i in 0..polynomial_number {
//             let mut eval_i = Vec::new();
//             for j in 0..x_points[i].len() {
//                 let eval = evals_vec.iter().zip(evals_lagrange.iter()).map(|(eval_slice, eval_lagrange)| eval_slice[i][j] * eval_lagrange).sum();
//                 eval_i.push(eval);
//             }
//             evals.push(eval_i);
//         }
//         evals
//     } else {
//         Vec::new()
//     };
//     println!("Prover {:?} evaluate time: {:?}", sub_prover_id, time.elapsed());

//     // verify
//     if Net::am_master() {
//         let time = Instant::now();
//         for _ in 0..50 {
//             let mut verifier_transcript : Transcript = Transcript::new(b"batch bivariate KZG at the same y");
//             let gamma = <Transcript as ProofTranscript<Bls12_381>>::challenge_scalar(
//                 &mut verifier_transcript, b"combined_polynomial_x_beta");
//             let is_valid = BivBatchKZG::<Bls12_381>::verify_at_same_y(&srs.1, &coms.clone().unwrap(), &x_points, &y_point, &evals, &proof.clone().unwrap(), &mut verifier_transcript, &gamma).unwrap();
//             assert!(is_valid);
//         }
//         println!("Verifier time: {:?}", time.elapsed()/50);
//     }


//     if Net::am_master() {
//         let mut bivariate_polynomials = Vec::new();
//         for i in 0..polynomial_number {
//             bivariate_polynomials.push(BivariatePolynomial{x_polynomials: polys_x_polynomials[i].clone()});
//         }

//         let time = Instant::now();
//         let com_test = BivBatchKZG::<Bls12_381>::commit(&srs.0, &bivariate_polynomials).unwrap();
//         println!("Prover commit individually time: {:?}", time.elapsed());
//         assert_eq!(coms.unwrap(), com_test);

//         let time = Instant::now();
//         let mut prover_transcript : Transcript = Transcript::new(b"batch bivariate KZG at the same y");
//         let gamma = <Transcript as ProofTranscript<Bls12_381>>::challenge_scalar(
//             &mut prover_transcript, b"combined_polynomial_x_beta");
//         let proof_test = BivBatchKZG::<Bls12_381>::open_lagrange_at_same_y(&srs.0, &bivariate_polynomials, &x_points, &y_point, &domain, &mut prover_transcript, &gamma).unwrap();
//         println!("Prover open individually time: {:?}", time.elapsed());
//         assert_eq!(proof.unwrap(), proof_test);

//         let time = Instant::now();
//         let mut evals_test: Vec<Vec<<Bls12_381 as Pairing>::ScalarField>> = Vec::new();
//         for i in 0..polynomial_number {
//             let mut eval_i = Vec::new();
//             for j in 0..x_points[i].len() {
//                 let point = (x_points[i][j], y_point);
//                 let eval = bivariate_polynomials[i].evaluate_lagrange(&point, &domain);
//                 eval_i.push(eval);
//             }
//             evals_test.push(eval_i);
//         }
//         println!("Prover evaluate individually time: {:?}", time.elapsed());
//         assert_eq!(evals, evals_test);

//         // Verify proof
//         let time = Instant::now();
//         for _ in 0..50{
//             let mut verifier_transcript : Transcript = Transcript::new(b"batch bivariate KZG at the same y");
//             let gamma = <Transcript as ProofTranscript<Bls12_381>>::challenge_scalar(
//                 &mut verifier_transcript, b"combined_polynomial_x_beta");
//             assert!(
//                 BivBatchKZG::<Bls12_381>::verify_at_same_y(&srs.1, &com_test, &x_points, &y_point, &evals_test, &proof_test, &mut verifier_transcript, &gamma).unwrap()
//             );
//         }
//         println!("Verifier individually time: {:?}", time.elapsed()/50);
//     }
// }
