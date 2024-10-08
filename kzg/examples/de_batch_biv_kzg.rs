use ark_bls12_381::Bls12_381;
use ark_ec::pairing::Pairing;
use ark_ff::Zero;
use my_kzg::{biv_trivial_kzg::BivariatePolynomial, biv_batch_kzg::BivBatchKZG};
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
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain};

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

    println!("log_degree: {:?}", m);

    (m, l, sub_prover_id)
}

fn main() {
    let (m, l, sub_prover_id) = init();
    let x_degree = (1usize << m) - 1;
    assert!(l.is_power_of_two());
    let y_degree = l - 1;
    let polynomial_number: usize = 1;
    
    let mut rng = StdRng::seed_from_u64(0u64);
    let domain = <GeneralEvaluationDomain<<Bls12_381 as Pairing>::ScalarField> as EvaluationDomain<<Bls12_381 as Pairing>::ScalarField>>::new(l).unwrap();

    let setup_start = Instant::now();
    let srs = BivBatchKZG::<Bls12_381>::setup_lagrange(&mut rng, x_degree, y_degree, &domain).unwrap();
    println!("Prover {:?} setup time: {:?}", sub_prover_id, setup_start.elapsed());

    let time = Instant::now();
    let polys_x_polynomials = if Net::am_master() {
        let mut polys_x_polynomials = Vec::new();
        for _ in 0..polynomial_number {
            let mut x_polynomials = Vec::new();
            for _ in 0..y_degree + 1 {
                let mut x_polynomial_coeffs = vec![];
                for _ in 0..x_degree + 1 {
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

    // let mut bivariate_polynomials = Vec::new();
    // for _ in 0..polynomial_number {
    //     let mut x_polynomials = Vec::new();
    //     for _ in 0..y_degree + 1 {
    //         let mut x_polynomial_coeffs = vec![];
    //         for _ in 0..x_degree + 1 {
    //             x_polynomial_coeffs.push(<Bls12_381 as Pairing>::ScalarField::rand(&mut rng));
    //         }
    //         x_polynomials.push(UnivariatePolynomial::from_coefficients_slice(
    //             &x_polynomial_coeffs,
    //         ));
    //     }
    //     bivariate_polynomials.push (BivariatePolynomial { x_polynomials });
    // }
    let (y_point, x_points) = if Net::am_master() {
        let y_point = <Bls12_381 as Pairing>::ScalarField::rand(&mut rng);

        let mut x_points = Vec::new();
        for i in 0..polynomial_number {
            if i%2 == 1 {
                // x_points.push(vec![UniformRand::rand(&mut rng)]);
                x_points.push(vec![<Bls12_381 as Pairing>::ScalarField::rand(&mut rng), <Bls12_381 as Pairing>::ScalarField::rand(&mut rng)]);
            }
            else {
                x_points.push(vec![<Bls12_381 as Pairing>::ScalarField::rand(&mut rng), <Bls12_381 as Pairing>::ScalarField::rand(&mut rng), <Bls12_381 as Pairing>::ScalarField::rand(&mut rng)]);
            }
        }

        Net::recv_from_master(Some(vec![(y_point.clone(), x_points.clone()); Net::n_parties()]));
        (y_point, x_points)
    } else {
        Net::recv_from_master(None)
    };
    println!("Prover {:?} generates random polynomials and evaluation time: {:?}", sub_prover_id, time.elapsed());

    // let time = Instant::now();
    let com = BivBatchKZG::<Bls12_381>::de_commit(sub_prover_id, &srs.0, &polys_x_polynomials);
    // println!("Prover {:?} committing time: {:?}", sub_prover_id, time.elapsed());

    let mut bivariate_polynomials = Vec::new();
    for i in 0..polynomial_number {
        bivariate_polynomials.push(BivariatePolynomial{x_polynomials: polys_x_polynomials[i].clone()});
    }

    if Net::am_master() {
        let time = Instant::now();
        let com_test = BivBatchKZG::<Bls12_381>::commit(&srs.0, &bivariate_polynomials).unwrap();
        println!("Prover commit individually time: {:?}", time.elapsed());
        assert_eq!(com.unwrap(), com_test);
    }
}
