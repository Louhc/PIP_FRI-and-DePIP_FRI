use ark_poly::{
    univariate::DensePolynomial as UnivariatePolynomial, DenseUVPolynomial, EvaluationDomain, Evaluations, GeneralEvaluationDomain, Polynomial
};
use std::marker::PhantomData;
use ark_ec::pairing::Pairing;
use my_kzg::{batch_kzg::BatchKZG, biv_batch_kzg::BivBatchKZG, helper::{get_x_srs, linear_combination_field}, transcript::ProofTranscript, trivial_kzg::{
    // DeKZG, 
    VerifierSRS,
    KZG
}};
use merlin::Transcript;
use my_ipa::{ipa::IPA, helper::{R1CSPublicPolys, R1CSWitnessPolys, generate_distributed_r1cs_polynomial_relation}, de_ipa::DeIPA};
use de_network::{DeMultiNet as Net, DeNet, DeSerNet};
use std::path::PathBuf;
use structopt::StructOpt;
use ark_std::rand::{rngs::StdRng, SeedableRng};
use ark_bls12_381::Bls12_381;
use ark_ff::{Field, One, Zero, UniformRand};
type MyField = <Bls12_381 as Pairing>::ScalarField;


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
    let m = (1 << 4);
    (m, l, sub_prover_id)
}

fn main() {
    let (m, l, sub_prover_id) = init();
    let mut rng = StdRng::seed_from_u64(0u64);

    let challenge_r = MyField::rand(&mut rng);
    let challenge_u1 = MyField::rand(&mut rng);
    let challenge_v = MyField::rand(&mut rng);
    let domain_x = <GeneralEvaluationDomain<MyField> as EvaluationDomain<MyField>>::new(m).unwrap();
    let domain_y = <GeneralEvaluationDomain<MyField> as EvaluationDomain<MyField>>::new(l).unwrap();
    let mut transcript : Transcript = Transcript::new(b"R1CS inner product");

    let x_degree = m - 1;
    let y_degree = l - 1;
    let srs = BivBatchKZG::<Bls12_381>::setup_lagrange(&mut rng, x_degree, y_degree, &domain_y).unwrap();
    let powers = &srs.0;
    let x_srs = get_x_srs::<Bls12_381>(&powers);

    let (r1cs_vecs, pub_polys, wit_polys) = generate_distributed_r1cs_polynomial_relation::<Bls12_381>(sub_prover_id, m, l, &challenge_r);

    let proof = DeIPA::<Bls12_381>::de_r1cs_prove(sub_prover_id, &powers, &x_srs, &wit_polys, &pub_polys, &challenge_r, &domain_x, &domain_y, &mut transcript, &challenge_v, &challenge_u1);
}
