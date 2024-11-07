use ark_ec::pairing::Pairing;
use ark_std::rand::{rngs::StdRng, SeedableRng};
use ark_ff::{One, Zero, UniformRand};
use ark_bls12_381::{Bls12_381, Fr};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem};
use my_ipa::r1cs::R1CSVectors;
use ark_rollup::{de_rollup::build_multi_tx_circuit, ConstraintF};

const NUM_TX: usize = 1 << 2;
const L: usize = 1 << 2;


#[test]
fn de_rollup_r1cs_satisfication_test() {
    let l = L;
    
    let mut rng = StdRng::seed_from_u64(0u64);
    let challenge_r = <Bls12_381 as Pairing>::ScalarField::rand(&mut rng);

    println!("Number of Machines: {}", l);

    // Generate the circuit

    let cs = ConstraintSystem::<ConstraintF>::new_ref();
    let _circuit = build_multi_tx_circuit::<NUM_TX, L>().generate_constraints(cs.clone()).unwrap();
    assert!(cs.is_satisfied().unwrap());

    println!("Number of constraints: {:?}", cs.num_constraints());
    println!("Number of variables: {:?}", cs.num_witness_variables() + cs.num_instance_variables());

    let m = cs.num_constraints() / l;

    let mut vec_r = Vec::new();
    let mut r_pow = <Bls12_381 as Pairing>::ScalarField::one();
    for _ in 0..m * l {
        vec_r.push(r_pow.clone());
        r_pow *= challenge_r;
    }

    let r1cs_vecs_all: Vec<R1CSVectors<Bls12_381>> = (0..l).map(|sub_prover_id| {
        R1CSVectors::<Bls12_381>::build(sub_prover_id, m, l, challenge_r, &cs).unwrap()
    }).collect();

    let mut ip_x_w = <Bls12_381 as Pairing>::ScalarField::zero();
    let mut ip_y_w = <Bls12_381 as Pairing>::ScalarField::zero();
    let mut ip_z_w = <Bls12_381 as Pairing>::ScalarField::zero();

    let mut ip_r_a = <Bls12_381 as Pairing>::ScalarField::zero();
    let mut ip_r_b = <Bls12_381 as Pairing>::ScalarField::zero();
    let mut ip_r_c = <Bls12_381 as Pairing>::ScalarField::zero();

    for i in 0..l {
        for j in 0..m {
            assert_eq!(r1cs_vecs_all[i].vec_a[j] * r1cs_vecs_all[i].vec_b[j], r1cs_vecs_all[i].vec_c[j]);
        }
    }

    for i in 0..l {

        ip_x_w += r1cs_vecs_all[i].vec_x.iter().zip(r1cs_vecs_all[i].vec_w.iter()).map(|(l, r)| *l * *r).sum::<Fr>();
        ip_y_w += r1cs_vecs_all[i].vec_y.iter().zip(r1cs_vecs_all[i].vec_w.iter()).map(|(l, r)| *l * *r).sum::<Fr>();
        ip_z_w += r1cs_vecs_all[i].vec_z.iter().zip(r1cs_vecs_all[i].vec_w.iter()).map(|(l, r)| *l * *r).sum::<Fr>();

        ip_r_a += r1cs_vecs_all[i].vec_a.iter().zip(vec_r[i * m..(i + 1) * m].iter()).map(|(l, r)| *l * *r).sum::<Fr>();
        ip_r_b += r1cs_vecs_all[i].vec_b.iter().zip(vec_r[i * m..(i + 1) * m].iter()).map(|(l, r)| *l * *r).sum::<Fr>();
        ip_r_c += r1cs_vecs_all[i].vec_c.iter().zip(vec_r[i * m..(i + 1) * m].iter()).map(|(l, r)| *l * *r).sum::<Fr>();
    }

    assert_eq!(ip_x_w, ip_r_a);
    assert_eq!(ip_y_w, ip_r_b);
    assert_eq!(ip_z_w, ip_r_c);   
}