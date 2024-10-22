use ark_std::rand::{rngs::StdRng, SeedableRng};
use ark_ff::{Field, One, Zero, UniformRand};
use ark_bls12_381::{Bls12_381, Fr};
use ark_relations::{
    lc,
    r1cs::{ConstraintSynthesizer, ConstraintSystemRef, ConstraintSystem, SynthesisError},
};
use ark_ec::pairing::Pairing;
use std::time::Instant;

use my_ipa::r1cs::R1CSVectors;

#[derive(Clone)]
struct RandomCircuit<F: Field> {
    pub a: Option<F>,
    pub b: Option<F>,
    pub num_variables: usize,
    pub num_constraints: usize,
}

impl<F: Field> ConstraintSynthesizer<F> for RandomCircuit<F> {
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {
        let n = self.num_variables / 3;
        for i in 0..n {
            let a = cs.new_witness_variable(|| self.a.ok_or(SynthesisError::AssignmentMissing))?;
            let b = cs.new_witness_variable(|| self.b.ok_or(SynthesisError::AssignmentMissing))?;
            let c = cs.new_input_variable(|| {
                let a = self.a.ok_or(SynthesisError::AssignmentMissing)?;
                let b = self.b.ok_or(SynthesisError::AssignmentMissing)?;
    
                Ok(a * b)
            })?;
            cs.enforce_constraint(lc!() + a, lc!() + b, lc!() + c)?;
            if i == n - 1 {
                for _ in 0..(self.num_variables - n * 3 - 1) {
                    let _ = cs.new_witness_variable(|| self.a.ok_or(SynthesisError::AssignmentMissing))?;
                }

                for _ in 0..(self.num_constraints - n) {
                    cs.enforce_constraint(lc!() + a, lc!() + b, lc!() + c)?;
                }
            }
        }
    
        Ok(())
    }
}


const NUM_CONSTRAINTS: usize = 1 << 10;
const NUM_VARIABLES: usize = 1 << 10;

#[test]
fn random_r1cs_satisfication_test() {
    let l = 8;
    
    let mut rng = StdRng::seed_from_u64(0u64);
    let challenge_r = Fr::rand(&mut rng);

    println!("Number of Machines: {}", l);

    // Generate the circuit

    let c = RandomCircuit::<Fr> {
        a: Some(Fr::rand(&mut rng)),
        b: Some(Fr::rand(&mut rng)),
        num_variables: NUM_VARIABLES,
        num_constraints: NUM_CONSTRAINTS,
    };
    let cs = ConstraintSystem::<Fr>::new_ref();
    c.generate_constraints(cs.clone()).unwrap();
    assert!(cs.is_satisfied().unwrap());

    println!("Number of constraints: {:?}", NUM_CONSTRAINTS);
    println!("Number of variables: {:?}", NUM_VARIABLES);

    let m = cs.num_constraints() / l;

    let mut vec_r = Vec::new();
    let mut r_pow = Fr::one();
    for _ in 0..m * l {
        vec_r.push(r_pow.clone());
        r_pow *= challenge_r;
    }

    let r1cs_vecs_all:Vec<R1CSVectors<Bls12_381>> = (0..l).map(|sub_prover_id| {
        R1CSVectors::<Bls12_381>::build(sub_prover_id, m, l, challenge_r, &cs).unwrap()
    }).collect();

    let mut ip_x_w = Fr::zero();
    let mut ip_y_w = Fr::zero();
    let mut ip_z_w = Fr::zero();

    let mut ip_r_a = Fr::zero();
    let mut ip_r_b = Fr::zero();
    let mut ip_r_c = Fr::zero();

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