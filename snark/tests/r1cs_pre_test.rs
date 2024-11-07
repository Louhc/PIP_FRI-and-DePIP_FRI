use ark_ec::pairing::Pairing;
use ark_bls12_381::Bls12_381;
use ark_relations::{
    lc,
    r1cs::{ConstraintSynthesizer, SynthesisError, ConstraintSystem, ConstraintSystemRef, Variable},
};
use my_snark::indexer::Indexer;
use std::marker::PhantomData;

#[derive(Clone)]
pub struct TestCircuit<P: Pairing> {
    _pairing: PhantomData<P>,
}

impl<P: Pairing> TestCircuit<P> {
    pub fn new(
    ) -> Self {
        Self {
            _pairing: PhantomData,
        }
    }
}

// impl<P: Pairing> ConstraintSynthesizer<P::ScalarField> for TestCircuit<P> {
//     fn generate_constraints(self, cs: ConstraintSystemRef<P::ScalarField>) -> Result<(), SynthesisError> {
//         let f_a = Some(P::ScalarField::from(2u64));
//         let f_b = Some(P::ScalarField::from(3u64));
//         let a = cs.new_witness_variable(|| f_a.ok_or(SynthesisError::AssignmentMissing))?;
//         let b = cs.new_witness_variable(|| f_b.ok_or(SynthesisError::AssignmentMissing))?;
//         let c = cs.new_witness_variable(|| {
//             let a = f_a.ok_or(SynthesisError::AssignmentMissing)?;
//             let b = f_b.ok_or(SynthesisError::AssignmentMissing)?;
    
//             Ok(a * b)
//         })?;
//         cs.enforce_constraint(lc!() + a, lc!() + b, lc!() + c)?;
//         cs.enforce_constraint(lc!() + b, lc!() + (P::ScalarField::from(2u64), Variable::One), lc!() + c)?;
//         cs.enforce_constraint(lc!() + (P::ScalarField::from(3u64), Variable::One), lc!() + a, lc!() + c)?;
//         cs.enforce_constraint(lc!() + (P::ScalarField::from(1u64),Variable::One), lc!() + b, lc!() + b)?;
    
//         Ok(())
//     }
// }

impl<P: Pairing> ConstraintSynthesizer<P::ScalarField> for TestCircuit<P> {
    fn generate_constraints(self, cs: ConstraintSystemRef<P::ScalarField>) -> Result<(), SynthesisError> {
        for i in 0..5 {
            let f_a = Some(P::ScalarField::from(2u64));
            let f_b = Some(P::ScalarField::from(3u64));
            let a = cs.new_witness_variable(|| f_a.ok_or(SynthesisError::AssignmentMissing))?;
            let b = cs.new_witness_variable(|| f_b.ok_or(SynthesisError::AssignmentMissing))?;
            let c = cs.new_witness_variable(|| {
                let a = f_a.ok_or(SynthesisError::AssignmentMissing)?;
                let b = f_b.ok_or(SynthesisError::AssignmentMissing)?;
        
                Ok(a * b)
            })?;
            cs.enforce_constraint(lc!() + a, lc!() + b, lc!() + c)?;  

            if i == 4 {
                for _ in 0..5 {
                    cs.enforce_constraint(lc!() + b, lc!() + (P::ScalarField::from(2u64), Variable::One), lc!() + c)?;
                    cs.enforce_constraint(lc!() + (P::ScalarField::from(3u64), Variable::One), lc!() + a, lc!() + c)?;
                }
                cs.enforce_constraint(lc!() + (P::ScalarField::from(1u64), Variable::One), lc!() + b, lc!() + b)?;    
            }
        }

        Ok(())
    }
}

#[test]
fn random_r1cs_preprocessing_test() {
    let l = 2;
    println!("Number of Machines: {}", l);

    // Generate the circuit
    let c = TestCircuit::<Bls12_381>::new();
    let cs = ConstraintSystem::<<Bls12_381 as Pairing>::ScalarField>::new_ref();
    c.generate_constraints(cs.clone()).unwrap();
    assert!(cs.is_satisfied().unwrap());

    let mut cs = cs.borrow_mut().unwrap();
    cs.finalize();
    let cs_matrix = cs.to_matrices().unwrap();

    let m = cs.num_constraints / l;
    println!("Number of constraints: {:?}", cs.num_constraints);

    let (de_row_index_vecs, de_col_index_vecs, de_val_evals_vecs, pow_of_two): (Vec<_>, Vec<_>, Vec<_>, usize) = Indexer::<Bls12_381>::build_de_r1cs_index(l, m, &cs_matrix).unwrap();
    
    let n_evals = Indexer::<Bls12_381>::build_n_evals(&de_row_index_vecs, &de_col_index_vecs, l, m, pow_of_two);

    println!("r1cs matrix: {:?}", cs_matrix);
    let vec_w = [&cs.instance_assignment[..], &cs.witness_assignment[..]].concat();
    println!("witness vector: {:?}", vec_w);
    
    println!("r1cs preprocessing row info: {:?}", de_row_index_vecs);
    println!("r1cs preprocessing col info: {:?}", de_col_index_vecs);
    println!("r1cs preprocessing val info: {:?}", de_val_evals_vecs);

    println!("r1cs preprocessing lookup info: {:?}", n_evals);

}