pub mod prover;
pub mod verifier;

#[cfg(test)]
mod tests {
    use std::mem::size_of;

    use crate::{prover::One2ManyProver, verifier::One2ManyVerifier};
    use ark_poly::GeneralEvaluationDomain;
    use utils::helper::MultilinearPolynomial;
    use utils::merkle_tree::MERKLE_ROOT_SIZE;
    use utils::fiat_shamir::RandomOracle;
    use utils::{CODE_RATE, SECURITY_BITS};
    use utils::goldilocks::Goldilocks as T;


    fn output_proof_size(variable_num: usize, terminate_round: usize) -> usize {
        let polynomial = MultilinearPolynomial::random_polynomial(variable_num);
        let mut interpolate_cosets = vec![GeneralEvaluationDomain::new(
            1 << (variable_num + CODE_RATE),
            T::random_element(),
        )];
        for i in 1..variable_num {
            interpolate_cosets.push(interpolate_cosets[i - 1].pow(2));
        }
        let oracle = RandomOracle::new(variable_num, SECURITY_BITS / CODE_RATE);
        let mut prover = One2ManyProver::new(
            variable_num - terminate_round,
            &interpolate_cosets,
            polynomial,
            &oracle,
        );
        let commit = prover.commit_polynomial();
        let mut verifier = One2ManyVerifier::new(
            variable_num - terminate_round,
            variable_num,
            &interpolate_cosets,
            commit,
            &oracle,
        );
        let open_point = verifier.get_open_point();

        prover.commit_functions(&open_point, &mut verifier);
        prover.prove();
        prover.commit_foldings(&mut verifier);
        let (folding_proof, function_proof) = prover.query();
        verifier.verify(&folding_proof, &function_proof);
        folding_proof.iter().map(|x| x.proof_size()).sum::<usize>()
            + function_proof.iter().map(|x| x.proof_size()).sum::<usize>()
            + (variable_num - terminate_round) * MERKLE_ROOT_SIZE * 2
            + ((1 << terminate_round) + 1) * size_of::<T>() * 2
    }

    #[test]
    fn test_proof_size() {
        for i in 5..=25 {
            let proof_size = output_proof_size(i, 1);
            println!(
                "PolyFRIM pcs proof size of {} variables is {} bytes",
                i, proof_size
            );
        }
    }
}
