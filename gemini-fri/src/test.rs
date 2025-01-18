#[cfg(test)]
mod tests {
    use crate::prover::FriProver;
    use crate::verifier::FriVerifier;
    use ark_ff::UniformRand;
    use utils::helper::MultilinearPolynomial;
    use ark_poly::EvaluationDomain;
    use crate::Tuple;
    use utils::{
        goldilocks::Goldilocks as T, 
        CODE_RATE, SECURITY_BITS};
    // use ark_ff::PrimeField;
    use utils::{helper::Helper, merkle_tree::MERKLE_ROOT_SIZE};
    use ark_std::rand::{rngs::StdRng, SeedableRng};
    use utils::fiat_shamir::RandomOracle;

    #[test]
    fn hyperplonk_test() {
        let variable_num: usize = 10;
        let mut rng = StdRng::seed_from_u64(0u64);
        let polynomial = MultilinearPolynomial::rand(variable_num);
        let point = (0..variable_num)
            .map(|_| T::rand(&mut rng))
            .collect::<Vec<T>>();
        let eval = polynomial.evaluate(&point);

        let mut interpolate_cosets = vec![EvaluationDomain::new_coset(1 << (variable_num + CODE_RATE), T::from(1)).unwrap()];
        for i in 1..variable_num {
            interpolate_cosets.push(Helper::pow(&interpolate_cosets[i-1], 2));
        }

        // commit
        let oracle = RandomOracle::new(variable_num, SECURITY_BITS / CODE_RATE);
        let mut prover = FriProver::new(variable_num, &interpolate_cosets, polynomial.clone(), &oracle);
        // 32 bytes = 256 bit
        let commitment = prover.commit_first_polynomial();

        // open
        let mut verifier = FriVerifier::new(variable_num, &interpolate_cosets, commitment, &oracle, &point);
        // tuples is the pair of evaluations
        // folding_proofs are merkle trees opening from 2nd round
        // function_proofs are merkle trees opening of the log N polynomials
        let (tuples, folding_proofs, function_proofs) = prover.open(&mut verifier, &point);

        // verifier.set_tuples(&tuples);
        let is_valid = verifier.verify(&tuples, eval, &folding_proofs, &function_proofs);
        assert!(is_valid);

        // proof size
        let proof_size =  tuples.len() * size_of::<Tuple<T>>()
            + (2 * variable_num - 3) * MERKLE_ROOT_SIZE
            + 2 * size_of::<T>()
            + folding_proofs.iter().map(|x| x.proof_size()).sum::<usize>()
            + function_proofs
                .iter()
                .map(|x| x.proof_size())
                .sum::<usize>();
        println!("proof size is {:?} KB", proof_size / 1024);
    }
}