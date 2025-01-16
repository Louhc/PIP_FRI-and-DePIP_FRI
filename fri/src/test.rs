#[cfg(test)]
mod tests {
    use crate::prover::Prover;
    use crate::verifier::Verifier;
    use ark_ff::UniformRand;
    use ark_poly::DenseUVPolynomial;
    use ark_poly::EvaluationDomain;
    use utils::{
        goldilocks::Goldilocks as T, 
        CODE_RATE, SECURITY_BITS};
    // use ark_ff::PrimeField;
    use utils::{helper::Helper, merkle_tree::MERKLE_ROOT_SIZE};
    use ark_poly::polynomial::{
        univariate::DensePolynomial as UnivariatePolynomial, Polynomial,
    };
    use ark_std::rand::{rngs::StdRng, SeedableRng};
    use utils::fiat_shamir::RandomOracle;

    #[test]
    fn fri_pcs_test() {
        let variable_num: usize = 10;
        let degree: usize = (1 << variable_num) - 1;
        let mut rng = StdRng::seed_from_u64(0u64);
        let polynomial = UnivariatePolynomial::rand(degree, &mut rng);
        let point = T::rand(&mut rng);
        let eval = polynomial.evaluate(&point);

        let mut interpolate_cosets = vec![EvaluationDomain::new_coset(1 << (variable_num + CODE_RATE), T::from(1)).unwrap()];
        for i in 1..variable_num {
            interpolate_cosets.push(Helper::pow(&interpolate_cosets[i-1], 2));
        }

        // commit
        let oracle = RandomOracle::new(variable_num, SECURITY_BITS / CODE_RATE);
        let mut prover = Prover::new(variable_num, &interpolate_cosets, polynomial, &oracle);
        // 32 bytes = 256 bit
        let com = prover.commit_polynomial();

        // open
        let mut verifier = Verifier::new(variable_num, &interpolate_cosets, com, &oracle, point);
        let proof = prover.open(point, eval, &mut verifier);
        
        // verify
        assert!(verifier.verify(&proof, eval));

        // proof size
        let proof_size = proof
            .iter()
            .map(|x| x.proof_size())
            .sum::<usize>()
            + variable_num * MERKLE_ROOT_SIZE;
        println!("proof size is {:?} KB", proof_size / 1024);
    }
}