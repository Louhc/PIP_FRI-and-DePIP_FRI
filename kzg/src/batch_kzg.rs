use ark_ec::{
    pairing::Pairing,
    scalar_mul::variable_base::VariableBaseMSM,
    CurveGroup, Group,
    scalar_mul::fixed_base::FixedBase,
};
use ark_ff::{One, UniformRand, Zero, PrimeField};
use ark_poly::polynomial::{
    univariate::DensePolynomial as UnivariatePolynomial, DenseUVPolynomial, Polynomial,
};
use crate::trivial_kzg::VerifierSRS;
use std::marker::PhantomData;
use ark_std::rand::Rng;
use crate::Error;
use deNetwork::{DeMultiNet as Net, DeNet, DeSerNet};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};

#[derive(Clone)]
pub struct SRS<P: Pairing> {
    pub g_alpha_powers: Vec<P::G1>,
    pub h_beta_powers: Vec<P::G2>,
    pub h_alpha: P::G2,
}

// #[derive(Clone)]
// pub struct VerifierSRS<P: Pairing> {
//     pub g: P::G1,
//     pub h: P::G2,
//     pub h_alpha: P::G2,
// }

//TODO: Change SRS to return reference iterator - requires changes to TIPA and GIPA signatures
impl<P: Pairing> SRS<P> {

    pub fn get_verifier_key(&self) -> VerifierSRS<P> {
        VerifierSRS {
            g: self.g_alpha_powers[0].clone(),
            h: self.h_beta_powers[0].clone(),
            h_alpha: self.h_alpha.clone(),
        }
    }
}

pub fn structured_generators_scalar_power<G: CurveGroup>(
    num: usize,
    g: &G,
    s: &G::ScalarField,
) -> Vec<G> {
    assert!(num > 0);
    let mut powers_of_scalar = vec![];
    let mut pow_s = G::ScalarField::one();
    for _ in 0..num {
        powers_of_scalar.push(pow_s);
        pow_s *= s;
    }

    let window_size = FixedBase::get_mul_window_size(num);

    let scalar_bits = G::ScalarField::MODULUS_BIT_SIZE as usize;
    let g_table = FixedBase::get_window_table(scalar_bits, window_size, g.clone());
    let powers_of_g = FixedBase::msm::<G>(scalar_bits, window_size, &g_table, &powers_of_scalar);
    powers_of_g
}

pub struct BatchKZG<P: Pairing> {
    _pairing: PhantomData<P>,
}

// Simple implementation of univariate batch KZG polynomial commitment scheme evaluated at the same point
impl<P: Pairing> BatchKZG<P> {
    pub fn setup<R: Rng>(
        rng: &mut R,
        degree: usize,
    ) -> Result<(Vec<P::G1Affine>, VerifierSRS<P>), Error> {
        let alpha = <P::ScalarField>::rand(rng);
        let g = <P::G1>::generator();
        let h = <P::G2>::generator();
        let g_alpha_powers = structured_generators_scalar_power(degree + 1, &g, &alpha);
        Ok((
            <P as Pairing>::G1::normalize_batch(&g_alpha_powers),
            VerifierSRS {
                g: g.clone(),
                h: h.clone(),
                h_alpha: h * alpha,
            },
        ))
    }

    pub fn commit(
        powers: &[P::G1Affine],
        polynomials: &Vec<UnivariatePolynomial<P::ScalarField>>,
    ) -> Result<Vec<P::G1>, Error> {
        assert!(powers.len() >= polynomials[0].degree() + 1);

        let mut results = Vec::new();

        for polynomial in polynomials.iter() {
            let mut coeffs = polynomial.coeffs.to_vec();
            coeffs.resize(powers.len(), <P::ScalarField>::zero());
        
            // Can unwrap because coeffs.len() is guaranteed to be equal to powers.len()
            let result = P::G1::msm(powers, &coeffs).unwrap();
            results.push(result);
        }
        Ok(results)
    }

    pub fn open(
        powers: &[P::G1Affine],
        polynomials: &Vec<UnivariatePolynomial<P::ScalarField>>,
        point: &P::ScalarField,
        // the de Lagrange open has to use challenge as you can not communicate with transcript
        // we also use challenge here for consistency
        challenge: &P::ScalarField,
        // transcript: &mut Transcript,
    ) -> Result<P::G1, Error> {

        assert!(powers.len() >= polynomials[0].degree() + 1);
        let poly_num = polynomials.len();
        let mut linear_factor = P::ScalarField::one();

        // let challenge = <Transcript as ProofTranscript<P>>::challenge_scalar(
        //     transcript, b"batch_kzg_rlc_challenge");

        let mut combined_polynomial = UnivariatePolynomial::from_coefficients_vec(
             vec![P::ScalarField::zero(); poly_num]);
        for i in 0..polynomials.len() {
            combined_polynomial += (linear_factor, &polynomials[i]);
            linear_factor *= challenge;
        }

        // Trick to calculate (p(x) - p(z)) / (x - z) as p(x) / (x - z) ignoring remainder p(z)
        let quotient_polynomial = &combined_polynomial
            / &UnivariatePolynomial::from_coefficients_vec(vec![
                -point.clone(),
                P::ScalarField::one(),
            ]);
        let mut quotient_coeffs = quotient_polynomial.coeffs.to_vec();
        quotient_coeffs.resize(powers.len(), <P::ScalarField>::zero());

        // Can unwrap because quotient_coeffs.len() is guaranteed to be equal to powers.len()
        Ok(P::G1::msm(powers, &quotient_coeffs).unwrap())
    }

    pub fn verify(
        v_srs: &VerifierSRS<P>,
        coms: &Vec<P::G1>,
        point: &P::ScalarField,
        evals: &Vec<P::ScalarField>,
        proof: &P::G1,
        challenge: &P::ScalarField,
        // transcript: &mut Transcript
    ) -> Result<bool, Error> {
        assert!(coms.len() >= 1);
        assert!(coms.len() == evals.len());

        let mut linear_factor = P::ScalarField::one();
        let mut linear_combination = coms[0].clone() - v_srs.g * evals[0];
        for i in 1..coms.len() {
            linear_factor *= challenge;
            linear_combination = linear_combination + (coms[i].clone() - v_srs.g * evals[i]) * linear_factor;
        }

        Ok(P::pairing(linear_combination.clone(), v_srs.h.clone())
            == P::pairing(proof.clone(), v_srs.h_alpha.clone() - v_srs.h * point))
    }
}

#[derive(Default, Clone, CanonicalSerialize, CanonicalDeserialize, PartialEq, Eq, Debug)]
pub struct DeBatchKZG<P: Pairing> {
    _pairing: PhantomData<P>,
}

impl<P: Pairing> DeBatchKZG<P> {

    pub fn de_commit(
        powers: &[P::G1Affine],
        sub_polynomials: &Vec<UnivariatePolynomial<P::ScalarField>>
    ) -> Option<Vec<P::G1>> {
        let mut sub_coms = Vec::new();

        for sub_polynomial in sub_polynomials.iter() {
            assert!(powers.len() >= sub_polynomial.degree() + 1);
            let mut coeffs = sub_polynomial.coeffs.to_vec();
            coeffs.resize(powers.len(), <P::ScalarField>::zero());

            let sub_com = P::G1::msm(powers, &coeffs).unwrap();
            sub_coms.push(sub_com);
        }
        let final_coms_slice = Net::send_to_master(&sub_coms);

        // guaranteed by the Net if delayed
        // the output vec lengh equals to sub prover number
        if Net::am_master() {
            let mut final_coms = vec![P::G1::zero(); sub_polynomials.len()];
            let final_coms_slice = final_coms_slice.unwrap();
            for row in final_coms_slice {
                for i in 0..row.len() {
                    final_coms[i] += row[i];
                }
            }
            Some(final_coms)
        } else {
            None
        }
    }

    pub fn de_open(
        powers: &[P::G1Affine],
        sub_polynomials: &Vec<UnivariatePolynomial<P::ScalarField>>,
        point: &P::ScalarField,
        // transcript: &mut Transcript,
        challenge: &P::ScalarField,
    ) -> Option<P::G1> {

        assert!(powers.len() >= sub_polynomials[0].degree() + 1);
        let poly_num = sub_polynomials.len();
        let mut linear_factor = P::ScalarField::one();

        // let challenge = <Transcript as ProofTranscript<P>>::challenge_scalar(
        //     transcript, b"batch_kzg_rlc_challenge");

        let mut combined_polynomial = UnivariatePolynomial::from_coefficients_vec(
             vec![P::ScalarField::zero(); poly_num]);
        for i in 0..sub_polynomials.len() {
            combined_polynomial += (linear_factor, &sub_polynomials[i]);
            linear_factor *= challenge;
        }

        // Trick to calculate (p(x) - p(z)) / (x - z) as p(x) / (x - z) ignoring remainder p(z)
        let quotient_polynomial = &combined_polynomial
            / &UnivariatePolynomial::from_coefficients_vec(vec![
                -point.clone(),
                P::ScalarField::one(),
            ]);
        let mut quotient_coeffs = quotient_polynomial.coeffs.to_vec();
        quotient_coeffs.resize(powers.len(), <P::ScalarField>::zero());

        let sub_proof = P::G1::msm(powers, &quotient_coeffs).unwrap();
        let final_proof_slice = Net::send_to_master(&sub_proof);

        if Net::am_master() {
            Some(final_proof_slice.unwrap().iter().sum())
        } else {
            None
        }
    }

}


#[cfg(test)]
mod tests {
    use ark_bls12_381::Bls12_381;
    use ark_std::rand::{rngs::StdRng, SeedableRng};
    use ark_ff::UniformRand;
    use merlin::Transcript;
    use crate::batch_kzg::BatchKZG;
    use ark_poly::polynomial::{
        univariate::DensePolynomial as UnivariatePolynomial, DenseUVPolynomial, Polynomial,
    };
    use ark_ec::pairing::Pairing;
    use std::time::{Duration, Instant};
    use crate::transcript::ProofTranscript;

    #[test]
    fn batch_kzg_test() {

        let log_degree = 10;
        let poly_num = 10;
        let degree = (1 << log_degree) - 1;
        let mut rng = StdRng::seed_from_u64(0u64);

        let setup_start = Instant::now();
        let (g_alpha_powers, v_srs) = BatchKZG::<Bls12_381>::setup(&mut rng, degree).unwrap();
        let time = setup_start.elapsed().as_millis();
        println!("BatchKZG setup time, {:} log_degree: {:} ", degree, time);

        let mut polynomials = Vec::new();
        let mut evals = Vec::new();
        let point = <Bls12_381 as Pairing>::ScalarField::rand(&mut rng);

        for _ in 0..poly_num {
            let polynomial = UnivariatePolynomial::rand(degree, &mut rng);
            let eval = polynomial.evaluate(&point);
            polynomials.push(polynomial);
            evals.push(eval);
        }

        // Commit
        let com_start = Instant::now();
        let coms = BatchKZG::<Bls12_381>::commit(&g_alpha_powers, &polynomials).unwrap();
        let mut prover_transcript : Transcript = Transcript::new(b"batch univariate KZG");
        
        println!("KZG commi time, {:} log_degree: {:?} ms", log_degree, com_start.elapsed().as_millis());
        println!("KZG commi size, {:} log_degree: {:?} bytes", log_degree, size_of_val(&coms[0])*coms.len());

        // TODO: append_point input inconsistency
        // Open
        let open_start = Instant::now();
        // prover_transcript.append_point(b"add_commitments", &coms[0]);
        let challenge = <Transcript as ProofTranscript<Bls12_381>>::challenge_scalar(
            &mut prover_transcript, b"batch_kzg_rlc_challenge");
        let proofs = BatchKZG::<Bls12_381>::open(&g_alpha_powers, &polynomials, &point, &challenge).unwrap();
        println!("KZG open  time, {:} log_degree: {:?} ms", log_degree, open_start.elapsed().as_millis());

        // Proof size
        let proof_size = size_of_val(&proofs);
        println!("KZG proof size, {:} log_degree: {:?} bytes", log_degree, proof_size);

        // Verify
        std::thread::sleep(Duration::from_millis(5000));
        let verify_start = Instant::now();
        let mut verifier_transcript : Transcript = Transcript::new(b"batch univariate KZG");
        let challenge = <Transcript as ProofTranscript<Bls12_381>>::challenge_scalar(
            &mut verifier_transcript, b"batch_kzg_rlc_challenge");
        for _ in 0..50 {
            let is_valid =
                BatchKZG::<Bls12_381>::verify(&v_srs, &coms, &point, &evals, &proofs, &challenge).unwrap();
            assert!(is_valid);
        }
        let verify_time = verify_start.elapsed().as_millis() / 50;
        println!("KZG verif time, {:} log_degree: {:?} ms", log_degree, verify_time);
    }
}