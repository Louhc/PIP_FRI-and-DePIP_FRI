use ark_ec::{
    pairing::Pairing,
    scalar_mul::variable_base::VariableBaseMSM,
    CurveGroup, Group,
    scalar_mul::fixed_base::FixedBase,
};
use ark_ff::{One, UniformRand, Zero, PrimeField, Field};
use ark_poly::polynomial::{
    univariate::DensePolynomial as UnivariatePolynomial, DenseUVPolynomial, Polynomial,
};
use crate::trivial_kzg::UniVerifierSRS;
use crate::trivial_kzg::KZG;
use std::marker::PhantomData;
use ark_std::rand::Rng;
use crate::Error;
use de_network::{DeMultiNet as Net, DeNet, DeSerNet};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_poly::{Evaluations, GeneralEvaluationDomain};
use rayon::prelude::*;

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
    ) -> Result<(Vec<P::G1Affine>, UniVerifierSRS<P>), Error> {
        let alpha = <P::ScalarField>::rand(rng);
        let g = <P::G1>::generator();
        let h = <P::G2>::generator();
        let g_alpha_powers = structured_generators_scalar_power(degree + 1, &g, &alpha);
        Ok((
            <P as Pairing>::G1::normalize_batch(&g_alpha_powers),
            UniVerifierSRS {
                g: g.clone(),
                h: h.clone(),
                h_alpha: h * alpha,
            },
        ))
    }

    // use par_iter for speed up
    pub fn commit(
        powers: &[P::G1Affine],
        polynomials: &Vec<UnivariatePolynomial<P::ScalarField>>,
    ) -> Result<Vec<P::G1>, Error> {

        assert!(powers.len() >= polynomials[0].degree() + 1);

        Ok(polynomials.par_iter().map(|polynomial| {
            let mut coeffs = polynomial.coeffs.to_vec();
            coeffs.resize(powers.len(), <P::ScalarField>::zero());
            P::G1::msm(powers, &coeffs).unwrap()
        })
        .collect())

    }

    pub fn commit_lagrange(
        powers: &[P::G1Affine],
        evals_vec: &Vec<Evaluations<P::ScalarField>>,
    ) -> Result<Vec<P::G1>, Error> {
        assert!(powers.len() == evals_vec[0].evals.len());

        Ok(evals_vec.par_iter().map(|evals| {
            let mut evals = evals.evals.clone();
            evals.resize(powers.len(), <P::ScalarField>::zero());
            P::G1::msm(powers, &evals).unwrap()
        })
        .collect())
    }

    pub fn open_lagrange(
        powers: &[P::G1Affine],
        evals_vec: &Vec<Evaluations<P::ScalarField>>,
        point: &P::ScalarField,
        domain: &GeneralEvaluationDomain<P::ScalarField>,
        challenge: &P::ScalarField,
    ) -> Result<P::G1, Error> {

        let mut linear_factors = vec![P::ScalarField::one(); evals_vec.len()];
        linear_factors.par_iter_mut().enumerate().for_each(|(i, val)| {
            *val = challenge.pow([i as u64]);
        });

        let mut result_eval = vec![P::ScalarField::zero(); evals_vec[0].evals.len()];
        for (vector, &coeff) in evals_vec.iter().zip(&linear_factors) {
            for (i, &value) in vector.evals.iter().enumerate() {
                result_eval[i] += coeff * value;
            }
        }
        let result_eval = Evaluations::<P::ScalarField, GeneralEvaluationDomain<P::ScalarField>>::from_vec_and_domain(result_eval, *domain);

        let quotient_evals = KZG::<P>::get_quotient_eval_lagrange(&result_eval, &point, &domain);

        // Can unwrap because quotient_coeffs.len() is guaranteed to be equal to powers.len()
        Ok(P::G1::msm(powers, &quotient_evals).unwrap())
    }

    pub fn open(
        powers: &[P::G1Affine],
        polynomials: &Vec<UnivariatePolynomial<P::ScalarField>>,
        point: &P::ScalarField,
        challenge: &P::ScalarField,
    ) -> Result<P::G1, Error> {
        let mut linear_factors = vec![P::ScalarField::one(); polynomials.len()];
        linear_factors.par_iter_mut().enumerate().for_each(|(i, val)| {
            *val = challenge.pow([i as u64]);
        });
        let combined_polynomial = polynomials.par_iter().zip(linear_factors.par_iter()).map(|(poly, factor)| poly * *factor).reduce(
            || UnivariatePolynomial::zero(),
            |acc, poly| acc + poly,
        );

        // Trick to calculate (p(x) - p(z)) / (x - z) as p(x) / (x - z) ignoring remainder p(z)
        let quotient_polynomial = &combined_polynomial
            / &UnivariatePolynomial::from_coefficients_vec(vec![
                -point.clone(),
                P::ScalarField::one(),
            ]);
        let mut quotient_coeffs = quotient_polynomial.coeffs.to_vec();
        quotient_coeffs.resize(powers.len(), <P::ScalarField>::zero());

        Ok(P::G1::msm(powers, &quotient_coeffs).unwrap())
    }

    pub fn verify(
        v_srs: &UniVerifierSRS<P>,
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

        let is_valid = P::pairing(linear_combination.clone(), v_srs.h.clone())
            == P::pairing(proof.clone(), v_srs.h_alpha.clone() - v_srs.h * point);
        Ok(is_valid)
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
    use crate::biv_batch_kzg::BivBatchKZG;
    use crate::trivial_kzg::{UniVerifierSRS, KZG};
    use ark_poly::polynomial::{
        univariate::DensePolynomial as UnivariatePolynomial, DenseUVPolynomial, Polynomial,
    };
    use ark_poly::{GeneralEvaluationDomain, EvaluationDomain};
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
        println!("BatchKZG setup time, {:} log_degree: {:?} ", degree, setup_start.elapsed());

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


    #[test]
    fn batch_kzg_lagrange_test() {

        let log_degree = 10;
        let poly_num = 10;
        let degree = (1 << log_degree) - 1;
        let mut rng = StdRng::seed_from_u64(0u64);
        let domain = <GeneralEvaluationDomain<<Bls12_381 as Pairing>::ScalarField> as EvaluationDomain<<Bls12_381 as Pairing>::ScalarField>>::new(1 << log_degree).unwrap();

        let setup_start = Instant::now();
        // let (g_alpha_powers, v_srs) = KZG::<Bls12_381>::setup_lagrange(&mut rng, degree, &domain).unwrap();
        let (g_alpha_powers, v_srs) = BivBatchKZG::<Bls12_381>::setup_lagrange(&mut rng, 3, degree, &domain).unwrap();
        let v_srs = UniVerifierSRS {
            g: v_srs.g,
            h: v_srs.h,
            h_alpha: v_srs.h_beta
        };
        let g_alpha_powers: Vec<<Bls12_381 as Pairing>::G1Affine> = g_alpha_powers.iter()
            .filter_map(|row| row.get(0))
            .cloned()
            .collect();

        let time = setup_start.elapsed().as_millis();
        println!("BatchKZG lagrange setup time, {:} log_degree: {:} ", degree, time);

        let mut polynomials = Vec::new();
        let mut evals = Vec::new();
        let mut evals_domain = Vec::new();
        let point = <Bls12_381 as Pairing>::ScalarField::rand(&mut rng);

        for _ in 0..poly_num {
            let polynomial = UnivariatePolynomial::rand(degree, &mut rng);
            let eval = polynomial.evaluate(&point);
            let eval_domain = polynomial.clone().evaluate_over_domain(domain.clone());
            polynomials.push(polynomial);
            evals.push(eval);
            evals_domain.push(eval_domain);
        }

        // Commit
        let com_start = Instant::now();
        let mut coms = Vec::new();
        for eval_domain in &evals_domain {
            let com = KZG::<Bls12_381>::commit_lagrange(&g_alpha_powers, eval_domain).unwrap();
            coms.push(com);
        }
        let mut prover_transcript : Transcript = Transcript::new(b"batch univariate KZG");
        
        println!("KZG commi time, {:} log_degree: {:?} ms", log_degree, com_start.elapsed().as_millis());
        println!("KZG commi size, {:} log_degree: {:?} bytes", log_degree, size_of_val(&coms[0])*coms.len());

        // TODO: append_point input inconsistency
        // Open
        let open_start = Instant::now();
        // prover_transcript.append_point(b"add_commitments", &coms[0]);
        let challenge = <Transcript as ProofTranscript<Bls12_381>>::challenge_scalar(
            &mut prover_transcript, b"batch_kzg_rlc_challenge");
        let proofs = BatchKZG::<Bls12_381>::open_lagrange(&g_alpha_powers, &evals_domain, &point, &domain, &challenge).unwrap();
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