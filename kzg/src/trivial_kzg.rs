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
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain};

use std::marker::PhantomData;

use ark_std::rand::Rng;
// use digest::Digest;

use crate::Error;

#[derive(Clone)]
pub struct SRS<P: Pairing> {
    pub g_alpha_powers: Vec<P::G1>,
    pub h_beta_powers: Vec<P::G2>,
    pub h_alpha: P::G2,
}

#[derive(Clone)]
pub struct VerifierSRS<P: Pairing> {
    pub g: P::G1,
    pub h: P::G2,
    pub h_alpha: P::G2,
}

//TODO: Change SRS to return reference iterator - requires changes to TIPA and GIPA signatures
impl<P: Pairing> SRS<P> {
    pub fn get_commitment_keys(&self) -> (Vec<P::G2>, Vec<P::G1>) {
        let ck_1 = self.h_beta_powers.iter().step_by(2).cloned().collect();
        let ck_2 = self.g_alpha_powers.iter().step_by(2).cloned().collect();
        (ck_1, ck_2)
    }

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

pub struct KZG<P: Pairing> {
    _pairing: PhantomData<P>,
}

// Simple implementation of KZG polynomial commitment scheme
impl<P: Pairing> KZG<P> {
    pub fn structured_generators_lagrange(
        num: usize,
        g: &P::G1,
        s: &P::ScalarField,
    ) -> Vec<P::G1> {
        assert!(num > 0);
        assert!(num.is_power_of_two());
        let domain = <GeneralEvaluationDomain<P::ScalarField> as EvaluationDomain<P::ScalarField>>::new(num).unwrap();
        let evals_of_lagrange = EvaluationDomain::evaluate_all_lagrange_coefficients(&domain, *s);
        // let mut pow_s = G::ScalarField::one();
        // for _ in 0..num {
        //     powers_of_scalar.push(pow_s);
        //     pow_s *= s;
        // }
    
        let window_size = FixedBase::get_mul_window_size(num);
    
        let scalar_bits = P::ScalarField::MODULUS_BIT_SIZE as usize;
        let g_table = FixedBase::get_window_table(scalar_bits, window_size, g.clone());
        let powers_of_g = FixedBase::msm::<P::G1>(scalar_bits, window_size, &g_table, &evals_of_lagrange);
        powers_of_g
    }


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
        polynomial: &UnivariatePolynomial<P::ScalarField>,
    ) -> Result<P::G1, Error> {
        assert!(powers.len() >= polynomial.degree() + 1);
        let mut coeffs = polynomial.coeffs.to_vec();
        coeffs.resize(powers.len(), <P::ScalarField>::zero());

        // Can unwrap because coeffs.len() is guaranteed to be equal to powers.len()
        Ok(P::G1::msm(powers, &coeffs).unwrap())
    }

    pub fn open(
        powers: &[P::G1Affine],
        polynomial: &UnivariatePolynomial<P::ScalarField>,
        point: &P::ScalarField,
    ) -> Result<P::G1, Error> {
        assert!(powers.len() >= polynomial.degree() + 1);

        // Trick to calculate (p(x) - p(z)) / (x - z) as p(x) / (x - z) ignoring remainder p(z)
        let quotient_polynomial = polynomial
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
        com: &P::G1,
        point: &P::ScalarField,
        eval: &P::ScalarField,
        proof: &P::G1,
    ) -> Result<bool, Error> {
        Ok(P::pairing(com.clone() - v_srs.g * eval, v_srs.h.clone())
            == P::pairing(proof.clone(), v_srs.h_alpha.clone() - v_srs.h * point))
    }
}


#[cfg(test)]
mod tests {
    // use super::*;
    use ark_bls12_381::Bls12_381;
    use ark_std::rand::{rngs::StdRng, SeedableRng};
    use ark_ff::UniformRand;
    use crate::trivial_kzg::KZG;

    use ark_poly::polynomial::{
        univariate::DensePolynomial as UnivariatePolynomial, DenseUVPolynomial, Polynomial,
    };
    use ark_ec::pairing::Pairing;

    use std::{io::stdout, time::{Duration, Instant}};

    use csv::Writer;

    // use blake2::Blake2b;

    // const BIVARIATE_X_DEGREE: usize = 7;
    // const BIVARIATE_Y_DEGREE: usize = 7;
    // //const UNIVARIATE_DEGREE: usize = 56;
    // const UNIVARIATE_DEGREE: usize = 65535;
    // //const UNIVARIATE_DEGREE: usize = 1048575;

    // type TestBivariatePolyCommitment = BivariatePolynomialCommitment<Bls12_381, Blake2b>;
    // type TestUnivariatePolyCommitment = UnivariatePolynomialCommitment<Bls12_381, Blake2b>;

    #[test]
    fn trivial_kzg_test() {

        let mut csv_writer = Writer::from_writer(stdout());
        csv_writer
            .write_record(&["trial", "scheme", "function", "degree", "time"])
            .unwrap();
        csv_writer.flush().unwrap();

        let log_degree = 10;
        let degree = (1 << log_degree) - 1;
        // let repeat: usize = 1;
        let mut rng = StdRng::seed_from_u64(0u64);

        let setup_start = Instant::now();
        let (g_alpha_powers, v_srs) = KZG::<Bls12_381>::setup(&mut rng, degree).unwrap();
        let time = setup_start.elapsed().as_millis();
        println!("KZG setup time, {:} log_degree: {:} ", degree, time);
        csv_writer
                .write_record(&[
                    1.to_string(),
                    "kzg".to_string(),
                    "setup".to_string(),
                    degree.to_string(),
                    time.to_string(),
                ])
                .unwrap();
            csv_writer.flush().unwrap();

        // for _ in 0..repeat {
        let polynomial = UnivariatePolynomial::rand(degree, &mut rng);
        let point = <Bls12_381 as Pairing>::ScalarField::rand(&mut rng);
        let eval = polynomial.evaluate(&point);

        // Commit
        let com_start = Instant::now();
        let com = KZG::<Bls12_381>::commit(&g_alpha_powers, &polynomial).unwrap();
        println!("KZG commi time, {:} log_degree: {:?} ", log_degree, com_start.elapsed());

        // Open
        let open_start = Instant::now();
        let proof = KZG::<Bls12_381>::open(&g_alpha_powers, &polynomial, &point).unwrap();
        println!("KZG open  time, {:} log_degree: {:?} ", log_degree, open_start.elapsed());

        // Verify
        std::thread::sleep(Duration::from_millis(5000));
        let verify_start = Instant::now();
        for _ in 0..50 {
            let is_valid =
                KZG::<Bls12_381>::verify(&v_srs, &com, &point, &eval, &proof).unwrap();
            assert!(is_valid);
        }
        let verify_time = verify_start.elapsed().as_millis() / 50;
        println!("KZG verif time, {:} log_degree: {:?}", log_degree, verify_time);
        csv_writer
        .write_record(&[
            1.to_string(),
            "kzg".to_string(),
            "verify".to_string(),
            degree.to_string(),
            verify_time.to_string(),
        ])
        .unwrap();
        csv_writer.flush().unwrap();
    }
}