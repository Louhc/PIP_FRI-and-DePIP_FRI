use ark_ec::{
    pairing::Pairing,
    Group,
    CurveGroup, AffineRepr
};
use ark_ff::{One, Field, Zero};
use ark_poly::{polynomial::{
    univariate::DensePolynomial as UnivariatePolynomial, DenseUVPolynomial
}   , 
    GeneralEvaluationDomain, EvaluationDomain};
use std::collections::HashSet;
use rayon::prelude::*;

pub fn generator_numerator_polynomial<P: Pairing> (
    points: &Vec<P::ScalarField>
) -> UnivariatePolynomial<P::ScalarField> {

    let mut points_without_repeat: Vec<P::ScalarField> = Vec::new();
    let mut unique_points = HashSet::new();

    for point in points {
        if !unique_points.contains(point) {
            unique_points.insert(*point);
            points_without_repeat.push(*point);
        }
    }

    let mut numerator_polynomial = UnivariatePolynomial::from_coefficients_vec(vec![
        -points_without_repeat[0],
        P::ScalarField::one()
    ]);
    for i in 1..points.len() {
        let current_polynomial = UnivariatePolynomial::from_coefficients_vec(vec![
            -points[i],
            P::ScalarField::one()
        ]); 
        numerator_polynomial = &numerator_polynomial * &current_polynomial;
    }
    numerator_polynomial
}


pub fn interpolate_on_trivial_domain<P: Pairing> (
    points: &Vec<P::ScalarField>, 
    evals: &Vec<P::ScalarField>,
) -> UnivariatePolynomial<P::ScalarField> {
    assert_eq!(points.len(), evals.len());
    // let mut result_polynomial = UnivariatePolynomial::zero();

    let numerator_polynomial = generator_numerator_polynomial::<P>(&points);

    points.par_iter().enumerate().map(|(i, &point_i)| {
        let mut constant_term = P::ScalarField::one();
        for (j, &point_j) in points.iter().enumerate() {
            if i != j {
                constant_term *= point_i - point_j;
            }
        }
        constant_term = constant_term.inverse().unwrap();
        constant_term *= evals[i];
        
        let divider_polynomial = &UnivariatePolynomial::from_coefficients_vec(vec![
            -point_i.clone(),
            P::ScalarField::one()
            ]);
        let quotient_polynomial = &numerator_polynomial / &divider_polynomial;
        &quotient_polynomial * constant_term
    }).reduce(
        || UnivariatePolynomial::zero(),
        |acc, poly| acc + poly
    )
}

// evaluate one evaluation of the id-th lagrange polynomial at the given point
pub fn evaluate_one_lagrange<P: Pairing>(
    id: usize,
    domain: &GeneralEvaluationDomain<P::ScalarField>,
    point: &P::ScalarField,
) -> <P as Pairing>::ScalarField {
    // g^{i-1} / size \cdot Y^{size} - 1 / Y - g^{i-1}
    // id can be zero
    let g_pow_i_minus_one = domain.group_gen().pow([id as u64]);

    if *point == g_pow_i_minus_one {
        P::ScalarField::one()
    }
    else {
        let size = domain.size();
        let size_field = domain.size_as_field_element();
        let point_pow_size = (*point).pow([size as u64]) - P::ScalarField::one();
        g_pow_i_minus_one * point_pow_size * (size_field * (*point - g_pow_i_minus_one)).inverse().unwrap()
    }
}

pub fn get_x_srs<P: Pairing> (
    powers: &Vec<Vec<P::G1Affine>>,
) -> Vec<P::G1Affine> {
    let mut x_srs: Vec<P::G1> = vec![P::G1::zero(); powers[0].len()];
    for i in 0..powers[0].len() {
        for j in 0..powers.len() {
            x_srs[i] += powers[j][i].into_group();
        }
    }
    assert!(x_srs[0] == P::G1::generator());
    let x_srs = P::G1::normalize_batch(&x_srs);
    x_srs
}

pub fn linear_combination_poly<P: Pairing> (
    polynomials: &Vec<UnivariatePolynomial<P::ScalarField>>,
    challenge: &P::ScalarField,
) -> UnivariatePolynomial<P::ScalarField> {

    let mut linear_factors = vec![P::ScalarField::one(); polynomials.len()];
        linear_factors.par_iter_mut().enumerate().for_each(|(i, val)| {
            *val = challenge.pow([i as u64]);
    });
    // an example of polynomial rlc using par_iter()
    let combined_polynomial = polynomials.par_iter().zip(linear_factors.par_iter())
        .map(|(poly, factor)| poly * *factor)
        .reduce_with(|acc, poly| acc + poly)
        .unwrap_or(UnivariatePolynomial::zero());

    combined_polynomial
}

pub fn linear_combination_field<P: Pairing> (
    values: &Vec<P::ScalarField>,
    challenge: &P::ScalarField,
) -> P::ScalarField {

    let mut linear_factor = P::ScalarField::one();
    let mut result = P::ScalarField::zero();

    for value in values {
        result += *value * linear_factor;
        linear_factor *= challenge;
    }
    result
}

#[cfg(test)]
mod tests {
    use ark_ec::pairing::Pairing;
    use ark_bls12_381::Bls12_381;
    use crate::helper::interpolate_on_trivial_domain;
    use ark_std::rand::{rngs::StdRng, SeedableRng};
    use ark_poly::polynomial::{
        univariate::DensePolynomial as UnivariatePolynomial, DenseUVPolynomial, Polynomial,
    };
    use ark_ff::UniformRand;

    #[test]
    fn trivial_polynomial_interpolation_test() {

        const DEGREE: usize = 10;
        let mut rng = StdRng::seed_from_u64(0u64);
        let polynomial = UnivariatePolynomial::rand(DEGREE, &mut rng);

        let points: Vec<<Bls12_381 as Pairing>::ScalarField> = (0..DEGREE+1).map(|_| <Bls12_381 as Pairing>::ScalarField::rand(&mut rng)).collect();
        let evaluations = points.iter().map(|point| polynomial.evaluate(point)).collect();
        let polynomial_interpolation = interpolate_on_trivial_domain::<Bls12_381>(&points, &evaluations);
        assert_eq!(polynomial, polynomial_interpolation);

    }

}
