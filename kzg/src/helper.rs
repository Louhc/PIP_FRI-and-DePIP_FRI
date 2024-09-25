use ark_ec::{
    pairing::Pairing,
    // scalar_mul::fixed_base::FixedBase,
};
use ark_ff::{One, Field, Zero};
use ark_poly::polynomial::{
    univariate::DensePolynomial as UnivariatePolynomial, DenseUVPolynomial, Polynomial
};
use std::collections::HashSet;

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
        -points_without_repeat[0].clone(),
        P::ScalarField::one()
    ]);
    for i in 1..points.len() {
        let current_polynomial = UnivariatePolynomial::from_coefficients_vec(vec![
            -points[i].clone(),
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
    let mut result_polynomial = UnivariatePolynomial::zero();

    // let mut numerator_polynomial = UnivariatePolynomial::from_coefficients_vec(vec![
    //     -points[0].clone(),
    //     P::ScalarField::one()
    // ]);
    // for i in 1..points.len() {
    //     let current_polynomial = UnivariatePolynomial::from_coefficients_vec(vec![
    //         -points[i].clone(),
    //         P::ScalarField::one()
    //     ]); 
    //     numerator_polynomial = &numerator_polynomial * &current_polynomial;
    // }
    let numerator_polynomial = generator_numerator_polynomial::<P>(&points);

    // test for correctness
    assert!(numerator_polynomial.degree() == points.len());
    for i in 0..points.len() {
        assert!(numerator_polynomial.evaluate(&points[i]) == P::ScalarField::zero());
    }

    for i in 0..points.len() {
        let mut constant_term = P::ScalarField::one();
        for j in 0..points.len() {
            if j!= i {
                constant_term *= points[i] - points[j];
            }
        }
        constant_term = constant_term.inverse().unwrap();
        constant_term *= evals[i];
        
        let divider_polynomial = &UnivariatePolynomial::from_coefficients_vec(vec![
            -points[i].clone(),
            P::ScalarField::one()
            ]);
        let quotient_polynomial = &numerator_polynomial / &divider_polynomial;
        result_polynomial += &(&quotient_polynomial * constant_term);
    }
    result_polynomial   
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
