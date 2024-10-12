use ark_ec::pairing::Pairing;
use ark_ff::{Field, One, Zero, UniformRand};
use ark_std::rand::{rngs::StdRng, SeedableRng};
use ark_poly::{univariate::DensePolynomial as UnivariatePolynomial, DenseUVPolynomial};

// This is a self-test of r1cs inner product piops
// We first generate a random r1cs instance inner products

#[derive(Clone)]
pub struct R1CSWitnessPolys<P: Pairing> {
    pub poly_w: UnivariatePolynomial<P::ScalarField>,
    pub poly_a: UnivariatePolynomial<P::ScalarField>,
    pub poly_b: UnivariatePolynomial<P::ScalarField>,
    pub poly_c: UnivariatePolynomial<P::ScalarField>,
}

#[derive(Clone)]
pub struct R1CSPublicPolys<P: Pairing> {
    pub poly_pa: UnivariatePolynomial<P::ScalarField>,
    pub poly_pb: UnivariatePolynomial<P::ScalarField>,
    pub poly_pc: UnivariatePolynomial<P::ScalarField>,
}

#[derive(Clone)]
pub struct R1CSDeWitnessPolys<P: Pairing> {
    pub polys_w: Vec<UnivariatePolynomial<P::ScalarField>>,
    pub polys_a: Vec<UnivariatePolynomial<P::ScalarField>>,
    pub polys_b: Vec<UnivariatePolynomial<P::ScalarField>>,
    pub polys_c: Vec<UnivariatePolynomial<P::ScalarField>>,
}

#[derive(Clone)]
pub struct R1CSDePublicPolys<P: Pairing> {
    pub polys_pa: Vec<UnivariatePolynomial<P::ScalarField>>,
    pub polys_pb: Vec<UnivariatePolynomial<P::ScalarField>>,
    pub polys_pc: Vec<UnivariatePolynomial<P::ScalarField>>,
}

#[derive(Clone)]
pub struct R1CSVectors<P: Pairing> {
    pub vec_x: Vec<P::ScalarField>,
    pub vec_y: Vec<P::ScalarField>,
    pub vec_z: Vec<P::ScalarField>,
    pub vec_w: Vec<P::ScalarField>,
    pub vec_a: Vec<P::ScalarField>,
    pub vec_b: Vec<P::ScalarField>,
    pub vec_c: Vec<P::ScalarField>,
    pub vec_r: Vec<P::ScalarField>,
}

#[derive(Clone)]
pub struct R1CSPubVectors<P: Pairing> {
    pub vec_x: Vec<P::ScalarField>,
    pub vec_y: Vec<P::ScalarField>,
    pub vec_z: Vec<P::ScalarField>,
}

// generate vectors x, y, z, w, a, b, r such that 
// <x, w> = <r, a>
// <y, w> = <r, b>
// <z, w> = <r, c>
// a \odot b = c
pub fn generate_r1cs_vectors<P: Pairing> (
    m: usize,
    l: usize,
    challenge_r: &P::ScalarField,
) -> (R1CSVectors<P>, R1CSPubVectors<P>) {

    let size = m * l;
    let mut rng = StdRng::seed_from_u64(0u64);

    let mut vec_r = Vec::new();
    let mut value_r = P::ScalarField::one();
    for _ in 0..size {
        vec_r.push(value_r.clone());
        value_r *= challenge_r;
    }
    assert!(vec_r[0] == P::ScalarField::one());
    assert!(vec_r[1] == *challenge_r);
    assert!(vec_r[2] == (*challenge_r).square());
      
    let mut vec_a = Vec::new();
    let mut vec_b = Vec::new();
    let mut vec_w = Vec::new();
    for _ in 0..size {
        vec_a.push(P::ScalarField::rand(&mut rng));
        vec_b.push(P::ScalarField::rand(&mut rng));
        vec_w.push(P::ScalarField::rand(&mut rng));
    }
    let vec_c: Vec<P::ScalarField> = vec_a.iter().zip(vec_b.iter()).map(|(a, b)| *a * *b).collect();

    let inner_product_first = get_inner_product::<P>(&vec_r, &vec_a);
    let vec_x = generate_half_vector_from_inner_product::<P>(&vec_w, &inner_product_first);
    let inner_product_second = get_inner_product::<P>(&vec_r, &vec_b);
    let vec_y = generate_half_vector_from_inner_product::<P>(&vec_w, &inner_product_second);
    let inner_product_third = get_inner_product::<P>(&vec_r, &vec_c);
    let vec_z = generate_half_vector_from_inner_product::<P>(&vec_w, &inner_product_third);

    (R1CSVectors {
        vec_x: vec_x.clone(),
        vec_y: vec_y.clone(),
        vec_z: vec_z.clone(),
        vec_w,
        vec_a,
        vec_b,
        vec_c,
        vec_r
    }, R1CSPubVectors {
        vec_x,
        vec_y,
        vec_z,
    })
}

pub fn generate_r1cs_de_vectors<P: Pairing> (
    sub_prover_id: usize,
    m: usize,
    l: usize,
    challenge_r: &P::ScalarField,
) -> (R1CSVectors<P>, R1CSPubVectors<P>) {

    let vectors_left = split_vector::<P>(&vector_left, m, l);
    let vectors_right = split_vector::<P>(&vector_right, m, l); 

    let size = m * l;
    let mut rng = StdRng::seed_from_u64(0u64);

    let mut vec_r = Vec::new();
    let mut value_r = P::ScalarField::one();
    for _ in 0..size {
        vec_r.push(value_r.clone());
        value_r *= challenge_r;
    }
      
    let mut vec_a = Vec::new();
    let mut vec_b = Vec::new();
    let mut vec_w = Vec::new();
    for _ in 0..size {
        vec_a.push(P::ScalarField::rand(&mut rng));
        vec_b.push(P::ScalarField::rand(&mut rng));
        vec_w.push(P::ScalarField::rand(&mut rng));
    }
    let vec_c: Vec<P::ScalarField> = vec_a.iter().zip(vec_b.iter()).map(|(a, b)| *a * *b).collect();

    let inner_product_first = get_inner_product::<P>(&vec_r, &vec_a);
    let vec_x = generate_half_vector_from_inner_product::<P>(&vec_w, &inner_product_first);
    let inner_product_second = get_inner_product::<P>(&vec_r, &vec_b);
    let vec_y = generate_half_vector_from_inner_product::<P>(&vec_w, &inner_product_second);
    let inner_product_third = get_inner_product::<P>(&vec_r, &vec_c);
    let vec_z = generate_half_vector_from_inner_product::<P>(&vec_w, &inner_product_third);

    (R1CSVectors {
        vec_x: vec_x.clone(),
        vec_y: vec_y.clone(),
        vec_z: vec_z.clone(),
        vec_w,
        vec_a,
        vec_b,
        vec_c,
        vec_r
    }, R1CSPubVectors {
        vec_x,
        vec_y,
        vec_z,
    })
}


pub fn generate_r1cs_polynomial_relation<P: Pairing> (
    m: usize,
    l: usize,
    challenge_r: &P::ScalarField,
) -> (R1CSVectors<P>, R1CSPublicPolys<P>, R1CSWitnessPolys<P>) {
    assert!(m.is_power_of_two());
    assert!(l.is_power_of_two());

    let (r1cs_vecs, _) = generate_r1cs_vectors::<P>(m, l, &challenge_r);

    let (polynomial_x, polynomial_w) = generate_sumcheck_polynomials_from_vectors::<P>(&r1cs_vecs.vec_x, &r1cs_vecs.vec_w);
    let (polynomial_y, _) = generate_sumcheck_polynomials_from_vectors::<P>(&r1cs_vecs.vec_y, &r1cs_vecs.vec_w);
    let (polynomial_z, _) = generate_sumcheck_polynomials_from_vectors::<P>(&r1cs_vecs.vec_z, &r1cs_vecs.vec_w);
    let (polynomial_a, polynomial_b) = generate_sumcheck_polynomials_from_vectors::<P>(&r1cs_vecs.vec_a, &r1cs_vecs.vec_b);
    let (polynomial_c, _) = generate_sumcheck_polynomials_from_vectors::<P>(&r1cs_vecs.vec_c, &r1cs_vecs.vec_b);

    (r1cs_vecs, R1CSPublicPolys {
        poly_pa: polynomial_x,
        poly_pb: polynomial_y,
        poly_pc: polynomial_z
    }, R1CSWitnessPolys {
        poly_a: polynomial_a,
        poly_b: polynomial_b,
        poly_c: polynomial_c,
        poly_w: polynomial_w
    })
}

pub fn generate_de_r1cs_polynomial_relation<P: Pairing> (
    m: usize,
    l: usize,
    challenge_r: &P::ScalarField,
) -> (R1CSVectors<P>, R1CSDePublicPolys<P>, R1CSDeWitnessPolys<P>) {
    assert!(m.is_power_of_two());
    assert!(l.is_power_of_two());

    let (r1cs_vecs, _) = generate_r1cs_vectors::<P>(m, l, &challenge_r);

    let (polynomials_x, polynomials_w) = generate_de_polynomials_from_vectors::<P>(m, l, &r1cs_vecs.vec_x, &r1cs_vecs.vec_w);
    let (polynomials_y, _) = generate_de_polynomials_from_vectors::<P>(m, l, &r1cs_vecs.vec_y, &r1cs_vecs.vec_w);
    let (polynomials_z, _) = generate_de_polynomials_from_vectors::<P>(m, l, &r1cs_vecs.vec_z, &r1cs_vecs.vec_w);
    let (polynomials_a, polynomials_b) = generate_de_polynomials_from_vectors::<P>(m, l, &r1cs_vecs.vec_a, &r1cs_vecs.vec_b);
    let (polynomials_c, _) = generate_de_polynomials_from_vectors::<P>(m, l, &r1cs_vecs.vec_c, &r1cs_vecs.vec_b);

    (r1cs_vecs, R1CSDePublicPolys {
        polys_pa: polynomials_x,
        polys_pb: polynomials_y,
        polys_pc: polynomials_z
    }, R1CSDeWitnessPolys {
        polys_a: polynomials_a,
        polys_b: polynomials_b,
        polys_c: polynomials_c,
        polys_w: polynomials_w
    })
}

pub fn generate_pub_r1cs_polynomials_from_vectors<P: Pairing> (
    r1cs_pub_vecs: &R1CSPubVectors<P>,
    m: usize,
    l: usize,
) -> R1CSDePublicPolys<P> {
    assert!(m.is_power_of_two());
    assert!(l.is_power_of_two());

    let polynomials_x = generate_de_polynomials_from_left_vector::<P>(m, l, &r1cs_pub_vecs.vec_x);
    let polynomials_y = generate_de_polynomials_from_left_vector::<P>(m, l, &r1cs_pub_vecs.vec_y);
    let polynomials_z = generate_de_polynomials_from_left_vector::<P>(m, l, &r1cs_pub_vecs.vec_z);

    R1CSDePublicPolys {
        polys_pa: polynomials_x,
        polys_pb: polynomials_y,
        polys_pc: polynomials_z
    }
}

pub fn generate_distributed_r1cs_polynomial_relation<P: Pairing> (
    sub_prover_id: usize,
    r1cs_vecs: &R1CSVectors<P>,
    m: usize,
    l: usize,
) -> (R1CSPublicPolys<P>, R1CSWitnessPolys<P>) {
    assert!(m.is_power_of_two());
    assert!(l.is_power_of_two());

    let (polynomials_x, polynomials_w) = generate_de_polynomials_from_vectors::<P>(m, l, &r1cs_vecs.vec_x, &r1cs_vecs.vec_w);
    let polynomials_y = generate_de_polynomials_from_left_vector::<P>(m, l, &r1cs_vecs.vec_y);
    let polynomials_z = generate_de_polynomials_from_left_vector::<P>(m, l, &r1cs_vecs.vec_z);
    let (polynomials_a, polynomials_b) = generate_de_polynomials_from_vectors::<P>(m, l, &r1cs_vecs.vec_a, &r1cs_vecs.vec_b);
    let polynomials_c = generate_de_polynomials_from_left_vector::<P>(m, l, &r1cs_vecs.vec_c);

    (R1CSPublicPolys {
        poly_pa: polynomials_x[sub_prover_id].clone(),
        poly_pb: polynomials_y[sub_prover_id].clone(),
        poly_pc: polynomials_z[sub_prover_id].clone()
    }, R1CSWitnessPolys {
        poly_a: polynomials_a[sub_prover_id].clone(),
        poly_b: polynomials_b[sub_prover_id].clone(),
        poly_c: polynomials_c[sub_prover_id].clone(),
        poly_w: polynomials_w[sub_prover_id].clone()
    })
}

pub fn generate_sumcheck_polynomials_from_vectors<P: Pairing> (
    vector_left: &Vec<P::ScalarField>,
    vector_right: &Vec<P::ScalarField>,
) -> (UnivariatePolynomial<P::ScalarField>, UnivariatePolynomial<P::ScalarField>) {
    let polynomial_left = UnivariatePolynomial::from_coefficients_vec(vector_left.clone());
    let mut coeffs_right = vec![vector_right[0].clone()];
    let mut rest = vector_right.clone().split_off(1);
    rest.reverse();
    coeffs_right.extend(rest);
    assert!(vector_left.len() == coeffs_right.len());
    assert_eq!(vector_right[0], coeffs_right[0]);
    assert_eq!(coeffs_right[1], vector_right[vector_right.len()-1]);
    
    let polynomial_right = UnivariatePolynomial::from_coefficients_vec(coeffs_right);

    (polynomial_left, polynomial_right)
}

pub fn generate_de_polynomials_from_vectors<P: Pairing> (
    m: usize,
    l: usize,
    vector_left: &Vec<P::ScalarField>,
    vector_right: &Vec<P::ScalarField>,
) -> (Vec<UnivariatePolynomial<P::ScalarField>>, Vec<UnivariatePolynomial<P::ScalarField>>) {
    assert_eq!(vector_left.len(), vector_right.len());
    assert_eq!(vector_left.len(), m * l);

    let mut polys_left = Vec::new();
    let mut polys_right = Vec::new();

    let vectors_left = split_vector::<P>(&vector_left, m, l);
    let vectors_right = split_vector::<P>(&vector_right, m, l);

    for i in 0..vectors_left.len() {
        polys_left.push(UnivariatePolynomial::from_coefficients_vec(vectors_left[i].clone()));

        let mut coeffs_right = vec![vectors_right[i][0].clone()];
        let mut rest = vectors_right[i].clone().split_off(1);
        rest.reverse();
        coeffs_right.extend(rest);
        
        polys_right.push(UnivariatePolynomial::from_coefficients_vec(coeffs_right));
    }

    (polys_left, polys_right)
}

pub fn generate_de_polynomials_from_left_vector<P: Pairing> (
    m: usize,
    l: usize,
    vector_left: &Vec<P::ScalarField>,
) -> Vec<UnivariatePolynomial<P::ScalarField>> {
    assert_eq!(vector_left.len(), m * l);

    let mut polys_left = Vec::new();

    let vectors_left = split_vector::<P>(&vector_left, m, l);

    for i in 0..vectors_left.len() {
        polys_left.push(UnivariatePolynomial::from_coefficients_vec(vectors_left[i].clone()));
    }

    polys_left
}

pub fn split_vector<P: Pairing>(vec: &Vec<P::ScalarField>, m: usize, l: usize) -> Vec<Vec<P::ScalarField>> {
    assert!(vec.len() == m * l);
    vec.chunks(m).take(l).map(|chunk| chunk.to_vec()).collect()
}

pub fn get_inner_product<P: Pairing> (
    left_vec: &Vec<P::ScalarField>,
    right_vec: &Vec<P::ScalarField>,
) -> P::ScalarField {
    assert_eq!(left_vec.len(), right_vec.len());
    left_vec.iter().zip(right_vec.iter()).map(|(left, right)| *left * *right).sum()    
}

pub fn generate_half_vector_from_inner_product<P: Pairing> (
    vec: &Vec<P::ScalarField>,
    inner_product: &P::ScalarField,
) -> Vec<P::ScalarField> {
    let mut result = Vec::new();
    let size = vec.len();
    let mut rng = StdRng::seed_from_u64(0u64);

    for _ in 0..size-1 {
        result.push(P::ScalarField::rand(&mut rng));
    }
    result.push(P::ScalarField::zero());

    let cur_inner_product = get_inner_product::<P>(&vec, &result);
    let target = *inner_product - cur_inner_product;
    let last_entry = target / vec[size-1];
    result[size - 1] = last_entry;

    result
}

// #[cfg(test)]
// mod tests {
//     use ark_ec::pairing::Pairing;
//     use ark_bls12_381::Bls12_381;
//     use ark_std::rand::{rngs::StdRng, SeedableRng};
//     use ark_ff::{UniformRand,
//         Field, Zero, One
//     };
//     use super::{generate_half_vector_from_inner_product, generate_r1cs_inner_relation, generate_r1cs_polynomial_relation, get_inner_product, generate_de_r1cs_polynomial_relation};
//     use crate::ipa::IPA;
//     use ark_poly::{
//         univariate::DensePolynomial as UnivariatePolynomial, DenseUVPolynomial, EvaluationDomain, GeneralEvaluationDomain, Polynomial
//     };

//     #[test]
//     fn generate_half_vector_test() {
//         let mut rng = StdRng::seed_from_u64(0u64);
//         let size: usize = 10;
          
//         let mut vec_a = Vec::new();
//         let mut vec_b = Vec::new();
//         let mut vec_w = Vec::new();

//         for _ in 0..size {
//             vec_a.push(<Bls12_381 as Pairing>::ScalarField::rand(&mut rng));
//             vec_b.push(<Bls12_381 as Pairing>::ScalarField::rand(&mut rng));
//             vec_w.push(<Bls12_381 as Pairing>::ScalarField::rand(&mut rng));
//         }

//         let inner_product = get_inner_product::<Bls12_381>(&vec_a, &vec_b);
//         let vec_v = generate_half_vector_from_inner_product::<Bls12_381>(&vec_w, &inner_product);
//         assert_eq!(inner_product, get_inner_product::<Bls12_381>(&vec_w, &vec_v));
//     }

//     #[test]
//     fn generate_r1cs_inner_relation_test() {
//         let mut rng = StdRng::seed_from_u64(0u64);
//         let m: usize = 10;
//         let l: usize = 4;
//         let challenge_r = <Bls12_381 as Pairing>::ScalarField::rand(&mut rng);

//         let (vectors, _) = generate_r1cs_inner_relation::<Bls12_381>(m, l, &challenge_r);

//         assert_eq!(get_inner_product::<Bls12_381>(&vectors.vec_x, &vectors.vec_w), get_inner_product::<Bls12_381>(&vectors.vec_r, &vectors.vec_a));
//         assert_eq!(get_inner_product::<Bls12_381>(&vectors.vec_y, &vectors.vec_w), get_inner_product::<Bls12_381>(&vectors.vec_r, &vectors.vec_b));
//         assert_eq!(get_inner_product::<Bls12_381>(&vectors.vec_z, &vectors.vec_w), get_inner_product::<Bls12_381>(&vectors.vec_r, &vectors.vec_c));
//         let vec_ar: Vec<<Bls12_381 as Pairing>::ScalarField> = vectors.vec_a.iter().zip(vectors.vec_r.iter()).map(|(left, right)| *left * *right).collect();
//         assert_eq!(get_inner_product::<Bls12_381>(&vec_ar, &vectors.vec_b), get_inner_product::<Bls12_381>(&vectors.vec_r, &vectors.vec_c));

//         // test randomness
//         let (vectors_test, _) = generate_r1cs_inner_relation::<Bls12_381>(m, l, &challenge_r);
//         assert_eq!(vectors.vec_a, vectors_test.vec_a);
//         assert_eq!(vectors.vec_b, vectors_test.vec_b);
//         assert_eq!(vectors.vec_c, vectors_test.vec_c);
//         assert_eq!(vectors.vec_x, vectors_test.vec_x);
//         assert_eq!(vectors.vec_y, vectors_test.vec_y);
//         assert_eq!(vectors.vec_z, vectors_test.vec_z);
//         assert_eq!(vectors.vec_w, vectors_test.vec_w);
//         assert_eq!(vectors.vec_r, vectors_test.vec_r);
//     }

//     #[test]
//     fn generate_r1cs_poly_relation_test() {
//         let mut rng = StdRng::seed_from_u64(0u64);
//         let m: usize = 1usize << 5;
//         let l: usize = 4;
//         let challenge_r = <Bls12_381 as Pairing>::ScalarField::rand(&mut rng);
//         let size = m * l;
//         let x_domain = <GeneralEvaluationDomain<<Bls12_381 as Pairing>::ScalarField> as EvaluationDomain<<Bls12_381 as Pairing>::ScalarField>>::new(size).unwrap();

//         let (r1cs_vecs, pub_polys, wit_polys) = generate_r1cs_polynomial_relation::<Bls12_381>(m, l, &challenge_r);

//         // first tuple
//         let poly_pa_w = &pub_polys.poly_pa * &wit_polys.poly_w;
//         let sum_pa_w = IPA::<Bls12_381>::get_sum_on_domain(&poly_pa_w, &x_domain);
//         let eval_a_r = wit_polys.poly_a.evaluate(&challenge_r);
//         assert_eq!(sum_pa_w, eval_a_r * x_domain.size_as_field_element());

//         // second tuple
//         let poly_pb_w = &pub_polys.poly_pb * &wit_polys.poly_w;
//         let sum_pb_w = IPA::<Bls12_381>::get_sum_on_domain(&poly_pb_w, &x_domain);
//         let r_power = challenge_r.pow([size as u64]);
//         let eval_b_0 = wit_polys.poly_b.evaluate(&<Bls12_381 as Pairing>::ScalarField::zero());
//         let eval_b_r = wit_polys.poly_b.evaluate(&challenge_r.inverse().unwrap()) * r_power + eval_b_0 * (<Bls12_381 as Pairing>::ScalarField::one() - r_power);
//         assert_eq!(sum_pb_w, eval_b_r * x_domain.size_as_field_element());

//         // third tuple
//         let poly_pc_w = &pub_polys.poly_pc * &wit_polys.poly_w;
//         let sum_pc_w = IPA::<Bls12_381>::get_sum_on_domain(&poly_pc_w, &x_domain);
//         let eval_c_r = wit_polys.poly_c.evaluate(&challenge_r);
//         assert_eq!(sum_pc_w, eval_c_r * x_domain.size_as_field_element());

//         // fourth tuple
//         let coeffs_a = wit_polys.poly_a.coeffs.to_vec();
//         let coeffs_ar: Vec<<Bls12_381 as Pairing>::ScalarField> = coeffs_a.iter().zip(r1cs_vecs.vec_r.iter()).map(|(left, right)| *left * *right).collect();
//         let poly_ar = UnivariatePolynomial::from_coefficients_vec(coeffs_ar);
//         let poly_ar_b = &poly_ar * &wit_polys.poly_b;
//         let sum_ar_b = IPA::<Bls12_381>::get_sum_on_domain(&poly_ar_b, &x_domain);
//         let eval_c_r = wit_polys.poly_c.evaluate(&challenge_r);
//         assert_eq!(sum_ar_b, eval_c_r * x_domain.size_as_field_element());

//     }


//     #[test]
//     fn generate_de_r1cs_poly_relation_test() {
//         let mut rng = StdRng::seed_from_u64(0u64);
//         let m: usize = 1usize << 5;
//         let l: usize = 4;
//         let challenge_r = <Bls12_381 as Pairing>::ScalarField::rand(&mut rng);
//         let size = m * l;
//         let x_domain = <GeneralEvaluationDomain<<Bls12_381 as Pairing>::ScalarField> as EvaluationDomain<<Bls12_381 as Pairing>::ScalarField>>::new(m).unwrap();
//         let _large_domain = <GeneralEvaluationDomain<<Bls12_381 as Pairing>::ScalarField> as EvaluationDomain<<Bls12_381 as Pairing>::ScalarField>>::new(size).unwrap();

//         let (r1cs_vecs, pub_polys, wit_polys) = generate_de_r1cs_polynomial_relation::<Bls12_381>(m, l, &challenge_r);

//         // get (1, r^m, r^{2m} ..., r^{(l-1)m})
//         let mut r_powers = Vec::new();
//         for i in 0..l {
//             let index = i * m;
//             r_powers.push(r1cs_vecs.vec_r[index]);
//         }
//         assert_eq!(r_powers[0], <Bls12_381 as Pairing>::ScalarField::one());
//         assert_eq!(r_powers[1], challenge_r.pow([m as u64]));

//         // get (1, r, r^{2} ..., r^{m-1})
//         let mut r_m_powers = Vec::new();
//         let mut current = <Bls12_381 as Pairing>::ScalarField::one();
//         for _ in 0..m {
//             r_m_powers.push(current.clone());
//             current *= challenge_r;
//         }
//         assert_eq!(r_m_powers[0], <Bls12_381 as Pairing>::ScalarField::one());
//         assert_eq!(r_m_powers[1], challenge_r);
//         assert_eq!(r_m_powers[m-1], challenge_r.pow([(m - 1) as u64]));

//         // first tuple
//         let polys_pa_w: Vec<UnivariatePolynomial<<Bls12_381 as Pairing>::ScalarField>> = pub_polys.polys_pa.iter().zip(wit_polys.polys_w.iter()).map(|(poly_pa, poly_w)| poly_pa * poly_w).collect();
//         let mut poly_pa_w = UnivariatePolynomial::zero();
//         for poly in polys_pa_w {
//             poly_pa_w += &poly;
//         }
//         let sum_pa_w = IPA::<Bls12_381>::get_sum_on_domain(&poly_pa_w, &x_domain);
//         let eval_a_r: <Bls12_381 as Pairing>::ScalarField = wit_polys.polys_a.iter().zip(r_powers.iter()).map(|(poly, r_power)| poly.evaluate(&challenge_r) * r_power).sum();
//         assert_eq!(sum_pa_w, eval_a_r * x_domain.size_as_field_element());

//         // second tuple
//         let polys_pb_w: Vec<UnivariatePolynomial<<Bls12_381 as Pairing>::ScalarField>> = pub_polys.polys_pb.iter().zip(wit_polys.polys_w.iter()).map(|(poly_pb, poly_w)| poly_pb * poly_w).collect();
//         let mut poly_pb_w = UnivariatePolynomial::zero();
//         for poly in polys_pb_w {
//             poly_pb_w += &poly;
//         }
//         let sum_pb_w = IPA::<Bls12_381>::get_sum_on_domain(&poly_pb_w, &x_domain);
//         let r_pow_m = challenge_r.pow([m as u64]);
//         let evals_b_0: Vec<<Bls12_381 as Pairing>::ScalarField> = wit_polys.polys_b.iter().map(|poly_b| poly_b.evaluate(&<Bls12_381 as Pairing>::ScalarField::zero())).collect();
//         let eval_b_r: <Bls12_381 as Pairing>::ScalarField = wit_polys.polys_b.iter().zip(r_powers.iter()).zip(evals_b_0.iter())
//             .map(|((poly, r_power), eval)| (poly.evaluate(&challenge_r.inverse().unwrap()) * r_pow_m + eval * &(<Bls12_381 as Pairing>::ScalarField::one() - r_pow_m)) * r_power).sum();
//         assert_eq!(sum_pb_w, eval_b_r * x_domain.size_as_field_element());

//         // third tuple
//         let polys_pc_w: Vec<UnivariatePolynomial<<Bls12_381 as Pairing>::ScalarField>> = pub_polys.polys_pc.iter().zip(wit_polys.polys_w.iter()).map(|(poly_pc, poly_w)| poly_pc * poly_w).collect();
//         let mut poly_pc_w = UnivariatePolynomial::zero();
//         for poly in polys_pc_w {
//             poly_pc_w += &poly;
//         }
//         let sum_pc_w = IPA::<Bls12_381>::get_sum_on_domain(&poly_pc_w, &x_domain);
//         let eval_c_r: <Bls12_381 as Pairing>::ScalarField = wit_polys.polys_c.iter().zip(r_powers.iter()).map(|(poly, r_power)| poly.evaluate(&challenge_r) * r_power).sum();
//         assert_eq!(sum_pc_w, eval_c_r * x_domain.size_as_field_element());

//         // fourth tuple
//         let coeffs_a_vec: Vec<Vec<<Bls12_381 as Pairing>::ScalarField>> = wit_polys.polys_a.iter().map(|poly_a| poly_a.coeffs.to_vec()).collect();
//         let mut polys_ar = Vec::new();
//         for coeff_a_vec in coeffs_a_vec {
//             let coeff_ar_vec: Vec<<Bls12_381 as Pairing>::ScalarField> = coeff_a_vec.iter().zip(r_m_powers.iter()).map(|(left, right)| *left * *right).collect();
//             polys_ar.push(UnivariatePolynomial::from_coefficients_vec(coeff_ar_vec));
//         }
//         let polys_ar_b: Vec<UnivariatePolynomial<<Bls12_381 as Pairing>::ScalarField>> = polys_ar.iter().zip(wit_polys.polys_b.iter()).zip(r_powers.iter()).map(|((poly_ar, poly_b), r_power)| &(poly_ar * poly_b) * *r_power).collect();
//         let mut poly_ar_b = UnivariatePolynomial::zero();
//         for poly in polys_ar_b {
//             poly_ar_b += &poly;
//         }
//         let sum_ar_b = IPA::<Bls12_381>::get_sum_on_domain(&poly_ar_b, &x_domain);
//         assert_eq!(sum_ar_b, eval_c_r * x_domain.size_as_field_element());

//     }
// }