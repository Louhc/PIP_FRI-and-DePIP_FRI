use ark_ec::pairing::Pairing;
use rayon::prelude::*;

pub fn inner_product <P: Pairing> (
    vec_1: &Vec<P::ScalarField>,
    vec_2: &Vec<P::ScalarField>,
) -> P::ScalarField {
    vec_1.par_iter().zip(vec_2.par_iter()).map(|(left, right)| left.clone() * right.clone()).sum()
}

pub fn entry_product <P: Pairing> (
    vec_1: &Vec<P::ScalarField>,
    vec_2: &Vec<P::ScalarField>,
) -> Vec<P::ScalarField> {
    vec_1.par_iter().zip(vec_2.par_iter()).map(|(left, right)| left.clone() * right.clone()).collect()
}

pub fn matrix_mul <P: Pairing> (
    matrix: &Vec<Vec<P::ScalarField>>,
    vec: &Vec<P::ScalarField>,
) -> Vec<P::ScalarField> {
    assert_eq!(matrix[0].len(), vec.len());
    matrix.par_iter().map(|row| inner_product::<P>(row, &vec)).collect()
}

pub fn vec_matrix_mul <P: Pairing> (
    vec: &Vec<P::ScalarField>,
    matrix: &Vec<Vec<P::ScalarField>>,
) -> Vec<P::ScalarField> {
    assert_eq!(matrix.len(), vec.len());
    (0..matrix[0].len()).into_par_iter().map(|j| {
        matrix.par_iter().zip(vec.par_iter()).map(|(row, val)| row[j] * val).sum()
    }).collect()
}

pub fn split_vector <P: Pairing>(vec: &Vec<P::ScalarField>) -> (Vec<P::ScalarField>, Vec<P::ScalarField>) {
    let mid = vec.len() / 2;
    let (first_half, second_half) = vec.split_at(mid);
    (first_half.to_vec(), second_half.to_vec())
}

#[cfg(test)]
mod tests{
    use ark_poly::{EvaluationDomain, GeneralEvaluationDomain, Polynomial, univariate::DensePolynomial as UnivariatePolynomial};
    use ark_bls12_381::Bls12_381;
    use ark_ec::pairing::Pairing;
    type MyField = <Bls12_381 as Pairing>::ScalarField;
    use ark_ff::{One, Zero, Field};
    use crate::{gadgets_and_tests::{entry_product, split_vector, vec_matrix_mul}, indexer::Indexer, prover_pre::PreProver};
    use super::matrix_mul;
    use crate::indexer::{DeRowIndex, DeColIndex, DeValEvals, NEvals};
    // use ark_std::rand::{rngs::StdRng, SeedableRng};
    // use ark_ff::UniformRand;
    use my_ipa::{helper::generate_r1cs_pub_polynomials, r1cs::R1CSPubVectors};
    use my_ipa::ipa::IPA;
    use my_kzg::par_join_3;
    use rayon::prelude::*;

#[test]
fn matrix_mul_test() {
    let f_zero = MyField::zero();
    let f_one = MyField::one();
    let f_two = MyField::from(2);
    let f_four = MyField::from(4);
    let pa = vec![vec![f_one, f_zero, f_zero, f_zero],
            vec![f_zero, f_two, f_zero, f_zero],
            vec![f_zero, f_zero, f_two, f_zero],
            vec![f_zero, f_zero, f_zero, f_one]];

    let pb = vec![vec![f_zero, f_zero, f_zero, f_one],
            vec![f_zero, f_zero, f_two, f_zero],
            vec![f_zero, f_two, f_zero, f_zero],
            vec![f_one, f_zero, f_zero, f_zero]];

    let pc = vec![vec![f_two, f_zero, f_zero, f_zero],
            vec![f_zero, f_four, f_zero, f_zero],
            vec![f_zero, f_zero, f_four, f_zero],
            vec![f_zero, f_zero, f_zero, f_two]];

    let w = vec![f_two, f_one, f_one, f_two];

    let a = matrix_mul::<Bls12_381>(&pa, &w);
    let b = matrix_mul::<Bls12_381>(&pb, &w);
    let c = matrix_mul::<Bls12_381>(&pc, &w);

    assert_eq!(c, entry_product::<Bls12_381>(&a, &b));

    assert_eq!(vec_matrix_mul::<Bls12_381>(&w, &pa), vec![f_two; 4]);
}

// two sub-provers, 
// m = m_prime = 2
#[test]
fn evaluation_test() {
    let m = 2;
    let l = 2;
    let m_prime = 2;

    let f_zero = MyField::zero();
    let f_one = MyField::one();
    let f_two = MyField::from(2);
    let f_four = MyField::from(4);
    let pa = vec![vec![f_one, f_zero, f_zero, f_zero],
            vec![f_zero, f_two, f_zero, f_zero],
            vec![f_zero, f_zero, f_two, f_zero],
            vec![f_zero, f_zero, f_zero, f_one]];

    let pb = vec![vec![f_zero, f_zero, f_zero, f_one],
            vec![f_zero, f_zero, f_two, f_zero],
            vec![f_zero, f_two, f_zero, f_zero],
            vec![f_one, f_zero, f_zero, f_zero]];

    let pc = vec![vec![f_two, f_zero, f_zero, f_zero],
            vec![f_zero, f_four, f_zero, f_zero],
            vec![f_zero, f_zero, f_four, f_zero],
            vec![f_zero, f_zero, f_zero, f_two]];

    let w = vec![f_two, f_one, f_one, f_two];
    let a = matrix_mul::<Bls12_381>(&pa, &w);
    let b = matrix_mul::<Bls12_381>(&pb, &w);
    let c = matrix_mul::<Bls12_381>(&pc, &w);
    assert_eq!(c, entry_product::<Bls12_381>(&a, &b));

    // TODO: consider m_prime is not power-of-two
    let row_1 = DeRowIndex {
        row_pa_low: vec![0, 1], row_pa_high: vec![0, 0],
        row_pb_low: vec![0, 1], row_pb_high: vec![1, 1],
        row_pc_low: vec![0, 1], row_pc_high: vec![0, 0]
    };
    let row_2 = DeRowIndex {
        row_pa_low: vec![0, 1], row_pa_high: vec![1, 1],
        row_pb_low: vec![0, 1], row_pb_high: vec![0, 0],
        row_pc_low: vec![0, 1], row_pc_high: vec![1, 1]
    };

    let col_1 = DeColIndex {
        col_pa: vec![0, 1],
        col_pb: vec![1, 0],
        col_pc: vec![0, 1]
    };
    let col_2 = DeColIndex {
        col_pa: vec![0, 1],
        col_pb: vec![1, 0],
        col_pc: vec![0, 1]
    };

    let val_1 = DeValEvals::<Bls12_381> {
        evals_val_pa: vec![f_one, f_two],
        evals_val_pb: vec![f_two, f_one],
        evals_val_pc: vec![f_two, f_four]
    };
    let val_2 = DeValEvals::<Bls12_381> {
        evals_val_pa: vec![f_two, f_one],
        evals_val_pb: vec![f_one, f_two],
        evals_val_pc: vec![f_four, f_two]
    };
    let val_evals = vec![val_1, val_2];

    let _n_1 = NEvals::<Bls12_381> {
        row_pa_low: vec![f_one, f_one],
        row_pa_high: vec![f_two, f_zero],
        row_pb_low: vec![f_one, f_one],
        row_pb_high: vec![f_zero, f_two],
        row_pc_low: vec![f_one, f_one],
        row_pc_high: vec![f_two, f_zero],
        col_pa: vec![f_one, f_one],
        col_pb: vec![f_one, f_one],
        col_pc: vec![f_one, f_one]
    };
    let _n_2 = NEvals::<Bls12_381> {
        row_pa_low: vec![f_one, f_one],
        row_pa_high: vec![f_zero, f_two],
        row_pb_low: vec![f_one, f_one],
        row_pb_high: vec![f_two, f_zero],
        row_pc_low: vec![f_one, f_one],
        row_pc_high: vec![f_zero, f_two],
        col_pa: vec![f_one, f_one],
        col_pb: vec![f_one, f_one],
        col_pc: vec![f_one, f_one]
    };

    // let mut rng = StdRng::seed_from_u64(0u64);
    // let r = MyField::rand(&mut rng);
    // let alpha = MyField::rand(&mut rng);
    // let beta = MyField::rand(&mut rng);
    let r = f_two;
    let alpha = f_one;
    let beta = f_one;
    let x_domain =  <GeneralEvaluationDomain<MyField> as EvaluationDomain<MyField>>::new(m).unwrap();
    let y_domain =  <GeneralEvaluationDomain<MyField> as EvaluationDomain<MyField>>::new(l).unwrap();
    let m_domain =  <GeneralEvaluationDomain<MyField> as EvaluationDomain<MyField>>::new(m_prime).unwrap();
    let eval_beta: Vec<MyField> = y_domain.evaluate_all_lagrange_coefficients(beta);

    // compute f_V(alpha, beta) from A, B
    let (upper_a_t_polys_1, _upper_a_t_evals_1) = PreProver::<Bls12_381>::compute_upper_a_t_polys_from_rows(m, l, &x_domain, &m_domain, &row_1, &r);
    let (upper_a_t_polys_2, _upper_a_t_evals_2) = PreProver::<Bls12_381>::compute_upper_a_t_polys_from_rows(m, l, &x_domain, &m_domain, &row_2, &r);
    let (upper_b_t_polys_1, _upper_b_t_evals_1) = PreProver::<Bls12_381>::compute_upper_b_t_polys_from_cols(m, &x_domain, &m_domain, &col_1, &alpha);
    let (upper_b_t_polys_2, _upper_b_t_evals_2) = PreProver::<Bls12_381>::compute_upper_b_t_polys_from_cols(m, &x_domain, &m_domain, &col_2, &alpha);
    let val_polys = Indexer::<Bls12_381>::compute_val_polys(l, &m_domain, &val_evals);
    let upper_a_t_polys = vec![upper_a_t_polys_1, upper_a_t_polys_2];
    let upper_b_t_polys = vec![upper_b_t_polys_1, upper_b_t_polys_2];
    let poly_pa_alpha_beta: UnivariatePolynomial<MyField> = val_polys.par_iter().
        zip(upper_a_t_polys.par_iter()).
        zip(upper_b_t_polys.par_iter()).
        zip(eval_beta.par_iter()).
        map(|(((val, upper_a), upper_b), l)| 
        {
            &(&(&(&val.val_pa * &upper_a.a_pa_low) * &upper_a.a_pa_high) * &upper_b.b_pa) * *l
        }).reduce_with(|acc, poly| acc + poly)
        .unwrap_or(UnivariatePolynomial::zero());
    let eval_pa_alpha_beta_from_sum = IPA::<Bls12_381>::get_sum_on_domain(&poly_pa_alpha_beta, &m_domain);
    let poly_pb_alpha_beta: UnivariatePolynomial<MyField> = val_polys.par_iter().
        zip(upper_a_t_polys.par_iter()).
        zip(upper_b_t_polys.par_iter()).
        zip(eval_beta.par_iter()).
        map(|(((val, upper_a), upper_b), l)| 
        {
            &(&(&(&val.val_pb * &upper_a.a_pb_low) * &upper_a.a_pb_high) * &upper_b.b_pb) * *l
        }).reduce_with(|acc, poly| acc + poly)
        .unwrap_or(UnivariatePolynomial::zero());
    let eval_pb_alpha_beta_from_sum = IPA::<Bls12_381>::get_sum_on_domain(&poly_pb_alpha_beta, &m_domain);
    let poly_pc_alpha_beta: UnivariatePolynomial<MyField> = val_polys.par_iter().
        zip(upper_a_t_polys.par_iter()).
        zip(upper_b_t_polys.par_iter()).
        zip(eval_beta.par_iter()).
        map(|(((val, upper_a), upper_b), l)| 
        {
            &(&(&(&val.val_pc * &upper_a.a_pc_low) * &upper_a.a_pc_high) * &upper_b.b_pc) * *l
        }).reduce_with(|acc, poly| acc + poly)
        .unwrap_or(UnivariatePolynomial::zero());
    let eval_pc_alpha_beta_from_sum = IPA::<Bls12_381>::get_sum_on_domain(&poly_pc_alpha_beta, &m_domain);


    // the true value
    let vec_r = vec![f_one, r, r.square(), r.pow([3 as u64])];
    let x = vec_matrix_mul::<Bls12_381>(&vec_r, &pa);
    let y = vec_matrix_mul::<Bls12_381>(&vec_r, &pb);
    let z = vec_matrix_mul::<Bls12_381>(&vec_r, &pc);

    let (x_1, x_2) = split_vector::<Bls12_381>(&x);
    let (y_1, y_2) = split_vector::<Bls12_381>(&y);
    let (z_1, z_2) = split_vector::<Bls12_381>(&z);

    let de_pub_vecs = vec![
        R1CSPubVectors::<Bls12_381> {vec_x: x_1, vec_y: y_1, vec_z: z_1},
        R1CSPubVectors::<Bls12_381> {vec_x: x_2, vec_y: y_2, vec_z: z_2}
    ];
    let pub_polys = generate_r1cs_pub_polynomials(&de_pub_vecs);

    let (eval_pa_alpha_beta, eval_pb_alpha_beta, eval_pc_alpha_beta)
    : (MyField, MyField, MyField) = par_join_3!(
        || pub_polys.polys_pa.par_iter().zip(eval_beta.par_iter()).map(|(poly, eval)| poly.evaluate(&alpha) * eval).sum(),
        || pub_polys.polys_pb.par_iter().zip(eval_beta.par_iter()).map(|(poly, eval)| poly.evaluate(&alpha) * eval).sum(), 
        || pub_polys.polys_pc.par_iter().zip(eval_beta.par_iter()).map(|(poly, eval)| poly.evaluate(&alpha) * eval).sum()
    );

    assert_eq!(eval_pa_alpha_beta, eval_pa_alpha_beta_from_sum);
    assert_eq!(eval_pc_alpha_beta, eval_pc_alpha_beta_from_sum);
    assert_eq!(eval_pb_alpha_beta, eval_pb_alpha_beta_from_sum);

}

}