use ark_ff::{BigInteger, PrimeField};
use std::marker::PhantomData;
use ark_serialize::*;
use ark_poly::{DenseUVPolynomial, EvaluationDomain, GeneralEvaluationDomain, Polynomial};
use ark_poly::univariate::DensePolynomial as UnivariatePolynomial;

#[derive(Debug, Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct Helper<T: PrimeField> {
    _field: PhantomData<T>,
}

impl<T: PrimeField> Helper<T> {

    pub fn as_bytes_vec(s: &[T]) -> Vec<u8> {
        let mut res = vec![];
        for i in s {
            res.append(&mut i.into_bigint().to_bytes_be());
        }
        res
    }

    pub fn to_bytes_vec(s: &[T]) -> Vec<u8> {
        let mut res = vec![];
        for i in s {
            res.append(&mut i.into_bigint().to_bytes_be().to_vec());
        }
        res
    }

    pub fn pow(coset: &GeneralEvaluationDomain<T>, index: usize) -> GeneralEvaluationDomain<T> {
        assert_eq!(index & (index - 1), 0);
        let lowbit = (index as i64 & (-(index as i64))) as usize;
        GeneralEvaluationDomain::new_coset(
            coset.size() / lowbit,
            coset.coset_offset().pow([index as u64]),
        ).unwrap()
    }

    // use for generate sub-polynomials
    pub fn split_polynomial(polynomial: UnivariatePolynomial<T>, m: usize, l: usize) -> Vec<UnivariatePolynomial<T>> {
        let coeffs = polynomial.coeffs();
        let mut result = Vec::with_capacity(l);
        for i in 0..l {
            let start = i * m;
            let end = start + m;
            let slice = &coeffs[start..end];
            result.push(UnivariatePolynomial::from_coefficients_slice(&slice));
        }
        result
    }

}


#[derive(Debug, Clone)]
pub struct MultilinearPolynomial<T: PrimeField>
    {
        coefficients: Vec<T>,
    }

impl<T: PrimeField> MultilinearPolynomial<T> {
    pub fn coefficients(&self) -> &Vec<T> {
        &self.coefficients
    }

    // pub fn evaluate_hypercube(&self) -> Vec<T> {
    //     let log_n = self.variable_num();
    //     let n = self.coefficients.len();
    //     let rank = batch_bit_reverse(log_n);
    //     let mut res = self.coefficients.clone();
    //     for i in 0..n {
    //         if i < rank[i] {
    //             (res[i], res[rank[i]]) = (res[rank[i]], res[i]);
    //         }
    //     }
    //     for i in 0..log_n {
    //         let m = 1 << i;
    //         for j in (0..n).step_by(m * 2) {
    //             for k in 0..m {
    //                 let tmp = res[j + k];
    //                 res[j + k + m] += tmp;
    //             }
    //         }
    //     }
    //     res
    // }

    pub fn new(coefficients: Vec<T>) -> Self {
        let len = coefficients.len();
        assert_eq!(len & (len - 1), 0);
        MultilinearPolynomial { coefficients }
    }

    pub fn folding(&self, parameter: T) -> Self {
        let coefficients = Self::folding_vector(&self.coefficients, parameter);
        MultilinearPolynomial { coefficients }
    }

    fn folding_vector(v: &Vec<T>, parameter: T) -> Vec<T> {
        let len = v.len();
        assert_eq!(len & (len - 1), 0);
        let mut res = vec![];
        for i in (0..v.len()).step_by(2) {
            res.push(v[i] + parameter * v[i + 1]);
        }
        res
    }

    pub fn rand(variable_num: usize) -> Self {
        let mut rng = rand::thread_rng();
        MultilinearPolynomial {
            coefficients: (0..(1 << variable_num))
                .map(|_| T::rand(&mut rng))
                .collect(),
        }
    }

    // led, evaluate a multilinear polynomial at point
    pub fn evaluate(&self, point: &Vec<T>) -> T {
        let len = self.coefficients.len();
        assert_eq!(1 << point.len(), self.coefficients.len());
        let mut res = self.coefficients.clone();
        for (index, coeff) in point.iter().enumerate() {
            for i in (0..len).step_by(2 << index) {
                let x = *coeff * res[i + (1 << index)];
                res[i] += x;
            }
        }
        res[0]
    }

    // set the coefficient as univariate polynomial coefficient and then evaluate at point
    pub fn evaluate_as_uni_polynomial(&self, point: T) -> T {
        let mut res = T::zero();
        for i in self.coefficients.iter().rev() {
            res *= point;
            res += *i;
        }
        res
    }

    pub fn variable_num(&self) -> usize {
        self.coefficients.len().ilog2() as usize
    }

    // divide into poly_num sub-polynomials
    pub fn chunks(&self, poly_num: usize) -> Vec<MultilinearPolynomial<T>> {
        let chunk_size = self.coefficients.len() / poly_num;
        self.coefficients
            .chunks(chunk_size)
            .map(|sub_poly| Self::new(sub_poly.to_vec()))
            .collect()
    }
}