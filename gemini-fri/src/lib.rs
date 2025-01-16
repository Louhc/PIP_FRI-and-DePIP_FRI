pub mod prover;
pub mod verifier;
pub mod test;

use ark_ff::PrimeField;

#[derive(Debug, Clone)]
pub struct Tuple<T: PrimeField> {
    pub a: T,
    pub b: T,
    pub c: T,
}

impl<T: PrimeField> Tuple<T> {
    pub fn verify(&self, beta: T, folding_param: T) -> bool {
        let v = beta * (self.a + self.b) + folding_param * (self.a - self.b);
        v == self.c * beta * T::from_u64(2 as u64).unwrap()
    }
}