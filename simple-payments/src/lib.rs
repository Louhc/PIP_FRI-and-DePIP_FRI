pub use ark_ed_on_bls12_381::EdwardsProjective;
pub use ark_ed_on_bls12_381::constraints::EdwardsVar;
pub type ConstraintFq = ark_ed_on_bls12_381::Fq;
pub type ConstraintF = ark_bls12_381::Fr;
pub type ConstraintP = ark_bls12_381::Bls12_381;

// pub use ark_ed_on_bn254::EdwardsProjective;
// pub use ark_ed_on_bn254::constraints::EdwardsVar;
// pub type ConstraintF = ark_bn254::Fr;
// pub type ConstraintP = ark_bn254::Bn254;
// pub type ConstraintFq = ark_ed_on_bn254::Fq;

pub mod account;
pub mod ledger;
pub mod transaction;

pub mod random_oracle;
pub mod signature;

extern crate derivative;
