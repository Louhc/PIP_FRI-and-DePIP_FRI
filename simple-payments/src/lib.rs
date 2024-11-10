pub use ark_ed_on_bls12_381::EdwardsProjective;
pub use ark_ed_on_bls12_381::constraints::EdwardsVar;
pub type ConstraintFq = ark_ed_on_bls12_381::Fq;
pub type ConstraintF = ark_bls12_381::Fr;

// pub use ark_ed_on_bn254::EdwardsProjective;
// pub use ark_ed_on_bn254::constraints::EdwardsVar;
// pub type ConstraintFq = ark_ed_on_bn254::Fq;
// pub type ConstraintF = ark_bls12_381::Fr;

pub mod account;
pub mod ledger;
pub mod transaction;

pub mod random_oracle;
pub mod signature;

extern crate derivative;
