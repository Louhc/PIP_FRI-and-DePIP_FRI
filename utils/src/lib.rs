pub mod fp17;
// pub mod fp64;

pub mod merkle_tree;
pub mod helper;
pub mod goldilocks;
pub mod query_result;
pub mod fiat_shamir;
pub mod commit_open_vec;
pub mod interpolate_vecs_value;

pub const CODE_RATE: usize = 3;
pub const SECURITY_BITS: usize = 100;