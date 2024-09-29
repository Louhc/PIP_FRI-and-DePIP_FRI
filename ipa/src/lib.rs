#![deny(warnings, unused, future_incompatible, nonstandard_style)]

pub mod sumcheck;
pub mod ipa;
pub mod ipa_from_laurent;

use std::error::Error as ErrorTrait;
pub type Error = Box<dyn ErrorTrait>;