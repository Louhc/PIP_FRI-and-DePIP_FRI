#![deny(warnings, unused, future_incompatible, nonstandard_style)]

pub mod sumcheck;
pub mod ipa;

use std::error::Error as ErrorTrait;
pub type Error = Box<dyn ErrorTrait>;