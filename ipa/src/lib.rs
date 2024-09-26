#![deny(warnings, unused, future_incompatible, nonstandard_style)]

pub mod sumcheck;

use std::error::Error as ErrorTrait;
pub type Error = Box<dyn ErrorTrait>;