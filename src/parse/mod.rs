//! Parsing functions.

mod tz_file;
mod tz_string;

pub(crate) use tz_file::{get_tz_file, parse_tz_file};
pub(crate) use tz_string::parse_posix_tz;
