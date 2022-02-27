//! Some useful constant functions.

use crate::error::OutOfRangeError;
use crate::timezone::{LeapSecond, Transition};

use std::cmp::Ordering;

/// Compare two values
pub const fn cmp(a: i64, b: i64) -> Ordering {
    if a < b {
        Ordering::Less
    } else if a == b {
        Ordering::Equal
    } else {
        Ordering::Greater
    }
}

/// Returns the minimum of two values
pub const fn min(a: i64, b: i64) -> i64 {
    match cmp(a, b) {
        Ordering::Less | Ordering::Equal => a,
        Ordering::Greater => b,
    }
}

/// Convert a `i64` value to a `i32` value
pub const fn try_into_i32(value: i64) -> Result<i32, OutOfRangeError> {
    let min = i32::MIN as i64;
    let max = i32::MAX as i64;

    if min <= value && value <= max {
        Ok(value as i32)
    } else {
        Err(OutOfRangeError("out of range integer conversion"))
    }
}

/// Macro for implementing binary search
macro_rules! impl_binary_search {
    ($slice:expr, $f:expr, $x:expr) => {{
        let mut size = $slice.len();
        let mut left = 0;
        let mut right = size;
        while left < right {
            let mid = left + size / 2;

            let v = $f(&$slice[mid]);
            if v < $x {
                left = mid + 1;
            } else if v > $x {
                right = mid;
            } else {
                return Ok(mid);
            }

            size = right - left;
        }
        Err(left)
    }};
}

/// Copy the input value
const fn copied(x: &i64) -> i64 {
    *x
}

/// Binary searches a sorted `i64` slice for the given element
pub const fn binary_search_i64(slice: &[i64], x: i64) -> Result<usize, usize> {
    impl_binary_search!(slice, copied, x)
}

/// Binary searches a sorted `Transition` slice for the given element
pub const fn binary_search_transitions(slice: &[Transition], x: i64) -> Result<usize, usize> {
    impl_binary_search!(slice, Transition::unix_leap_time, x)
}

/// Binary searches a sorted `LeapSecond` slice for the given element
pub const fn binary_search_leap_seconds(slice: &[LeapSecond], x: i64) -> Result<usize, usize> {
    impl_binary_search!(slice, LeapSecond::unix_leap_time, x)
}
