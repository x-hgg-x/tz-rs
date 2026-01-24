//! Some useful system time functions.

use std::time::{Duration, SystemTime};

/// Returns the duration between Unix epoch (`1970-01-01T00:00:00Z`) and a `SystemTime`.
///
/// The `Ok` variant corresponds to a positive duration, and the `Err` variant to a negative duration.
fn duration_since_epoch(time: SystemTime) -> Result<Duration, Duration> {
    time.duration_since(SystemTime::UNIX_EPOCH).map_err(|e| e.duration())
}

/// Returns the Unix time in seconds for a `SystemTime`
pub(crate) fn unix_time(time: SystemTime) -> i64 {
    match duration_since_epoch(time) {
        Ok(duration) => 0i64.saturating_add_unsigned(duration.as_secs()),
        Err(duration) => 0i64.saturating_sub_unsigned(duration.as_secs()),
    }
}

/// Returns the total nanoseconds between Unix epoch (`1970-01-01T00:00:00Z`) and a `SystemTime`
pub(crate) fn total_nanoseconds(time: SystemTime) -> i128 {
    match duration_since_epoch(time) {
        Ok(duration) => 0i128.saturating_add_unsigned(duration.as_nanos()),
        Err(duration) => 0i128.saturating_sub_unsigned(duration.as_nanos()),
    }
}
