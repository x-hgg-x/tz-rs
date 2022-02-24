use std::ops::Deref;
use std::time::Duration;

use crate::constants::NANOSECONDS_PER_SECOND;
use crate::error::{Result, TzError};

/// Internal trait to implement integral and real Unix times
pub trait UnixTime: Copy + PartialOrd + PartialEq + std::fmt::Debug {
    /// A type to store the nanoseconds of the this Unix time
    type Nanoseconds: Copy + Ord + Eq + std::fmt::Debug;

    /// Calculate the UnixTime from a sum of the seconds and nanoseconds
    fn from_seconds(secs: i64, nanos: Self::Nanoseconds) -> Self;

    /// Convert a Duration to a UnixSecond
    fn from_duration(duration: &Duration) -> Result<Self>;

    /// Add seconds to this UnixSeconds
    fn add_seconds(self, seconds: i64) -> Result<Self>;

    /// Extract the integral part of the UnixTime
    fn get_seconds(self) -> Result<i64>;

    /// Extract the nanoseconds of the UnixTime
    fn get_nanoseconds(self) -> Self::Nanoseconds;

    /// Ensure that the input is in the valid range
    fn validate_nanoseconds(nanos: Self::Nanoseconds) -> Result<()>;
}

impl UnixTime for i64 {
    type Nanoseconds = ();

    fn from_seconds(secs: i64, _: Self::Nanoseconds) -> Self {
        secs
    }

    fn from_duration(duration: &Duration) -> Result<Self> {
        Ok(duration.as_secs().try_into()?)
    }

    fn add_seconds(self, seconds: i64) -> Result<Self> {
        let seconds = seconds.try_into().map_err(|_| TzError::InvalidDateTime("invalid nanoseconds"))?;
        i64::checked_add(self, seconds).ok_or(TzError::InvalidDateTime("invalid nanoseconds"))
    }

    fn get_seconds(self) -> Result<i64> {
        Ok(self)
    }

    fn get_nanoseconds(self) -> Self::Nanoseconds {
        ()
    }

    fn validate_nanoseconds(_: Self::Nanoseconds) -> Result<()> {
        Ok(())
    }
}

impl UnixTime for f64 {
    type Nanoseconds = u32;

    fn from_seconds(secs: i64, nanos: Self::Nanoseconds) -> Self {
        (secs as f64) + (nanos as f64) * (1_f64 / NANOSECONDS_PER_SECOND as f64)
    }

    fn from_duration(duration: &Duration) -> Result<Self> {
        let result = duration.as_secs_f64();
        match result >= i64::MIN as _ && result <= i64::MAX as _ {
            true => Ok(result),
            false => Err(TzError::InvalidDateTime("invalid nanoseconds")),
        }
    }

    fn add_seconds(self, seconds: i64) -> Result<Self> {
        let result = self + seconds as f64;
        match result >= i64::MIN as _ && result <= i64::MAX as _ {
            true => Ok(result),
            false => Err(TzError::InvalidDateTime("invalid nanoseconds")),
        }
    }

    fn get_seconds(self) -> Result<i64> {
        let result = self.floor();
        match result >= i64::MIN as _ && result <= i64::MAX as _ {
            true => Ok(result as i64),
            false => Err(TzError::InvalidDateTime("invalid nanoseconds")),
        }
    }

    fn get_nanoseconds(self) -> Self::Nanoseconds {
        let result = (self - self.floor()) * (NANOSECONDS_PER_SECOND as f64);
        match result.is_finite() {
            true => result as u32,
            false => 0_u32,
        }
    }

    fn validate_nanoseconds(nanos: Self::Nanoseconds) -> Result<()> {
        match nanos < NANOSECONDS_PER_SECOND as _ {
            true => Ok(()),
            false => Err(TzError::InvalidDateTime("invalid nanoseconds")),
        }
    }
}

/// A UnixTime implemented by as a fixed point number with a factor of 1_000_000_000
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FixedPoint {
    /// Nanoseconds since 1970-01-01 00:00:00.
    pub nanoseconds: i128,
}

impl Deref for FixedPoint {
    type Target = i128;

    fn deref(&self) -> &Self::Target {
        &self.nanoseconds
    }
}

impl UnixTime for FixedPoint {
    type Nanoseconds = u32;

    fn from_seconds(secs: i64, nanos: Self::Nanoseconds) -> Self {
        Self {
            nanoseconds: secs as i128 * NANOSECONDS_PER_SECOND as i128 + nanos as i128,
        }
    }

    fn from_duration(duration: &Duration) -> Result<Self> {
        Ok(Self {
            nanoseconds: duration.as_nanos().try_into()?,
        })
    }

    fn add_seconds(self, seconds: i64) -> Result<Self> {
        const MIN: i128 = i64::MIN as i128 * NANOSECONDS_PER_SECOND as i128;
        const MAX: i128 = i64::MAX as i128 * NANOSECONDS_PER_SECOND as i128;

        let result = match seconds >= 0 {
            true => self.checked_add(seconds as i128),
            false => self.checked_sub(-(seconds as i128)),
        };
        match result.ok_or(TzError::InvalidDateTime("invalid nanoseconds"))? {
            nanoseconds @ (MIN..=MAX) => Ok(Self { nanoseconds }),
            _ => Err(TzError::InvalidDateTime("invalid nanoseconds")),
        }
    }

    fn get_seconds(self) -> Result<i64> {
        Ok((self.nanoseconds / NANOSECONDS_PER_SECOND as i128) as i64)
    }

    fn get_nanoseconds(self) -> Self::Nanoseconds {
        (self.nanoseconds % NANOSECONDS_PER_SECOND as i128) as u32
    }

    fn validate_nanoseconds(nanos: Self::Nanoseconds) -> Result<()> {
        match nanos < NANOSECONDS_PER_SECOND as _ {
            true => Ok(()),
            false => Err(TzError::InvalidDateTime("invalid nanoseconds")),
        }
    }
}
