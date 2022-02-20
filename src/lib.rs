#![forbid(unsafe_code)]
#![deny(missing_docs)]

//! This crate provides the `TimeZone` and `DateTime` structs, which can be used to determine local time on a given time zone.
//!
//! This allows to convert between an [Unix timestamp](https://en.wikipedia.org/wiki/Unix_time) and a calendar time exprimed in the [proleptic gregorian calendar](https://en.wikipedia.org/wiki/Proleptic_Gregorian_calendar) with a provided time zone.
//!
//! Time zones are provided to the library with a [POSIX `TZ` string](https://pubs.opengroup.org/onlinepubs/9699919799/basedefs/V1_chap08.html) which can be read from the environment.
//!
//! Two formats are currently accepted for the `TZ` string:
//! * `std offset[dst[offset][,start[/time],end[/time]]]` providing a time zone description
//! * `file` or `:file` providing the path to a [TZif file](https://datatracker.ietf.org/doc/html/rfc8536), which is absolute or relative to the system timezone directory.
//!
//! # Usage
//!
//! ## Time zone
//!
//! ```rust
//! # fn main() -> Result<(), tz::TzError> {
//!     use tz::TimeZone;
//!
//!     // 2000-01-01T00:00:00Z
//!     let unix_time = 946684800;
//!
//!     // Get UTC time zone
//!     let time_zone_utc = TimeZone::utc();
//!     assert_eq!(time_zone_utc.find_local_time_type(unix_time)?.ut_offset(), 0);
//!
//!     // Get fixed time zone at GMT-1
//!     let time_zone_fixed = TimeZone::fixed(-3600);
//!     assert_eq!(time_zone_fixed.find_local_time_type(unix_time)?.ut_offset(), -3600);
//!
//!     // Get local time zone (UNIX only)
//!     let time_zone_local = TimeZone::local()?;
//!     // Get the current local time type
//!     let _current_local_time_type = time_zone_local.find_current_local_time_type()?;
//!
//!     // Get time zone from a TZ string:
//!     // From an absolute file
//!     let _ = TimeZone::from_posix_tz("/usr/share/zoneinfo/Pacific/Auckland");
//!     // From a file relative to the system timezone directory
//!     let _ = TimeZone::from_posix_tz("Pacific/Auckland");
//!     // From a time zone description
//!     TimeZone::from_posix_tz("HST10")?;
//!     TimeZone::from_posix_tz("<-03>3")?;
//!     TimeZone::from_posix_tz("NZST-12:00:00NZDT-13:00:00,M10.1.0,M3.3.0")?;
//!     // Use a leading colon to force searching for a corresponding file
//!     let _ = TimeZone::from_posix_tz(":UTC");
//! # Ok(())
//! # }
//! ```
//!
//! ## Date time
//!
//! ```rust
//! # fn main() -> Result<(), tz::TzError> {
//!     use tz::{DateTime, TimeZone, UtcDateTime};
//!
//!     // Get the current UTC date time
//!     let _current_utc_date_time = UtcDateTime::now()?;
//!
//!     // Create a new UTC date time (2000-01-01T00:00:00Z)
//!     let utc_date_time = UtcDateTime::new(2000, 0, 1, 0, 0, 0)?;
//!     assert_eq!(utc_date_time.second(), 0);
//!     assert_eq!(utc_date_time.minute(), 0);
//!     assert_eq!(utc_date_time.hour(), 0);
//!     assert_eq!(utc_date_time.month_day(), 1);
//!     assert_eq!(utc_date_time.month(), 0);
//!     assert_eq!(utc_date_time.year(), 100);
//!     assert_eq!(utc_date_time.full_year(), 2000);
//!     assert_eq!(utc_date_time.week_day(), 6);
//!     assert_eq!(utc_date_time.year_day(), 0);
//!     assert_eq!(utc_date_time.unix_time(), 946684800);
//!
//!     // Create a new UTC date time from a Unix time (2000-01-01T00:00:00Z)
//!     let other_utc_date_time = UtcDateTime::from_unix_time(946684800)?;
//!     assert_eq!(other_utc_date_time, utc_date_time);
//!
//!     // Project the UTC date time to a time zone
//!     let date_time = utc_date_time.project(&TimeZone::fixed(-3600))?;
//!     assert_eq!(date_time.second(), 0);
//!     assert_eq!(date_time.minute(), 0);
//!     assert_eq!(date_time.hour(), 23);
//!     assert_eq!(date_time.month_day(), 31);
//!     assert_eq!(date_time.month(), 11);
//!     assert_eq!(date_time.year(), 99);
//!     assert_eq!(date_time.full_year(), 1999);
//!     assert_eq!(date_time.week_day(), 5);
//!     assert_eq!(date_time.year_day(), 364);
//!     assert_eq!(date_time.local_time_type().ut_offset(), -3600);
//!     assert_eq!(date_time.unix_time(), 946684800);
//!
//!     // Project the date time to another time zone
//!     let other_date_time = date_time.project(&TimeZone::fixed(3600))?;
//!     assert_eq!(other_date_time.second(), 0);
//!     assert_eq!(other_date_time.minute(), 0);
//!     assert_eq!(other_date_time.hour(), 1);
//!     assert_eq!(other_date_time.month_day(), 1);
//!     assert_eq!(other_date_time.month(), 0);
//!     assert_eq!(other_date_time.year(), 100);
//!     assert_eq!(other_date_time.full_year(), 2000);
//!     assert_eq!(other_date_time.week_day(), 6);
//!     assert_eq!(other_date_time.year_day(), 0);
//!     assert_eq!(other_date_time.local_time_type().ut_offset(), 3600);
//!     assert_eq!(other_date_time.unix_time(), 946684800);
//!
//!     // Get the current date time at the local time zone (UNIX only)
//!     let time_zone_local = TimeZone::local()?;
//!     let _date_time = DateTime::now(&time_zone_local)?;
//! # Ok(())
//! # }
//! ```

mod constants;
mod tz_file;
mod tz_string;
mod utils;

use std::cmp::Ordering;
use std::error;
use std::fmt;
use std::fs::{self, File};
use std::io::{self, Read};
use std::num::TryFromIntError;
use std::sync::Arc;
use std::time::{SystemTime, SystemTimeError};

use tz_file::TzFileError;
use tz_string::TzStringError;

/// Alias for [`std::result::Result`] with the crate unified error
pub type Result<T> = std::result::Result<T, TzError>;

/// Unified error type for everything in the crate
#[non_exhaustive]
#[derive(Debug)]
pub enum TzError {
    /// Integer conversion error
    ConversionError(TryFromIntError),
    /// I/O error
    IoError(io::Error),
    /// System time error
    SystemTimeError(SystemTimeError),
    /// Unified error for parsing a TZif file
    TzFileError(TzFileError),
    /// Unified error for parsing a TZ string
    TzStringError(TzStringError),
    /// Date time input error
    DateTimeInputError(&'static str),
    /// No available local type type
    NoLocalTimeType,
}

impl fmt::Display for TzError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::ConversionError(error) => error.fmt(f),
            Self::IoError(error) => error.fmt(f),
            Self::SystemTimeError(error) => error.fmt(f),
            Self::TzFileError(error) => error.fmt(f),
            Self::TzStringError(error) => error.fmt(f),
            Self::DateTimeInputError(error) => write!(f, "invalid date time input: {}", error),
            Self::NoLocalTimeType => write!(f, "no local time type is available for the specified timestamp"),
        }
    }
}

impl error::Error for TzError {}

impl From<TryFromIntError> for TzError {
    fn from(error: TryFromIntError) -> Self {
        Self::ConversionError(error)
    }
}

impl From<io::Error> for TzError {
    fn from(error: io::Error) -> Self {
        Self::IoError(error)
    }
}

impl From<SystemTimeError> for TzError {
    fn from(error: SystemTimeError) -> Self {
        Self::SystemTimeError(error)
    }
}

impl From<TzFileError> for TzError {
    fn from(error: TzFileError) -> Self {
        Self::TzFileError(error)
    }
}

impl From<TzStringError> for TzError {
    fn from(error: TzStringError) -> Self {
        Self::TzStringError(error)
    }
}

/// Transition of a TZif file
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
struct Transition {
    /// Unix leap time
    unix_leap_time: i64,
    /// Index specifying the local time type of the transition
    local_time_type_index: usize,
}

/// Leap second of a TZif file
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
struct LeapSecond {
    /// Unix leap time
    unix_leap_time: i64,
    /// Leap second correction
    correction: i32,
}

/// Local time type associated to a time zone
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct LocalTimeType {
    /// Offset from UTC in seconds
    ut_offset: i32,
    /// Daylight Saving Time indicator
    is_dst: bool,
    /// Time zone designation
    time_zone_designation: Option<Arc<str>>,
}

impl LocalTimeType {
    /// Returns offset from UTC in seconds
    pub fn ut_offset(&self) -> i32 {
        self.ut_offset
    }

    /// Returns daylight saving time indicator
    pub fn is_dst(&self) -> bool {
        self.is_dst
    }

    /// Returns time zone designation
    pub fn time_zone_designation(&self) -> &str {
        self.time_zone_designation.as_deref().unwrap_or_default()
    }

    /// Construct the local time type associated to UTC
    pub fn utc() -> Self {
        Self::with_ut_offset(0)
    }

    /// Construct a local time type with the specified offset in seconds
    pub fn with_ut_offset(ut_offset: i32) -> Self {
        Self { ut_offset, is_dst: false, time_zone_designation: None }
    }
}

/// Transition rule day
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
enum RuleDay {
    /// Julian day in `[1, 365]`, without taking occasional Feb 29 into account, which is not referenceable
    Julian1WithoutLeap(u16),
    /// Zero-based Julian day in `[0, 365]`, taking occasional Feb 29 into account
    Julian0WithLeap(u16),
    /// Day represented by a month, a month week and a week day
    MonthWeekDay {
        /// Month in `[1, 12]`
        month: u8,
        /// Week of the month in `[1, 5]`, with `5` representing the last week of the month
        week: u8,
        /// Day of the week in `[0, 6]` from Sunday
        week_day: u8,
    },
}

impl RuleDay {
    /// Get the transition date for the provided year
    ///
    /// ## Inputs
    ///
    /// * `year`: Years since 1900
    ///
    /// ## Outputs
    ///
    /// * `month`: Month in `[0, 11]`
    /// * `month_day`: Day of the month in `[1, 31]`
    ///
    fn transition_date(&self, year: i32) -> (usize, i64) {
        use constants::*;

        match *self {
            Self::Julian1WithoutLeap(year_day) => {
                let year_day = year_day.into();
                let month = CUM_DAY_IN_MONTHS_NORMAL_YEAR[1..].partition_point(|&x| x < year_day);
                let month_day = year_day - CUM_DAY_IN_MONTHS_NORMAL_YEAR[month];

                (month, month_day)
            }
            Self::Julian0WithLeap(year_day) => {
                let leap = is_leap_year(year) as i64;

                let cum_day_in_months =
                    [0, 31, 59 + leap, 90 + leap, 120 + leap, 151 + leap, 181 + leap, 212 + leap, 243 + leap, 273 + leap, 304 + leap, 334 + leap, 365 + leap];

                let year_day = year_day.into();
                let month = cum_day_in_months[1..].partition_point(|&x| x <= year_day);
                let month_day = 1 + year_day - cum_day_in_months[month];

                (month, month_day)
            }
            Self::MonthWeekDay { month: rule_month, week, week_day } => {
                let leap = is_leap_year(year) as i64;

                let month = rule_month as usize - 1;

                let mut day_in_month = DAY_IN_MONTHS_NORMAL_YEAR[month];
                if month == 1 {
                    day_in_month += leap;
                }

                let week_day_of_first_month_day = (4 + days_since_unix_epoch(year, month, 1)).rem_euclid(DAYS_PER_WEEK);
                let first_week_day_occurence_in_month = 1 + (week_day as i64 - week_day_of_first_month_day).rem_euclid(DAYS_PER_WEEK);

                let mut month_day = first_week_day_occurence_in_month + (week as i64 - 1) * DAYS_PER_WEEK;
                if month_day > day_in_month {
                    month_day -= DAYS_PER_WEEK
                }

                (month, month_day)
            }
        }
    }

    /// Returns the UTC Unix time in seconds associated to the transition date for the provided year
    ///
    /// ## Inputs
    ///
    /// * `year`: Years since 1900
    /// * `day_time_in_utc`: UTC day time in seconds
    ///
    fn unix_time(&self, year: i32, day_time_in_utc: i64) -> i64 {
        use constants::*;

        let (month, month_day) = self.transition_date(year);
        days_since_unix_epoch(year, month, month_day) * SECONDS_PER_DAY + day_time_in_utc
    }
}

/// Transition rule
#[derive(Debug, Clone, Eq, PartialEq)]
enum TransitionRule {
    /// Fixed local time type
    Fixed(LocalTimeType),
    /// Alternate local time type
    Alternate {
        /// Local time type for standard time
        std: LocalTimeType,
        /// Local time type for Daylight Saving Time
        dst: LocalTimeType,
        /// Start day of Daylight Saving Time
        dst_start: RuleDay,
        /// Local start day time of Daylight Saving Time, in seconds
        dst_start_time: i32,
        /// End day of Daylight Saving Time
        dst_end: RuleDay,
        /// Local end day time of Daylight Saving Time, in seconds
        dst_end_time: i32,
    },
}

impl TransitionRule {
    /// Find the local time type associated to the transition rule at the specified Unix time in seconds
    fn find_local_time_type(&self, unix_time: i64) -> Result<&LocalTimeType> {
        match self {
            Self::Fixed(local_time_type) => Ok(local_time_type),
            Self::Alternate { std, dst, dst_start, dst_start_time, dst_end, dst_end_time } => {
                let dst_start_time_in_utc = (dst_start_time - std.ut_offset).into();
                let dst_end_time_in_utc = (dst_end_time - dst.ut_offset).into();

                let current_year = UtcDateTime::from_unix_time(unix_time)?.year();

                let current_year_dst_start_unix_time = dst_start.unix_time(current_year, dst_start_time_in_utc);
                let current_year_dst_end_unix_time = dst_end.unix_time(current_year, dst_end_time_in_utc);

                // Check DST start/end Unix times for previous/current/next years to support for transition day times outside of [0h, 24h] range
                let is_dst = match current_year_dst_start_unix_time.cmp(&current_year_dst_end_unix_time) {
                    Ordering::Less | Ordering::Equal => {
                        if unix_time < current_year_dst_start_unix_time {
                            let previous_year_dst_end_unix_time = dst_end.unix_time(current_year - 1, dst_end_time_in_utc);
                            if unix_time < previous_year_dst_end_unix_time {
                                let previous_year_dst_start_unix_time = dst_start.unix_time(current_year - 1, dst_start_time_in_utc);
                                previous_year_dst_start_unix_time <= unix_time
                            } else {
                                false
                            }
                        } else if unix_time < current_year_dst_end_unix_time {
                            true
                        } else {
                            let next_year_dst_start_unix_time = dst_start.unix_time(current_year + 1, dst_start_time_in_utc);
                            if next_year_dst_start_unix_time <= unix_time {
                                let next_year_dst_end_unix_time = dst_end.unix_time(current_year + 1, dst_end_time_in_utc);
                                unix_time < next_year_dst_end_unix_time
                            } else {
                                false
                            }
                        }
                    }
                    Ordering::Greater => {
                        if unix_time < current_year_dst_end_unix_time {
                            let previous_year_dst_start_unix_time = dst_start.unix_time(current_year - 1, dst_start_time_in_utc);
                            if unix_time < previous_year_dst_start_unix_time {
                                let previous_year_dst_end_unix_time = dst_end.unix_time(current_year - 1, dst_end_time_in_utc);
                                unix_time < previous_year_dst_end_unix_time
                            } else {
                                true
                            }
                        } else if unix_time < current_year_dst_start_unix_time {
                            false
                        } else {
                            let next_year_dst_end_unix_time = dst_end.unix_time(current_year + 1, dst_end_time_in_utc);
                            if next_year_dst_end_unix_time <= unix_time {
                                let next_year_dst_start_unix_time = dst_start.unix_time(current_year + 1, dst_start_time_in_utc);
                                next_year_dst_start_unix_time <= unix_time
                            } else {
                                true
                            }
                        }
                    }
                };

                if is_dst {
                    Ok(dst)
                } else {
                    Ok(std)
                }
            }
        }
    }
}

/// Time zone
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct TimeZone {
    /// List of transitions
    transitions: Vec<Transition>,
    /// List of local time types
    local_time_types: Vec<LocalTimeType>,
    /// List of leap seconds
    leap_seconds: Vec<LeapSecond>,
    /// Extra transition rule applicable after the last transition
    extra_rule: Option<TransitionRule>,
}

impl TimeZone {
    /// Returns UTC time zone
    pub fn utc() -> Self {
        Self::fixed(0)
    }

    /// Returns time zone with fixed UTC offset in seconds
    pub fn fixed(ut_offset: i32) -> Self {
        Self { transitions: Vec::new(), local_time_types: vec![LocalTimeType::with_ut_offset(ut_offset)], leap_seconds: Vec::new(), extra_rule: None }
    }

    /// Returns local time zone.
    ///
    /// This method in not supported on non-UNIX platforms, and returns the UTC time zone instead.
    ///
    pub fn local() -> Result<Self> {
        #[cfg(not(unix))]
        let local_time_zone = Self::utc();

        #[cfg(unix)]
        let local_time_zone = Self::from_posix_tz("localtime")?;

        Ok(local_time_zone)
    }

    /// Construct a time zone from a POSIX TZ string, as described in [the POSIX documentation of the `TZ` environment variable](https://pubs.opengroup.org/onlinepubs/9699919799/basedefs/V1_chap08.html).
    pub fn from_posix_tz(tz_string: &str) -> Result<Self> {
        if tz_string.is_empty() {
            return Err(TzError::TzStringError(TzStringError::InvalidTzString("empty TZ string")));
        }

        if tz_string == "localtime" {
            return tz_file::parse_tz_file(&fs::read("/etc/localtime")?);
        }

        let read = |mut file: File| -> io::Result<_> {
            let mut bytes = Vec::new();
            file.read_to_end(&mut bytes)?;
            Ok(bytes)
        };

        let mut chars = tz_string.chars();
        if chars.next() == Some(':') {
            return tz_file::parse_tz_file(&read(tz_file::get_tz_file(chars.as_str())?)?);
        }

        match tz_file::get_tz_file(tz_string) {
            Ok(file) => tz_file::parse_tz_file(&read(file)?),
            Err(_) => {
                let tz_string = tz_string.trim_matches(|c: char| c.is_ascii_whitespace());

                // TZ string extensions are not allowed
                let rule = tz_string::parse_posix_tz(tz_string.as_bytes(), false)?;

                let local_time_types = match &rule {
                    TransitionRule::Fixed(local_time_type) => vec![local_time_type.clone()],
                    TransitionRule::Alternate { std, dst, .. } => vec![std.clone(), dst.clone()],
                };
                Ok(TimeZone { transitions: Vec::new(), local_time_types, leap_seconds: Vec::new(), extra_rule: Some(rule) })
            }
        }
    }

    /// Find the local time type associated to the time zone at the specified Unix time in seconds
    pub fn find_local_time_type(&self, unix_time: i64) -> Result<&LocalTimeType> {
        match self.transitions.last() {
            None => match &self.extra_rule {
                Some(extra_rule) => extra_rule.find_local_time_type(unix_time),
                None => Ok(&self.local_time_types[0]),
            },
            Some(last_transition) => {
                let unix_leap_time = self.unix_time_to_unix_leap_time(unix_time);

                if unix_leap_time >= last_transition.unix_leap_time {
                    match &self.extra_rule {
                        Some(extra_rule) => extra_rule.find_local_time_type(unix_time),
                        None => Err(TzError::NoLocalTimeType),
                    }
                } else {
                    let index = self.transitions.partition_point(|x| x.unix_leap_time <= unix_leap_time);
                    let local_time_type_index = if index > 0 { self.transitions[index - 1].local_time_type_index } else { 0 };
                    Ok(&self.local_time_types[local_time_type_index])
                }
            }
        }
    }

    /// Find the current local time type associated to the time zone
    pub fn find_current_local_time_type(&self) -> Result<&LocalTimeType> {
        self.find_local_time_type(SystemTime::now().duration_since(SystemTime::UNIX_EPOCH)?.as_secs().try_into()?)
    }

    /// Convert Unix time to Unix leap time, from the list of leap seconds in the time zone
    fn unix_time_to_unix_leap_time(&self, unix_time: i64) -> i64 {
        let mut unix_leap_time = unix_time;

        for leap_second in &self.leap_seconds {
            if unix_leap_time < leap_second.unix_leap_time {
                break;
            }
            unix_leap_time = unix_time + leap_second.correction as i64;
        }

        unix_leap_time
    }

    /// Convert Unix leap time to Unix time, from the list of leap seconds in the time zone
    fn unix_leap_time_to_unix_time(&self, unix_leap_time: i64) -> i64 {
        let index = self.leap_seconds.partition_point(|x| x.unix_leap_time < unix_leap_time);
        let correction = if index > 0 { self.leap_seconds[index - 1].correction } else { 0 };

        unix_leap_time - correction as i64
    }
}

/// UTC date time exprimed in the [proleptic gregorian calendar](https://en.wikipedia.org/wiki/Proleptic_Gregorian_calendar)
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct UtcDateTime {
    /// Seconds in `[0, 60]`, with a possible leap second
    second: u8,
    /// Minutes in `[0, 59]`
    minute: u8,
    /// Hours since midnight in `[0, 23]`
    hour: u8,
    /// Day of the month in `[1, 31]`
    month_day: u8,
    /// Month in `[0, 11]`
    month: u8,
    /// Years since 1900
    year: i32,
}

impl Ord for UtcDateTime {
    fn cmp(&self, other: &Self) -> Ordering {
        let self_tuple = (self.year, self.month, self.month_day, self.hour, self.second, self.minute);
        let other_tuple = (other.year, other.month, other.month_day, other.hour, other.second, other.minute);
        self_tuple.cmp(&other_tuple)
    }
}

impl PartialOrd for UtcDateTime {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl UtcDateTime {
    /// Returns seconds in `[0, 60]`, with a possible leap second
    pub fn second(&self) -> u8 {
        self.second
    }

    /// Returns minutes in `[0, 59]`
    pub fn minute(&self) -> u8 {
        self.minute
    }

    /// Returns hours since midnight in `[0, 23]`
    pub fn hour(&self) -> u8 {
        self.hour
    }

    /// Returns day of the month in `[1, 31]`
    pub fn month_day(&self) -> u8 {
        self.month_day
    }

    /// Returns month in `[0, 11]`
    pub fn month(&self) -> u8 {
        self.month
    }

    /// Returns years since 1900
    pub fn year(&self) -> i32 {
        self.year
    }

    /// Returns year
    pub fn full_year(&self) -> i32 {
        self.year + 1900
    }

    /// Returns days since Sunday in `[0, 6]`
    pub fn week_day(&self) -> u8 {
        let days_since_unix_epoch = days_since_unix_epoch(self.year, self.month.into(), self.month_day.into());
        (4 + days_since_unix_epoch).rem_euclid(constants::DAYS_PER_WEEK) as u8
    }

    /// Returns days since January 1 in `[0, 365]`
    pub fn year_day(&self) -> u16 {
        let leap = (self.month >= 2 && is_leap_year(self.year)) as i64;
        (constants::CUM_DAY_IN_MONTHS_NORMAL_YEAR[self.month as usize] + leap + self.month_day as i64 - 1) as u16
    }

    /// Returns the Unix time in seconds associated to the UTC date time
    pub fn unix_time(&self) -> i64 {
        use constants::*;

        let mut result = days_since_unix_epoch(self.year, self.month.into(), self.month_day.into());
        result *= HOURS_PER_DAY;
        result += self.hour as i64;
        result *= MINUTES_PER_HOUR;
        result += self.minute as i64;
        result *= SECONDS_PER_MINUTE;
        result += self.second as i64;

        result
    }

    /// Construct a UTC date time
    ///
    /// ## Inputs
    ///
    /// * `full_year`: Year
    /// * `month`: Month in `[0, 11]`
    /// * `month_day`: Day of the month in `[1, 31]`
    /// * `hour`: Hours since midnight in `[0, 23]`
    /// * `minute`: Minutes in `[0, 59]`
    /// * `second`: Seconds in `[0, 60]`, with a possible leap second
    ///
    pub fn new(full_year: i32, month: u8, month_day: u8, hour: u8, minute: u8, second: u8) -> Result<Self> {
        use constants::*;

        let year = full_year - 1900;

        if !(0..=11).contains(&month) {
            return Err(TzError::DateTimeInputError("invalid month"));
        }
        if !(1..=31).contains(&month_day) {
            return Err(TzError::DateTimeInputError("invalid month day"));
        }
        if !(0..=23).contains(&hour) {
            return Err(TzError::DateTimeInputError("invalid hour"));
        }
        if !(0..=59).contains(&minute) {
            return Err(TzError::DateTimeInputError("invalid minute"));
        }
        if !(0..=60).contains(&second) {
            return Err(TzError::DateTimeInputError("invalid second"));
        }

        let leap = is_leap_year(year) as i64;

        let mut day_in_month = DAY_IN_MONTHS_NORMAL_YEAR[month as usize];
        if month == 1 {
            day_in_month += leap;
        }

        if month_day as i64 > day_in_month {
            return Err(TzError::DateTimeInputError("invalid month day"));
        }

        Ok(Self { second, minute, hour, month_day, month, year })
    }

    /// Construct a UTC date time from a Unix time in seconds
    pub fn from_unix_time(unix_time: i64) -> Result<Self> {
        use constants::*;

        let seconds = unix_time - UNIX_OFFSET_SECS;
        let mut remaining_days = seconds / SECONDS_PER_DAY;
        let mut remaining_seconds = seconds % SECONDS_PER_DAY;
        if remaining_seconds < 0 {
            remaining_seconds += SECONDS_PER_DAY;
            remaining_days -= 1;
        }

        let mut cycles_400_years = remaining_days / DAYS_PER_400_YEARS;
        remaining_days %= DAYS_PER_400_YEARS;
        if remaining_days < 0 {
            remaining_days += DAYS_PER_400_YEARS;
            cycles_400_years -= 1;
        }

        let cycles_100_years = (remaining_days / DAYS_PER_100_YEARS).min(3);
        remaining_days -= cycles_100_years * DAYS_PER_100_YEARS;

        let cycles_4_years = (remaining_days / DAYS_PER_4_YEARS).min(24);
        remaining_days -= cycles_4_years * DAYS_PER_4_YEARS;

        let remaining_years = (remaining_days / DAYS_PER_NORMAL_YEAR).min(3);
        remaining_days -= remaining_years * DAYS_PER_NORMAL_YEAR;

        let mut year = OFFSET_YEARS + remaining_years + cycles_4_years * 4 + cycles_100_years * 100 + cycles_400_years * 400;

        let mut month = 2;
        for days in DAY_IN_MONTHS_LEAP_YEAR_FROM_MARCH {
            if remaining_days < days {
                break;
            }
            remaining_days -= days;
            month += 1;
        }

        if month >= MONTHS_PER_YEAR {
            month -= MONTHS_PER_YEAR;
            year += 1;
        }

        let month_day = 1 + remaining_days;

        let hour = remaining_seconds / SECONDS_PER_HOUR;
        let minute = (remaining_seconds / SECONDS_PER_MINUTE) % MINUTES_PER_HOUR;
        let second = remaining_seconds % SECONDS_PER_MINUTE;

        Ok(Self {
            second: second.try_into()?,
            minute: minute.try_into()?,
            hour: hour.try_into()?,
            month_day: month_day.try_into()?,
            month: month.try_into()?,
            year: year.try_into()?,
        })
    }

    /// Returns the current UTC date time
    pub fn now() -> Result<Self> {
        Self::from_unix_time(SystemTime::now().duration_since(SystemTime::UNIX_EPOCH)?.as_secs().try_into()?)
    }

    /// Project the UTC date time into a time zone.
    ///
    /// Leap seconds are not preserved.
    ///
    pub fn project(&self, time_zone: &TimeZone) -> Result<DateTime> {
        let unix_time = self.unix_time();
        let local_time_type = time_zone.find_local_time_type(unix_time)?;

        let utc_date_time_with_offset = UtcDateTime::from_unix_time(unix_time + local_time_type.ut_offset() as i64)?;

        Ok(DateTime {
            second: utc_date_time_with_offset.second,
            minute: utc_date_time_with_offset.minute,
            hour: utc_date_time_with_offset.hour,
            month_day: utc_date_time_with_offset.month_day,
            month: utc_date_time_with_offset.month,
            year: utc_date_time_with_offset.year,
            week_day: utc_date_time_with_offset.week_day(),
            year_day: utc_date_time_with_offset.year_day(),
            local_time_type: local_time_type.clone(),
            unix_time,
        })
    }
}

/// Date time associated to a local time type, exprimed in the [proleptic gregorian calendar](https://en.wikipedia.org/wiki/Proleptic_Gregorian_calendar)
#[derive(Debug, Clone)]
pub struct DateTime {
    /// Seconds in `[0, 60]`, with a possible leap second
    second: u8,
    /// Minutes in `[0, 59]`
    minute: u8,
    /// Hours since midnight in `[0, 23]`
    hour: u8,
    /// Day of the month in `[1, 31]`
    month_day: u8,
    /// Month in `[0, 11]`
    month: u8,
    /// Years since 1900
    year: i32,
    /// Days since Sunday in `[0, 6]`
    week_day: u8,
    /// Days since January 1 in `[0, 365]`
    year_day: u16,
    /// Local time type
    local_time_type: LocalTimeType,
    /// UTC Unix time in seconds
    unix_time: i64,
}

impl PartialEq for DateTime {
    fn eq(&self, other: &Self) -> bool {
        self.unix_time == other.unix_time
    }
}

impl PartialOrd for DateTime {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.unix_time.partial_cmp(&other.unix_time)
    }
}

impl DateTime {
    /// Returns seconds in `[0, 60]`, with a possible leap second
    pub fn second(&self) -> u8 {
        self.second
    }

    /// Returns minutes in `[0, 59]`
    pub fn minute(&self) -> u8 {
        self.minute
    }

    /// Returns hours since midnight in `[0, 23]`
    pub fn hour(&self) -> u8 {
        self.hour
    }

    /// Returns day of the month in `[1, 31]`
    pub fn month_day(&self) -> u8 {
        self.month_day
    }

    /// Returns month in `[0, 11]`
    pub fn month(&self) -> u8 {
        self.month
    }

    /// Returns years since 1900
    pub fn year(&self) -> i32 {
        self.year
    }

    /// Returns year
    pub fn full_year(&self) -> i32 {
        self.year + 1900
    }

    /// Returns days since Sunday in `[0, 6]`
    pub fn week_day(&self) -> u8 {
        self.week_day
    }

    /// Returns days since January 1 in `[0, 365]`
    pub fn year_day(&self) -> u16 {
        self.year_day
    }

    /// Returns local time type
    pub fn local_time_type(&self) -> &LocalTimeType {
        &self.local_time_type
    }

    /// Returns UTC Unix time in seconds
    pub fn unix_time(&self) -> i64 {
        self.unix_time
    }

    /// Project the date time into another time zone.
    ///
    /// Leap seconds are not preserved.
    ///
    pub fn project(&self, time_zone: &TimeZone) -> Result<Self> {
        let local_time_type = time_zone.find_local_time_type(self.unix_time)?;

        let utc_date_time_with_offset = UtcDateTime::from_unix_time(self.unix_time + local_time_type.ut_offset() as i64)?;

        Ok(DateTime {
            second: utc_date_time_with_offset.second,
            minute: utc_date_time_with_offset.minute,
            hour: utc_date_time_with_offset.hour,
            month_day: utc_date_time_with_offset.month_day,
            month: utc_date_time_with_offset.month,
            year: utc_date_time_with_offset.year,
            week_day: utc_date_time_with_offset.week_day(),
            year_day: utc_date_time_with_offset.year_day(),
            local_time_type: local_time_type.clone(),
            unix_time: self.unix_time,
        })
    }

    /// Returns the current date time associated to the specified time zone
    pub fn now(time_zone: &TimeZone) -> Result<Self> {
        let unix_time = SystemTime::now().duration_since(SystemTime::UNIX_EPOCH)?.as_secs().try_into()?;
        let local_time_type = time_zone.find_local_time_type(unix_time)?;

        let utc_date_time_with_offset = UtcDateTime::from_unix_time(unix_time + local_time_type.ut_offset() as i64)?;

        Ok(DateTime {
            second: utc_date_time_with_offset.second,
            minute: utc_date_time_with_offset.minute,
            hour: utc_date_time_with_offset.hour,
            month_day: utc_date_time_with_offset.month_day,
            month: utc_date_time_with_offset.month,
            year: utc_date_time_with_offset.year,
            week_day: utc_date_time_with_offset.week_day(),
            year_day: utc_date_time_with_offset.year_day(),
            local_time_type: local_time_type.clone(),
            unix_time,
        })
    }
}

/// Check if a year is a leap year.
///
/// ## Inputs
///
/// * `year`: Years since 1900
///
fn is_leap_year(year: i32) -> bool {
    let full_year = 1900 + year;
    full_year % 400 == 0 || (full_year % 4 == 0 && full_year % 100 != 0)
}

/// Compute the number of days since Unix epoch (`1970-01-01T00:00:00Z`).
///
/// ## Inputs
///
/// * `year`: Years since 1900
/// * `month`: Month in `[0, 11]`
/// * `month_day`: Day of the month in `[1, 31]`
///
fn days_since_unix_epoch(year: i32, month: usize, month_day: i64) -> i64 {
    use constants::*;

    let is_leap_year = is_leap_year(year);

    let full_year = 1900 + year as i64;

    let mut result = (full_year - 1970) * 365;

    if full_year >= 1970 {
        result += (full_year - 1968) / 4;
        result -= (full_year - 1900) / 100;
        result += (full_year - 1600) / 400;

        if is_leap_year && month < 2 {
            result -= 1;
        }
    } else {
        result += (full_year - 1972) / 4;
        result -= (full_year - 2000) / 100;
        result += (full_year - 2000) / 400;

        if is_leap_year && month >= 2 {
            result += 1;
        }
    }

    result += CUM_DAY_IN_MONTHS_NORMAL_YEAR[month as usize] + month_day - 1;

    result
}

#[cfg(test)]
mod test {
    use super::*;

    fn check_equal_date_time(x: &DateTime, y: &DateTime) {
        assert_eq!(x.second, y.second);
        assert_eq!(x.minute, y.minute);
        assert_eq!(x.hour, y.hour);
        assert_eq!(x.month_day, y.month_day);
        assert_eq!(x.month, y.month);
        assert_eq!(x.year, y.year);
        assert_eq!(x.week_day, y.week_day);
        assert_eq!(x.year_day, y.year_day);
        assert_eq!(x.local_time_type, y.local_time_type);
        assert_eq!(x.unix_time, y.unix_time);
    }

    #[test]
    fn test_rule_day() -> Result<()> {
        let rule_day_j1 = RuleDay::Julian1WithoutLeap(60);
        assert_eq!(rule_day_j1.transition_date(100), (2, 1));
        assert_eq!(rule_day_j1.transition_date(101), (2, 1));
        assert_eq!(rule_day_j1.unix_time(100, 43200), 951912000);

        let rule_day_j0 = RuleDay::Julian0WithLeap(59);
        assert_eq!(rule_day_j0.transition_date(100), (1, 29));
        assert_eq!(rule_day_j0.transition_date(101), (2, 1));
        assert_eq!(rule_day_j0.unix_time(100, 43200), 951825600);

        let rule_day_mwd = RuleDay::MonthWeekDay { month: 2, week: 5, week_day: 2 };
        assert_eq!(rule_day_mwd.transition_date(100), (1, 29));
        assert_eq!(rule_day_mwd.transition_date(101), (1, 27));
        assert_eq!(rule_day_mwd.unix_time(100, 43200), 951825600);
        assert_eq!(rule_day_mwd.unix_time(101, 43200), 983275200);

        Ok(())
    }

    #[test]
    fn test_transition_rule() -> Result<()> {
        let transition_rule_fixed = TransitionRule::Fixed(LocalTimeType::with_ut_offset(0));
        assert_eq!(*transition_rule_fixed.find_local_time_type(0)?, LocalTimeType::utc());

        let transition_rule_neg = TransitionRule::Alternate {
            std: LocalTimeType { ut_offset: 0, is_dst: false, time_zone_designation: None },
            dst: LocalTimeType { ut_offset: 0, is_dst: true, time_zone_designation: None },
            dst_start: RuleDay::Julian0WithLeap(100),
            dst_start_time: 0,
            dst_end: RuleDay::Julian0WithLeap(101),
            dst_end_time: -86500,
        };

        assert!(transition_rule_neg.find_local_time_type(8639899)?.is_dst());
        assert!(!transition_rule_neg.find_local_time_type(8639900)?.is_dst());
        assert!(!transition_rule_neg.find_local_time_type(8639999)?.is_dst());
        assert!(transition_rule_neg.find_local_time_type(8640000)?.is_dst());

        Ok(())
    }

    #[test]
    fn test_time_zone() -> Result<()> {
        let time_zone_1 = TimeZone { transitions: Vec::new(), local_time_types: vec![LocalTimeType::utc()], leap_seconds: Vec::new(), extra_rule: None };
        assert_eq!(*time_zone_1.find_local_time_type(0)?, LocalTimeType::utc());

        let time_zone_2 = TimeZone {
            transitions: Vec::new(),
            local_time_types: vec![LocalTimeType::utc()],
            leap_seconds: Vec::new(),
            extra_rule: Some(TransitionRule::Fixed(LocalTimeType::with_ut_offset(3600))),
        };

        assert_eq!(*time_zone_2.find_local_time_type(0)?, LocalTimeType::with_ut_offset(3600));

        let time_zone_3 = TimeZone {
            transitions: vec![Transition { unix_leap_time: 0, local_time_type_index: 0 }],
            local_time_types: vec![LocalTimeType::utc()],
            leap_seconds: Vec::new(),
            extra_rule: None,
        };

        assert_eq!(*time_zone_3.find_local_time_type(-1)?, LocalTimeType::utc());
        assert!(matches!(time_zone_3.find_local_time_type(0), Err(TzError::NoLocalTimeType)));

        let time_zone_4 = TimeZone {
            transitions: vec![Transition { unix_leap_time: 0, local_time_type_index: 0 }],
            local_time_types: vec![LocalTimeType::utc()],
            leap_seconds: Vec::new(),
            extra_rule: Some(TransitionRule::Fixed(LocalTimeType::with_ut_offset(3600))),
        };

        assert_eq!(*time_zone_4.find_local_time_type(-1)?, LocalTimeType::utc());
        assert_eq!(*time_zone_4.find_local_time_type(0)?, LocalTimeType::with_ut_offset(3600));

        Ok(())
    }

    #[test]
    fn test_time_zone_from_posix_tz() -> Result<()> {
        #[cfg(unix)]
        {
            let time_zone_local = TimeZone::local()?;
            let time_zone_local_1 = TimeZone::from_posix_tz("localtime")?;
            let time_zone_local_2 = TimeZone::from_posix_tz("/etc/localtime")?;
            let time_zone_local_3 = TimeZone::from_posix_tz(":/etc/localtime")?;

            assert_eq!(time_zone_local, time_zone_local_1);
            assert_eq!(time_zone_local, time_zone_local_2);
            assert_eq!(time_zone_local, time_zone_local_3);

            assert!(matches!(time_zone_local.find_current_local_time_type(), Ok(_) | Err(TzError::NoLocalTimeType)));

            let time_zone_utc = TimeZone::from_posix_tz("UTC")?;
            assert_eq!(time_zone_utc.find_local_time_type(0)?.ut_offset(), 0);
        }

        assert!(TimeZone::from_posix_tz("EST5EDT,0/0,J365/25").is_err());
        assert!(TimeZone::from_posix_tz("").is_err());

        Ok(())
    }

    #[test]
    fn test_date_time() -> Result<()> {
        let time_zone_utc = TimeZone::utc();
        let utc = LocalTimeType::utc();

        let time_zone_cet = TimeZone::fixed(3600);
        let cet = LocalTimeType::with_ut_offset(3600);

        let time_zone_eet = TimeZone::fixed(7200);
        let eet = LocalTimeType::with_ut_offset(7200);

        assert_eq!(DateTime::now(&time_zone_utc)?.local_time_type().ut_offset(), 0);
        assert_eq!(DateTime::now(&time_zone_cet)?.local_time_type().ut_offset(), 3600);
        assert_eq!(DateTime::now(&time_zone_eet)?.local_time_type().ut_offset(), 7200);

        let unix_times = [-93750523200, -11670955200, -8515195200, -8483659200, -8389051200, 951825600, 983448000, 1078056000, 4107585600, 32540356800];

        #[rustfmt::skip]
        let date_times_utc = [
            DateTime { second: 0, minute: 0, hour: 12, month_day: 1,  month: 2, year: -2901, week_day: 5, year_day: 59, local_time_type: utc.clone(), unix_time: -93750523200 },
            DateTime { second: 0, minute: 0, hour: 12, month_day: 29, month: 1, year: -300,  week_day: 2, year_day: 59, local_time_type: utc.clone(), unix_time: -11670955200 },
            DateTime { second: 0, minute: 0, hour: 12, month_day: 1,  month: 2, year: -200,  week_day: 1, year_day: 59, local_time_type: utc.clone(), unix_time: -8515195200 },
            DateTime { second: 0, minute: 0, hour: 12, month_day: 1,  month: 2, year: -199,  week_day: 2, year_day: 59, local_time_type: utc.clone(), unix_time: -8483659200 },
            DateTime { second: 0, minute: 0, hour: 12, month_day: 29, month: 1, year: -196,  week_day: 5, year_day: 59, local_time_type: utc.clone(), unix_time: -8389051200 },
            DateTime { second: 0, minute: 0, hour: 12, month_day: 29, month: 1, year: 100,   week_day: 2, year_day: 59, local_time_type: utc.clone(), unix_time: 951825600 },
            DateTime { second: 0, minute: 0, hour: 12, month_day: 1,  month: 2, year: 101,   week_day: 4, year_day: 59, local_time_type: utc.clone(), unix_time: 983448000 },
            DateTime { second: 0, minute: 0, hour: 12, month_day: 29, month: 1, year: 104,   week_day: 0, year_day: 59, local_time_type: utc.clone(), unix_time: 1078056000 },
            DateTime { second: 0, minute: 0, hour: 12, month_day: 1,  month: 2, year: 200,   week_day: 1, year_day: 59, local_time_type: utc.clone(), unix_time: 4107585600 },
            DateTime { second: 0, minute: 0, hour: 12, month_day: 1,  month: 2, year: 1101,  week_day: 0, year_day: 59, local_time_type: utc,         unix_time: 32540356800 },
        ];

        #[rustfmt::skip]
        let date_times_cet = [
            DateTime { second: 0, minute: 0, hour: 13, month_day: 1,  month: 2, year: -2901, week_day: 5, year_day: 59, local_time_type: cet.clone(), unix_time: -93750523200 },
            DateTime { second: 0, minute: 0, hour: 13, month_day: 29, month: 1, year: -300,  week_day: 2, year_day: 59, local_time_type: cet.clone(), unix_time: -11670955200 },
            DateTime { second: 0, minute: 0, hour: 13, month_day: 1,  month: 2, year: -200,  week_day: 1, year_day: 59, local_time_type: cet.clone(), unix_time: -8515195200 },
            DateTime { second: 0, minute: 0, hour: 13, month_day: 1,  month: 2, year: -199,  week_day: 2, year_day: 59, local_time_type: cet.clone(), unix_time: -8483659200 },
            DateTime { second: 0, minute: 0, hour: 13, month_day: 29, month: 1, year: -196,  week_day: 5, year_day: 59, local_time_type: cet.clone(), unix_time: -8389051200 },
            DateTime { second: 0, minute: 0, hour: 13, month_day: 29, month: 1, year: 100,   week_day: 2, year_day: 59, local_time_type: cet.clone(), unix_time: 951825600 },
            DateTime { second: 0, minute: 0, hour: 13, month_day: 1,  month: 2, year: 101,   week_day: 4, year_day: 59, local_time_type: cet.clone(), unix_time: 983448000 },
            DateTime { second: 0, minute: 0, hour: 13, month_day: 29, month: 1, year: 104,   week_day: 0, year_day: 59, local_time_type: cet.clone(), unix_time: 1078056000 },
            DateTime { second: 0, minute: 0, hour: 13, month_day: 1,  month: 2, year: 200,   week_day: 1, year_day: 59, local_time_type: cet.clone(), unix_time: 4107585600 },
            DateTime { second: 0, minute: 0, hour: 13, month_day: 1,  month: 2, year: 1101,  week_day: 0, year_day: 59, local_time_type: cet,         unix_time: 32540356800 },
        ];

        #[rustfmt::skip]
        let date_times_eet = [
            DateTime { second: 0, minute: 0, hour: 14, month_day: 1,  month: 2, year: -2901, week_day: 5, year_day: 59, local_time_type: eet.clone(), unix_time: -93750523200 },
            DateTime { second: 0, minute: 0, hour: 14, month_day: 29, month: 1, year: -300,  week_day: 2, year_day: 59, local_time_type: eet.clone(), unix_time: -11670955200 },
            DateTime { second: 0, minute: 0, hour: 14, month_day: 1,  month: 2, year: -200,  week_day: 1, year_day: 59, local_time_type: eet.clone(), unix_time: -8515195200 },
            DateTime { second: 0, minute: 0, hour: 14, month_day: 1,  month: 2, year: -199,  week_day: 2, year_day: 59, local_time_type: eet.clone(), unix_time: -8483659200 },
            DateTime { second: 0, minute: 0, hour: 14, month_day: 29, month: 1, year: -196,  week_day: 5, year_day: 59, local_time_type: eet.clone(), unix_time: -8389051200 },
            DateTime { second: 0, minute: 0, hour: 14, month_day: 29, month: 1, year: 100,   week_day: 2, year_day: 59, local_time_type: eet.clone(), unix_time: 951825600 },
            DateTime { second: 0, minute: 0, hour: 14, month_day: 1,  month: 2, year: 101,   week_day: 4, year_day: 59, local_time_type: eet.clone(), unix_time: 983448000 },
            DateTime { second: 0, minute: 0, hour: 14, month_day: 29, month: 1, year: 104,   week_day: 0, year_day: 59, local_time_type: eet.clone(), unix_time: 1078056000 },
            DateTime { second: 0, minute: 0, hour: 14, month_day: 1,  month: 2, year: 200,   week_day: 1, year_day: 59, local_time_type: eet.clone(), unix_time: 4107585600 },
            DateTime { second: 0, minute: 0, hour: 14, month_day: 1,  month: 2, year: 1101,  week_day: 0, year_day: 59, local_time_type: eet,         unix_time: 32540356800 },
        ];

        for (((unix_time, date_time_utc), date_time_cet), date_time_eet) in unix_times.into_iter().zip(date_times_utc).zip(date_times_cet).zip(date_times_eet) {
            let utc_date_time = UtcDateTime::from_unix_time(unix_time)?;

            assert_eq!(utc_date_time.second(), date_time_utc.second());
            assert_eq!(utc_date_time.minute(), date_time_utc.minute());
            assert_eq!(utc_date_time.hour(), date_time_utc.hour());
            assert_eq!(utc_date_time.month_day(), date_time_utc.month_day());
            assert_eq!(utc_date_time.month(), date_time_utc.month());
            assert_eq!(utc_date_time.year(), date_time_utc.year());
            assert_eq!(utc_date_time.full_year(), date_time_utc.full_year());

            assert_eq!(utc_date_time.unix_time(), unix_time);
            assert_eq!(date_time_utc.unix_time(), unix_time);
            assert_eq!(date_time_cet.unix_time(), unix_time);
            assert_eq!(date_time_eet.unix_time(), unix_time);

            assert_eq!(date_time_utc, date_time_cet);
            assert_eq!(date_time_utc, date_time_eet);

            check_equal_date_time(&utc_date_time.project(&time_zone_utc)?, &date_time_utc);
            check_equal_date_time(&utc_date_time.project(&time_zone_cet)?, &date_time_cet);
            check_equal_date_time(&utc_date_time.project(&time_zone_eet)?, &date_time_eet);

            check_equal_date_time(&date_time_utc.project(&time_zone_utc)?, &date_time_utc);
            check_equal_date_time(&date_time_cet.project(&time_zone_utc)?, &date_time_utc);
            check_equal_date_time(&date_time_eet.project(&time_zone_utc)?, &date_time_utc);

            check_equal_date_time(&date_time_utc.project(&time_zone_cet)?, &date_time_cet);
            check_equal_date_time(&date_time_cet.project(&time_zone_cet)?, &date_time_cet);
            check_equal_date_time(&date_time_eet.project(&time_zone_cet)?, &date_time_cet);

            check_equal_date_time(&date_time_utc.project(&time_zone_eet)?, &date_time_eet);
            check_equal_date_time(&date_time_cet.project(&time_zone_eet)?, &date_time_eet);
            check_equal_date_time(&date_time_eet.project(&time_zone_eet)?, &date_time_eet);
        }

        Ok(())
    }

    #[test]
    fn test_date_time_leap_seconds() -> Result<()> {
        let utc_date_time = UtcDateTime::new(1972, 5, 30, 23, 59, 60)?;
        let date_time = utc_date_time.project(&TimeZone::fixed(-3600))?;

        let date_time_result = DateTime {
            second: 00,
            minute: 00,
            hour: 23,
            month_day: 30,
            month: 5,
            year: 72,
            week_day: 5,
            year_day: 181,
            local_time_type: LocalTimeType::with_ut_offset(-3600),
            unix_time: 78796800,
        };

        check_equal_date_time(&date_time, &date_time_result);

        Ok(())
    }

    #[test]
    fn test_date_time_partial_eq_partial_ord() -> Result<()> {
        let time_zone_utc = TimeZone::utc();
        let time_zone_cet = TimeZone::fixed(3600);
        let time_zone_eet = TimeZone::fixed(7200);

        let utc_date_time_1 = UtcDateTime::from_unix_time(1)?;
        let utc_date_time_2 = UtcDateTime::from_unix_time(2)?;
        let utc_date_time_3 = UtcDateTime::from_unix_time(3)?;

        let date_time_utc_1 = utc_date_time_1.project(&time_zone_utc)?;
        let date_time_utc_2 = utc_date_time_2.project(&time_zone_utc)?;
        let date_time_utc_3 = utc_date_time_3.project(&time_zone_utc)?;

        let date_time_cet_1 = utc_date_time_1.project(&time_zone_cet)?;
        let date_time_cet_2 = utc_date_time_2.project(&time_zone_cet)?;
        let date_time_cet_3 = utc_date_time_3.project(&time_zone_cet)?;

        let date_time_eet_1 = utc_date_time_1.project(&time_zone_eet)?;
        let date_time_eet_2 = utc_date_time_2.project(&time_zone_eet)?;
        let date_time_eet_3 = utc_date_time_3.project(&time_zone_eet)?;

        assert_eq!(date_time_utc_1, date_time_cet_1);
        assert_eq!(date_time_utc_1, date_time_eet_1);

        assert_eq!(date_time_utc_2, date_time_cet_2);
        assert_eq!(date_time_utc_2, date_time_eet_2);

        assert_eq!(date_time_utc_3, date_time_cet_3);
        assert_eq!(date_time_utc_3, date_time_eet_3);

        assert_ne!(date_time_utc_1, date_time_utc_2);
        assert_ne!(date_time_utc_1, date_time_utc_3);

        assert_eq!(date_time_utc_1.partial_cmp(&date_time_cet_1), Some(Ordering::Equal));
        assert_eq!(date_time_utc_1.partial_cmp(&date_time_eet_1), Some(Ordering::Equal));

        assert_eq!(date_time_utc_2.partial_cmp(&date_time_cet_2), Some(Ordering::Equal));
        assert_eq!(date_time_utc_2.partial_cmp(&date_time_eet_2), Some(Ordering::Equal));

        assert_eq!(date_time_utc_3.partial_cmp(&date_time_cet_3), Some(Ordering::Equal));
        assert_eq!(date_time_utc_3.partial_cmp(&date_time_eet_3), Some(Ordering::Equal));

        assert_eq!(date_time_utc_1.partial_cmp(&date_time_utc_2), Some(Ordering::Less));
        assert_eq!(date_time_utc_2.partial_cmp(&date_time_utc_3), Some(Ordering::Less));

        Ok(())
    }

    #[test]
    fn test_date_time_sync_and_send() {
        trait AssertSyncSendStatic: Sync + Send + 'static {}
        impl AssertSyncSendStatic for DateTime {}
    }

    #[test]
    fn test_utc_date_time_ord() -> Result<()> {
        let utc_date_time_1 = UtcDateTime::new(1972, 5, 30, 23, 59, 59)?;
        let utc_date_time_2 = UtcDateTime::new(1972, 5, 30, 23, 59, 60)?;
        let utc_date_time_3 = UtcDateTime::new(1972, 6, 1, 0, 0, 0)?;

        assert_eq!(utc_date_time_1.cmp(&utc_date_time_1), Ordering::Equal);
        assert_eq!(utc_date_time_1.cmp(&utc_date_time_2), Ordering::Less);
        assert_eq!(utc_date_time_1.cmp(&utc_date_time_3), Ordering::Less);

        assert_eq!(utc_date_time_2.cmp(&utc_date_time_1), Ordering::Greater);
        assert_eq!(utc_date_time_2.cmp(&utc_date_time_2), Ordering::Equal);
        assert_eq!(utc_date_time_2.cmp(&utc_date_time_3), Ordering::Less);

        assert_eq!(utc_date_time_3.cmp(&utc_date_time_1), Ordering::Greater);
        assert_eq!(utc_date_time_3.cmp(&utc_date_time_2), Ordering::Greater);
        assert_eq!(utc_date_time_3.cmp(&utc_date_time_3), Ordering::Equal);

        Ok(())
    }

    #[test]
    fn test_is_leap_year() {
        assert!(is_leap_year(100));
        assert!(!is_leap_year(101));
        assert!(is_leap_year(104));
        assert!(!is_leap_year(200));
        assert!(!is_leap_year(300));
        assert!(!is_leap_year(400));
        assert!(is_leap_year(500));
    }

    #[test]
    fn test_days_since_unix_epoch() {
        assert_eq!(days_since_unix_epoch(-2901, 2, 1), -1085076);
        assert_eq!(days_since_unix_epoch(-300, 1, 29), -135081);
        assert_eq!(days_since_unix_epoch(-300, 2, 1), -135080);
        assert_eq!(days_since_unix_epoch(-200, 2, 1), -98556);
        assert_eq!(days_since_unix_epoch(-199, 2, 1), -98191);
        assert_eq!(days_since_unix_epoch(-196, 1, 29), -97096);
        assert_eq!(days_since_unix_epoch(100, 1, 29), 11016);
        assert_eq!(days_since_unix_epoch(100, 2, 1), 11017);
        assert_eq!(days_since_unix_epoch(101, 2, 1), 11382);
        assert_eq!(days_since_unix_epoch(104, 1, 29), 12477);
        assert_eq!(days_since_unix_epoch(200, 2, 1), 47541);
        assert_eq!(days_since_unix_epoch(1101, 2, 1), 376624);
    }
}
