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
//! ## Construct a time zone object
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
//! # Ok(())
//! # }
//! ```
//! ```rust,ignore
//!     // Get local time zone (UNIX only)
//!     let time_zone_local = TimeZone::local()?;
//!     // Get the current local time type
//!     let _current_local_time_type = time_zone_local.find_current_local_time_type()?;
//! ```
//! ```rust
//! # fn main() -> Result<(), tz::TzError> {
//! # use tz::TimeZone;
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
//! ## Construct a date time object
//!
//! ```rust
//! # fn main() -> Result<(), tz::TzError> {
//!     use tz::{DateTime, TimeZone, UtcDateTime};
//!
//!     // Create a new UTC date time
//!     // 2000-01-01T00:00:00Z
//!     let utc_date_time = UtcDateTime::new(2000, 0, 1, 0, 0, 0)?;
//!     let date_time = utc_date_time.to_date_time();
//!     assert_eq!(date_time.second(), 0);
//!     assert_eq!(date_time.minute(), 0);
//!     assert_eq!(date_time.hour(), 0);
//!     assert_eq!(date_time.month_day(), 1);
//!     assert_eq!(date_time.month(), 0);
//!     assert_eq!(date_time.year(), 100);
//!     assert_eq!(date_time.full_year(), 2000);
//!     assert_eq!(date_time.week_day(), 6);
//!     assert_eq!(date_time.year_day(), 0);
//!     assert_eq!(date_time.local_time_type().ut_offset(), 0);
//!
//!     // Create a date time from a time zone and an UTC date time
//!     let time_zone_fixed = TimeZone::fixed(-3600);
//!
//!     // 2000-01-01T00:00:00Z
//!     let utc_date_time = UtcDateTime::new(2000, 0, 1, 0, 0, 0)?;
//!     let date_time = DateTime::from_utc_date_time(&time_zone_fixed, utc_date_time)?;
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
//!
//!     // Create a date time from a time zone and an unix time
//!     // 2000-01-01T00:00:00Z
//!     let date_time = DateTime::from_unix_time(&time_zone_fixed, 946684800)?;
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
//!
//!     // Get the corresponding UTC unix time
//!     let unix_time = date_time.unix_time();
//!     assert_eq!(unix_time, 946684800);
//! # Ok(())
//! # }
//! ```
//! ```rust,ignore
//!     // Get the current date time at the local time zone (UNIX only)
//!     let time_zone_local = TimeZone::local()?;
//!     let _date_time = DateTime::now(&time_zone_local)?;
//! ```

mod constants;
mod cursor;
mod tz_file;
mod tz_string;

use std::cmp::Ordering;
use std::error;
use std::fmt;
use std::fs::{self, File};
use std::io::{self, Read};
use std::num::TryFromIntError;
use std::time::{SystemTime, SystemTimeError};

use tz_file::TzFileError;
use tz_string::TzStringError;

/// Alias for [`std::result::Result`] with the crate unified error
pub type Result<T> = std::result::Result<T, TzError>;

/// Unified error type for everything in the crate
#[non_exhaustive]
#[derive(Debug)]
pub enum TzError {
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
    time_zone_designation: String,
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
        &self.time_zone_designation
    }

    /// Construct the local time type associated to UTC
    pub fn utc() -> Self {
        Self::with_ut_offset(0)
    }

    /// Construct a local time type with the specified offset in seconds
    pub fn with_ut_offset(ut_offset: i32) -> Self {
        Self { ut_offset, is_dst: false, time_zone_designation: "".to_owned() }
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

    /// Returns the UTC unix time in seconds associated to the transition date for the provided year
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
    /// Find the local time type associated to the transition rule at the specified unix time in seconds
    fn find_local_time_type(&self, unix_time: i64) -> Result<&LocalTimeType> {
        match self {
            Self::Fixed(local_time_type) => Ok(local_time_type),
            Self::Alternate { std, dst, dst_start, dst_start_time, dst_end, dst_end_time } => {
                let dst_start_time_in_utc = (dst_start_time - std.ut_offset).into();
                let dst_end_time_in_utc = (dst_end_time - dst.ut_offset).into();

                let current_year = DateTime::from_unix_time(&TimeZone::utc(), unix_time)?.year();

                let current_year_dst_start_unix_time = dst_start.unix_time(current_year, dst_start_time_in_utc);
                let current_year_dst_end_unix_time = dst_end.unix_time(current_year, dst_end_time_in_utc);

                // Check DST start/end unix times for previous/current/next years to support for transition day times outside of [0h, 24h] range
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

    /// Returns local time zone
    #[cfg(unix)]
    pub fn local() -> Result<Self> {
        Self::from_posix_tz("localtime")
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

    /// Find the local time type associated to the time zone at the specified unix time in seconds
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

    /// Convert unix time to unix leap time, from the list of leap seconds in the time zone
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

    /// Convert unix leap time to unix time, from the list of leap seconds in the time zone
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
    /// Days since Sunday in `[0, 6]`
    week_day: u8,
    /// Days since January 1 in `[0, 365]`
    year_day: u16,
}

impl UtcDateTime {
    /// Construct an UTC date time
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

        let days_since_unix_epoch = days_since_unix_epoch(year, month.into(), month_day.into());

        let week_day = (4 + days_since_unix_epoch).rem_euclid(DAYS_PER_WEEK).try_into()?;

        let cum_day_in_months = [0, 31, 59 + leap, 90 + leap, 120 + leap, 151 + leap, 181 + leap, 212 + leap, 243 + leap, 273 + leap, 304 + leap, 334 + leap];
        let year_day = (cum_day_in_months[month as usize] + month_day as i64 - 1).try_into()?;

        Ok(Self { second, minute, hour, month_day, month, year, week_day, year_day })
    }

    /// Convert to a date time
    pub fn to_date_time(self) -> DateTime {
        DateTime {
            second: self.second,
            minute: self.minute,
            hour: self.hour,
            month_day: self.month_day,
            month: self.month,
            year: self.year,
            week_day: self.week_day,
            year_day: self.year_day,
            local_time_type: LocalTimeType::with_ut_offset(0),
        }
    }
}

/// Date time associated to a local time type, exprimed in the [proleptic gregorian calendar](https://en.wikipedia.org/wiki/Proleptic_Gregorian_calendar)
#[derive(Debug, Clone, Eq, PartialEq)]
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

    /// Returns the current date time associated to the specified time zone
    pub fn now(time_zone: &TimeZone) -> Result<Self> {
        Self::from_unix_time(time_zone, SystemTime::now().duration_since(SystemTime::UNIX_EPOCH)?.as_secs().try_into()?)
    }

    /// Construct date time from a time zone and an UTC date time
    pub fn from_utc_date_time(time_zone: &TimeZone, utc_date_time: UtcDateTime) -> Result<Self> {
        // Preserve leap seconds
        let utc_leap = utc_date_time.second.max(59) - 59;

        let mut date_time = Self::from_unix_time(time_zone, utc_date_time.to_date_time().unix_time() - utc_leap as i64)?;
        date_time.second += utc_leap;

        Ok(date_time)
    }

    /// Construct date time from a time zone and an unix time in seconds
    pub fn from_unix_time(time_zone: &TimeZone, unix_time: i64) -> Result<Self> {
        use constants::*;

        let local_time_type = time_zone.find_local_time_type(unix_time)?;

        let seconds = unix_time + local_time_type.ut_offset as i64 - UNIX_OFFSET_SECS;
        let mut remaining_days = seconds / SECONDS_PER_DAY;
        let mut remaining_seconds = seconds % SECONDS_PER_DAY;
        if remaining_seconds < 0 {
            remaining_seconds += SECONDS_PER_DAY;
            remaining_days -= 1;
        }

        let week_day = (3 + remaining_days).rem_euclid(DAYS_PER_WEEK);

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

        let leap = (remaining_years == 0 && (cycles_4_years != 0 || cycles_100_years == 0)) as i64;
        let year_day = (remaining_days + OFFSET_DAYS + leap).rem_euclid(DAYS_PER_NORMAL_YEAR + leap);

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
            week_day: week_day.try_into()?,
            year_day: year_day.try_into()?,
            local_time_type: local_time_type.clone(),
        })
    }

    /// Returns the UTC unix time in seconds associated to the date time
    pub fn unix_time(&self) -> i64 {
        use constants::*;

        let mut result = days_since_unix_epoch(self.year, self.month.into(), self.month_day.into());
        result *= HOURS_PER_DAY;
        result += self.hour as i64;
        result *= MINUTES_PER_HOUR;
        result += self.minute as i64;
        result *= SECONDS_PER_MINUTE;
        result += self.second as i64;
        result -= self.local_time_type.ut_offset as i64;

        result
    }

    /// Changes the associated time zone
    pub fn with_timezone(&self, time_zone: &TimeZone) -> Result<Self> {
        Self::from_unix_time(time_zone, self.unix_time())
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
            std: LocalTimeType { ut_offset: 0, is_dst: false, time_zone_designation: "".to_owned() },
            dst: LocalTimeType { ut_offset: 0, is_dst: true, time_zone_designation: "".to_owned() },
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
            let time_zone_local_1 = TimeZone::local()?;
            let time_zone_local_2 = TimeZone::from_posix_tz("localtime")?;
            let time_zone_local_3 = TimeZone::from_posix_tz("/etc/localtime")?;
            let time_zone_local_4 = TimeZone::from_posix_tz(":/etc/localtime")?;

            assert_eq!(time_zone_local_1, time_zone_local_2);
            assert_eq!(time_zone_local_1, time_zone_local_3);
            assert_eq!(time_zone_local_1, time_zone_local_4);

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

        let unix_times = [-93750523200, -11670955200, -8515195200, -8483659200, -8389051200, 951825600, 983448000, 1078056000, 4107585600, 32540356800];

        let date_times_utc = [
            DateTime { second: 0, minute: 0, hour: 12, month_day: 1, month: 2, year: -2901, week_day: 5, year_day: 59, local_time_type: utc.clone() },
            DateTime { second: 0, minute: 0, hour: 12, month_day: 29, month: 1, year: -300, week_day: 2, year_day: 59, local_time_type: utc.clone() },
            DateTime { second: 0, minute: 0, hour: 12, month_day: 1, month: 2, year: -200, week_day: 1, year_day: 59, local_time_type: utc.clone() },
            DateTime { second: 0, minute: 0, hour: 12, month_day: 1, month: 2, year: -199, week_day: 2, year_day: 59, local_time_type: utc.clone() },
            DateTime { second: 0, minute: 0, hour: 12, month_day: 29, month: 1, year: -196, week_day: 5, year_day: 59, local_time_type: utc.clone() },
            DateTime { second: 0, minute: 0, hour: 12, month_day: 29, month: 1, year: 100, week_day: 2, year_day: 59, local_time_type: utc.clone() },
            DateTime { second: 0, minute: 0, hour: 12, month_day: 1, month: 2, year: 101, week_day: 4, year_day: 59, local_time_type: utc.clone() },
            DateTime { second: 0, minute: 0, hour: 12, month_day: 29, month: 1, year: 104, week_day: 0, year_day: 59, local_time_type: utc.clone() },
            DateTime { second: 0, minute: 0, hour: 12, month_day: 1, month: 2, year: 200, week_day: 1, year_day: 59, local_time_type: utc.clone() },
            DateTime { second: 0, minute: 0, hour: 12, month_day: 1, month: 2, year: 1101, week_day: 0, year_day: 59, local_time_type: utc },
        ];

        let date_times_cet = [
            DateTime { second: 0, minute: 0, hour: 13, month_day: 1, month: 2, year: -2901, week_day: 5, year_day: 59, local_time_type: cet.clone() },
            DateTime { second: 0, minute: 0, hour: 13, month_day: 29, month: 1, year: -300, week_day: 2, year_day: 59, local_time_type: cet.clone() },
            DateTime { second: 0, minute: 0, hour: 13, month_day: 1, month: 2, year: -200, week_day: 1, year_day: 59, local_time_type: cet.clone() },
            DateTime { second: 0, minute: 0, hour: 13, month_day: 1, month: 2, year: -199, week_day: 2, year_day: 59, local_time_type: cet.clone() },
            DateTime { second: 0, minute: 0, hour: 13, month_day: 29, month: 1, year: -196, week_day: 5, year_day: 59, local_time_type: cet.clone() },
            DateTime { second: 0, minute: 0, hour: 13, month_day: 29, month: 1, year: 100, week_day: 2, year_day: 59, local_time_type: cet.clone() },
            DateTime { second: 0, minute: 0, hour: 13, month_day: 1, month: 2, year: 101, week_day: 4, year_day: 59, local_time_type: cet.clone() },
            DateTime { second: 0, minute: 0, hour: 13, month_day: 29, month: 1, year: 104, week_day: 0, year_day: 59, local_time_type: cet.clone() },
            DateTime { second: 0, minute: 0, hour: 13, month_day: 1, month: 2, year: 200, week_day: 1, year_day: 59, local_time_type: cet.clone() },
            DateTime { second: 0, minute: 0, hour: 13, month_day: 1, month: 2, year: 1101, week_day: 0, year_day: 59, local_time_type: cet },
        ];

        for ((unix_time, date_time_utc), date_time_cet) in unix_times.into_iter().zip(date_times_utc).zip(date_times_cet) {
            assert_eq!(DateTime::from_unix_time(&time_zone_utc, unix_time)?, date_time_utc);
            assert_eq!(date_time_utc.unix_time(), unix_time);

            assert_eq!(DateTime::from_unix_time(&time_zone_cet, unix_time)?, date_time_cet);
            assert_eq!(date_time_cet.unix_time(), unix_time);
        }

        Ok(())
    }

    #[test]
    fn test_date_time_leap_seconds() -> Result<()> {
        let utc_date_time = UtcDateTime::new(1972, 5, 30, 23, 59, 60)?;
        let date_time = DateTime::from_utc_date_time(&TimeZone::fixed(-3600), utc_date_time)?;

        let date_time_result = DateTime {
            second: 60,
            minute: 59,
            hour: 22,
            month_day: 30,
            month: 5,
            year: 72,
            week_day: 5,
            year_day: 181,
            local_time_type: LocalTimeType::with_ut_offset(-3600),
        };

        assert_eq!(date_time, date_time_result);
        assert_eq!(date_time.unix_time(), date_time_result.unix_time());

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
        assert_eq!(days_since_unix_epoch(-200, 2, 1), -98556);
        assert_eq!(days_since_unix_epoch(-199, 2, 1), -98191);
        assert_eq!(days_since_unix_epoch(-196, 1, 29), -97096);
        assert_eq!(days_since_unix_epoch(100, 1, 29), 11016);
        assert_eq!(days_since_unix_epoch(101, 2, 1), 11382);
        assert_eq!(days_since_unix_epoch(104, 1, 29), 12477);
        assert_eq!(days_since_unix_epoch(200, 2, 1), 47541);
        assert_eq!(days_since_unix_epoch(1101, 2, 1), 376624);
    }

    #[test]
    fn test_with_timezone() -> Result<()> {
        let utc = DateTime::from_unix_time(&TimeZone::utc(), 1645360496)?;
        assert_eq!(
            &utc,
            &DateTime {
                second: 56,
                minute: 34,
                hour: 12,
                month_day: 20,
                month: 1,
                year: 122,
                week_day: 0,
                year_day: 50,
                local_time_type: LocalTimeType {
                    ut_offset: 0,
                    is_dst: false,
                    time_zone_designation: "".into(),
                },
            },
        );

        let berlin = utc.with_timezone(&TimeZone::from_posix_tz("Europe/Berlin")?)?;
        assert_eq!(
            &berlin,
            &DateTime {
                second: 56,
                minute: 34,
                hour: 13,
                month_day: 20,
                month: 1,
                year: 122,
                week_day: 0,
                year_day: 50,
                local_time_type: LocalTimeType {
                    ut_offset: 3600,
                    is_dst: false,
                    time_zone_designation: "CET".into(),
                },
            },
        );

        let maseru = berlin.with_timezone(&TimeZone::from_posix_tz("Africa/Maseru")?)?;
        assert_eq!(
            &maseru,
            &DateTime {
                second: 56,
                minute: 34,
                hour: 14,
                month_day: 20,
                month: 1,
                year: 122,
                week_day: 0,
                year_day: 50,
                local_time_type: LocalTimeType {
                    ut_offset: 7200,
                    is_dst: false,
                    time_zone_designation: "SAST".into(),
                },
            },
        );

        let belize = maseru.with_timezone(&TimeZone::from_posix_tz("America/Belize")?)?;
        assert_eq!(
            &belize,
            &DateTime {
                second: 56,
                minute: 34,
                hour: 6,
                month_day: 20,
                month: 1,
                year: 122,
                week_day: 0,
                year_day: 50,
                local_time_type: LocalTimeType {
                    ut_offset: -21600,
                    is_dst: false,
                    time_zone_designation: "CST".into(),
                },
            },
        );

        Ok(())
    }
}
