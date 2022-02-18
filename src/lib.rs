//! This crate provides the struct `TimeZone` and `DateTime`, which can be used to determine local time on a given time zone.
//!
//! # Usage
//!
//! ## Construct a time zone object
//!
//! ```rust
//! # fn timezone() -> Result<(), tz::TzError> {
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
//!     // Get local time zone
//!     let time_zone_local = TimeZone::local()?;
//!
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
//! # Ok(())
//! # }
//! ```
//!
//! ## Construct a date time object
//!
//! ```rust
//! # fn datetime() -> Result<(), tz::TzError> {
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
//!
//!     // Get the current date time at the local time zone
//!     let time_zone_local = TimeZone::local()?;
//!     let _date_time = DateTime::now(&time_zone_local)?;
//! # Ok(())
//! # }
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

#[derive(Debug)]
pub enum TzError {
    ConversionError(TryFromIntError),
    IoError(io::Error),
    SystemTimeError(SystemTimeError),
    TzFileError(TzFileError),
    TzStringError(TzStringError),
    DateTimeInputError,
}

impl fmt::Display for TzError {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Self::ConversionError(error) => error.fmt(f),
            Self::IoError(error) => error.fmt(f),
            Self::SystemTimeError(error) => error.fmt(f),
            Self::TzFileError(error) => error.fmt(f),
            Self::TzStringError(error) => error.fmt(f),
            Self::DateTimeInputError => write!(f, "invalid DateTime input"),
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

#[derive(Debug, Copy, Clone)]
struct Transition {
    unix_leap_time: i64,
    local_time_type_index: usize,
}

#[derive(Debug, Copy, Clone)]
struct LeapSecond {
    unix_leap_time: i64,
    correction: i32,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct LocalTimeType {
    ut_offset: i32,
    is_dst: bool,
    time_zone_designation: String,
}

impl LocalTimeType {
    pub fn ut_offset(&self) -> i32 {
        self.ut_offset
    }

    pub fn is_dst(&self) -> bool {
        self.is_dst
    }

    pub fn time_zone_designation(&self) -> &str {
        &self.time_zone_designation
    }

    pub fn utc() -> Self {
        Self::with_ut_offset(0)
    }

    pub fn with_ut_offset(ut_offset: i32) -> Self {
        Self { ut_offset, is_dst: false, time_zone_designation: "".to_owned() }
    }
}

#[derive(Debug, Copy, Clone)]
enum RuleDay {
    Julian1WithoutLeap(u16),
    Julian0WithLeap(u16),
    MonthWeekDay { month: u8, week: u8, week_day: u8 },
}

impl RuleDay {
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

    fn unix_time(&self, year: i32, day_time_in_utc: i64) -> i64 {
        use constants::*;

        let (month, month_day) = self.transition_date(year);
        days_since_unix_epoch(year, month, month_day) * SECONDS_PER_DAY + day_time_in_utc
    }
}

#[derive(Debug, Clone)]
enum TransitionRule {
    Fixed(LocalTimeType),
    Alternate { std: LocalTimeType, dst: LocalTimeType, dst_start: RuleDay, dst_start_time: i32, dst_end: RuleDay, dst_end_time: i32 },
}

impl TransitionRule {
    fn find_local_time_type(&self, unix_time: i64) -> Result<&LocalTimeType, TzError> {
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

#[derive(Debug, Clone)]
pub struct TimeZone {
    transitions: Vec<Transition>,
    local_time_types: Vec<LocalTimeType>,
    leap_seconds: Vec<LeapSecond>,
    extra_rule: Option<TransitionRule>,
}

impl TimeZone {
    pub fn utc() -> Self {
        Self::fixed(0)
    }

    pub fn fixed(ut_offset: i32) -> Self {
        Self {
            transitions: Vec::new(),
            local_time_types: vec![LocalTimeType::with_ut_offset(ut_offset)],
            leap_seconds: Vec::new(),
            extra_rule: Some(TransitionRule::Fixed(LocalTimeType::with_ut_offset(ut_offset))),
        }
    }

    pub fn local() -> Result<Self, TzError> {
        Self::from_posix_tz("localtime")
    }

    pub fn from_posix_tz(tz_string: &str) -> Result<Self, TzError> {
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
                let rule = tz_string::parse_posix_tz(tz_string.as_bytes(), false)?;

                let local_time_types = match &rule {
                    TransitionRule::Fixed(local_time_type) => vec![local_time_type.clone()],
                    TransitionRule::Alternate { std, dst, .. } => vec![std.clone(), dst.clone()],
                };
                Ok(TimeZone { transitions: Vec::new(), local_time_types, leap_seconds: Vec::new(), extra_rule: Some(rule) })
            }
        }
    }

    pub fn find_local_time_type(&self, unix_time: i64) -> Result<&LocalTimeType, TzError> {
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
                        None => Ok(&self.local_time_types[last_transition.local_time_type_index]),
                    }
                } else {
                    let index = self.transitions.partition_point(|x| x.unix_leap_time <= unix_leap_time);
                    let local_time_type_index = if index > 0 { self.transitions[index - 1].local_time_type_index } else { 0 };
                    Ok(&self.local_time_types[local_time_type_index])
                }
            }
        }
    }

    pub fn find_current_local_time_type(&self) -> Result<&LocalTimeType, TzError> {
        self.find_local_time_type(SystemTime::now().duration_since(SystemTime::UNIX_EPOCH)?.as_secs().try_into()?)
    }

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

    fn unix_leap_time_to_unix_time(&self, unix_leap_time: i64) -> i64 {
        let index = self.leap_seconds.partition_point(|x| x.unix_leap_time < unix_leap_time);
        let correction = if index > 0 { self.leap_seconds[index - 1].correction } else { 0 };

        unix_leap_time - correction as i64
    }
}

#[derive(Debug, Clone)]
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
    pub fn new(full_year: i32, month: u8, month_day: u8, hour: u8, minute: u8, second: u8) -> Result<Self, TzError> {
        use constants::*;

        let year = full_year - 1900;

        let mut check = true;
        check = check && (0..=11).contains(&month);
        check = check && (1..=31).contains(&month_day);
        check = check && (0..=23).contains(&hour);
        check = check && (0..=59).contains(&minute);
        check = check && (0..=60).contains(&second);

        if !check {
            return Err(TzError::DateTimeInputError);
        }

        let leap = is_leap_year(year) as i64;

        let mut day_in_month = DAY_IN_MONTHS_NORMAL_YEAR[month as usize];
        if month == 1 {
            day_in_month += leap;
        }

        if month_day as i64 > day_in_month {
            return Err(TzError::DateTimeInputError);
        }

        let days_since_unix_epoch = days_since_unix_epoch(year, month.into(), month_day.into());

        let week_day = (4 + days_since_unix_epoch).rem_euclid(DAYS_PER_WEEK).try_into()?;

        let cum_day_in_months = [0, 31, 59 + leap, 90 + leap, 120 + leap, 151 + leap, 181 + leap, 212 + leap, 243 + leap, 273 + leap, 304 + leap, 334 + leap];
        let year_day = (cum_day_in_months[month as usize] + month_day as i64 - 1).try_into()?;

        Ok(Self { second, minute, hour, month_day, month, year, week_day, year_day })
    }

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
    /// Local time parameters
    local_time_type: LocalTimeType,
}

impl DateTime {
    pub fn second(&self) -> u8 {
        self.second
    }

    pub fn minute(&self) -> u8 {
        self.minute
    }

    pub fn hour(&self) -> u8 {
        self.hour
    }

    pub fn month_day(&self) -> u8 {
        self.month_day
    }

    pub fn month(&self) -> u8 {
        self.month
    }

    pub fn year(&self) -> i32 {
        self.year
    }

    pub fn full_year(&self) -> i32 {
        self.year + 1900
    }

    pub fn week_day(&self) -> u8 {
        self.week_day
    }

    pub fn year_day(&self) -> u16 {
        self.year_day
    }

    pub fn local_time_type(&self) -> &LocalTimeType {
        &self.local_time_type
    }

    pub fn now(time_zone: &TimeZone) -> Result<Self, TzError> {
        Self::from_unix_time(time_zone, SystemTime::now().duration_since(SystemTime::UNIX_EPOCH)?.as_secs().try_into()?)
    }

    pub fn from_utc_date_time(time_zone: &TimeZone, utc_date_time: UtcDateTime) -> Result<Self, TzError> {
        Self::from_unix_time(time_zone, utc_date_time.to_date_time().unix_time())
    }

    pub fn from_unix_time(time_zone: &TimeZone, unix_time: i64) -> Result<Self, TzError> {
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
        let mut year_day = remaining_days + OFFSET_DAYS + leap;
        let mut year = OFFSET_YEARS + remaining_years + cycles_4_years * 4 + cycles_100_years * 100 + cycles_400_years * 400;

        if year_day >= DAYS_PER_NORMAL_YEAR + leap {
            year_day -= DAYS_PER_NORMAL_YEAR + leap;
            year += 1;
        }

        let cum_day_in_months =
            [0, 31, 59 + leap, 90 + leap, 120 + leap, 151 + leap, 181 + leap, 212 + leap, 243 + leap, 273 + leap, 304 + leap, 334 + leap, 365 + leap];

        let month = cum_day_in_months[1..].partition_point(|&x| x <= year_day);
        let month_day = 1 + year_day - cum_day_in_months[month];

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
}

fn is_leap_year(year: i32) -> bool {
    let full_year = 1900 + year;
    full_year % 400 == 0 || (full_year % 4 == 0 && full_year % 100 != 0)
}

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
