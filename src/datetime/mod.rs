//! Types related to a date time.

use crate::error::*;
use crate::timezone::{LocalTimeType, TimeZoneRef};
use crate::utils::*;

use std::cmp::Ordering;
use std::fmt;
use std::time::SystemTime;

/// UTC date time exprimed in the [proleptic gregorian calendar](https://en.wikipedia.org/wiki/Proleptic_Gregorian_calendar)
#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd)]
pub struct UtcDateTime {
    /// Years since 1900
    year: i32,
    /// Month in `[0, 11]`
    month: u8,
    /// Day of the month in `[1, 31]`
    month_day: u8,
    /// Hours since midnight in `[0, 23]`
    hour: u8,
    /// Minutes in `[0, 59]`
    minute: u8,
    /// Seconds in `[0, 60]`, with a possible leap second
    second: u8,
    /// Nanoseconds in `[0, 999_999_999]`
    nanoseconds: u32,
}

impl fmt::Display for UtcDateTime {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        format_date_time(f, self.full_year(), self.month + 1, self.month_day, self.hour, self.minute, self.second, self.nanoseconds, 0)
    }
}

impl UtcDateTime {
    /// Minimum Unix time allowed for a UTC date time
    pub const MIN_UNIX_TIME: i64 = -67768040609740800;
    /// Maximum Unix time allowed for a UTC date time
    pub const MAX_UNIX_TIME: i64 = 67767976233532799;

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
    /// * `nanoseconds`: Nanoseconds in `[0, 999_999_999]`
    ///
    pub const fn new(full_year: i32, month: u8, month_day: u8, hour: u8, minute: u8, second: u8, nanoseconds: u32) -> Result<Self, DateTimeError> {
        use crate::constants::*;

        // Exclude the maximum possible UTC date time with a leap second
        if full_year == i32::MAX && month == 11 && month_day == 31 && hour == 23 && minute == 59 && second == 60 {
            return Err(DateTimeError("out of range date time"));
        }

        let year = match full_year.checked_sub(1900) {
            Some(year) => year,
            None => return Err(DateTimeError("invalid year: out of range operation")),
        };

        if month > 11 {
            return Err(DateTimeError("invalid month"));
        }
        if !(1 <= month_day && month_day <= 31) {
            return Err(DateTimeError("invalid month day"));
        }
        if hour > 23 {
            return Err(DateTimeError("invalid hour"));
        }
        if minute > 59 {
            return Err(DateTimeError("invalid minute"));
        }
        if second > 60 {
            return Err(DateTimeError("invalid second"));
        }
        if nanoseconds >= NANOSECONDS_PER_SECOND {
            return Err(DateTimeError("invalid nanoseconds"));
        }

        let leap = is_leap_year(year) as i64;

        let mut day_in_month = DAY_IN_MONTHS_NORMAL_YEAR[month as usize];
        if month == 1 {
            day_in_month += leap;
        }

        if month_day as i64 > day_in_month {
            return Err(DateTimeError("invalid month day"));
        }

        Ok(Self { year, month, month_day, hour, minute, second, nanoseconds })
    }

    /// Construct a UTC date time from a Unix time in seconds and nanoseconds
    pub const fn from_timespec(unix_time: i64, nanoseconds: u32) -> Result<Self, OutOfRangeError> {
        use crate::constants::*;

        if !(Self::MIN_UNIX_TIME <= unix_time && unix_time <= Self::MAX_UNIX_TIME) {
            return Err(OutOfRangeError("out of range date time"));
        }

        let seconds = match unix_time.checked_sub(UNIX_OFFSET_SECS) {
            Some(seconds) => seconds,
            None => return Err(OutOfRangeError("out of range operation")),
        };

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

        let cycles_100_years = min(remaining_days / DAYS_PER_100_YEARS, 3);
        remaining_days -= cycles_100_years * DAYS_PER_100_YEARS;

        let cycles_4_years = min(remaining_days / DAYS_PER_4_YEARS, 24);
        remaining_days -= cycles_4_years * DAYS_PER_4_YEARS;

        let remaining_years = min(remaining_days / DAYS_PER_NORMAL_YEAR, 3);
        remaining_days -= remaining_years * DAYS_PER_NORMAL_YEAR;

        let mut year = OFFSET_YEARS + remaining_years + cycles_4_years * 4 + cycles_100_years * 100 + cycles_400_years * 400;

        let mut month = 0;
        while month < DAY_IN_MONTHS_LEAP_YEAR_FROM_MARCH.len() {
            let days = DAY_IN_MONTHS_LEAP_YEAR_FROM_MARCH[month];
            if remaining_days < days {
                break;
            }
            remaining_days -= days;
            month += 1;
        }
        month += 2;

        if month >= MONTHS_PER_YEAR as usize {
            month -= MONTHS_PER_YEAR as usize;
            year += 1;
        }

        let month_day = 1 + remaining_days;

        let hour = remaining_seconds / SECONDS_PER_HOUR;
        let minute = (remaining_seconds / SECONDS_PER_MINUTE) % MINUTES_PER_HOUR;
        let second = remaining_seconds % SECONDS_PER_MINUTE;

        let year = match try_into_i32(year) {
            Ok(year) => year,
            Err(error) => return Err(error),
        };

        Ok(Self { year, month: month as u8, month_day: month_day as u8, hour: hour as u8, minute: minute as u8, second: second as u8, nanoseconds })
    }

    /// Returns the current UTC date time
    pub fn now() -> Result<Self, TzError> {
        let now = SystemTime::now().duration_since(SystemTime::UNIX_EPOCH)?;
        Ok(Self::from_timespec(now.as_secs().try_into()?, now.subsec_nanos())?)
    }

    /// Returns the Unix time in seconds associated to the UTC date time
    pub const fn unix_time(&self) -> i64 {
        use crate::constants::*;

        let mut result = days_since_unix_epoch(self.year, self.month as usize, self.month_day as i64);
        result *= HOURS_PER_DAY;
        result += self.hour as i64;
        result *= MINUTES_PER_HOUR;
        result += self.minute as i64;
        result *= SECONDS_PER_MINUTE;
        result += self.second as i64;

        result
    }

    /// Project the UTC date time into a time zone.
    ///
    /// Leap seconds are not preserved.
    ///
    pub const fn project(&self, time_zone_ref: TimeZoneRef) -> Result<DateTime, ProjectDateTimeError> {
        DateTime::from_timespec(self.unix_time(), self.nanoseconds, time_zone_ref)
    }
}

/// Date time associated to a local time type, exprimed in the [proleptic gregorian calendar](https://en.wikipedia.org/wiki/Proleptic_Gregorian_calendar)
#[derive(Debug, Clone)]
pub struct DateTime {
    /// Years since 1900
    year: i32,
    /// Month in `[0, 11]`
    month: u8,
    /// Day of the month in `[1, 31]`
    month_day: u8,
    /// Hours since midnight in `[0, 23]`
    hour: u8,
    /// Minutes in `[0, 59]`
    minute: u8,
    /// Seconds in `[0, 60]`, with a possible leap second
    second: u8,
    /// Local time type
    local_time_type: LocalTimeType,
    /// UTC Unix time in seconds
    unix_time: i64,
    /// Nanoseconds in `[0, 999_999_999]`
    nanoseconds: u32,
}

impl PartialEq for DateTime {
    fn eq(&self, other: &Self) -> bool {
        (self.unix_time, self.nanoseconds) == (other.unix_time, other.nanoseconds)
    }
}

impl PartialOrd for DateTime {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        (self.unix_time, self.nanoseconds).partial_cmp(&(other.unix_time, other.nanoseconds))
    }
}

impl fmt::Display for DateTime {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let ut_offset = self.local_time_type().ut_offset();
        format_date_time(f, self.full_year(), self.month + 1, self.month_day, self.hour, self.minute, self.second, self.nanoseconds, ut_offset)
    }
}

impl DateTime {
    /// Construct a date time from a Unix time in seconds with nanoseconds and a time zone
    pub const fn from_timespec(unix_time: i64, nanoseconds: u32, time_zone_ref: TimeZoneRef) -> Result<Self, ProjectDateTimeError> {
        let local_time_type = match time_zone_ref.find_local_time_type(unix_time) {
            Ok(local_time_type) => local_time_type.clone(),
            Err(FindLocalTimeTypeError(error)) => return Err(ProjectDateTimeError(error)),
        };

        let unix_time_with_offset = match unix_time.checked_add(local_time_type.ut_offset() as i64) {
            Some(unix_time_with_offset) => unix_time_with_offset,
            None => return Err(ProjectDateTimeError("out of range date time")),
        };

        let utc_date_time_with_offset = match UtcDateTime::from_timespec(unix_time_with_offset, nanoseconds) {
            Ok(utc_date_time_with_offset) => utc_date_time_with_offset,
            Err(OutOfRangeError(error)) => return Err(ProjectDateTimeError(error)),
        };

        let UtcDateTime { year, month, month_day, hour, minute, second, nanoseconds } = utc_date_time_with_offset;
        Ok(Self { year, month, month_day, hour, minute, second, local_time_type, unix_time, nanoseconds })
    }

    /// Returns the current date time associated to the specified time zone
    pub fn now(time_zone_ref: TimeZoneRef) -> Result<Self, TzError> {
        let now = SystemTime::now().duration_since(SystemTime::UNIX_EPOCH)?;
        Ok(Self::from_timespec(now.as_secs().try_into()?, now.subsec_nanos(), time_zone_ref)?)
    }

    /// Project the date time into another time zone.
    ///
    /// Leap seconds are not preserved.
    ///
    pub const fn project(&self, time_zone_ref: TimeZoneRef) -> Result<Self, ProjectDateTimeError> {
        Self::from_timespec(self.unix_time, self.nanoseconds, time_zone_ref)
    }
}

/// Macro for implementing date time getters
macro_rules! impl_datetime {
    () => {
        /// Returns year
        pub const fn full_year(&self) -> i32 {
            self.year + 1900
        }

        /// Returns years since 1900
        pub const fn year(&self) -> i32 {
            self.year
        }

        /// Returns month in `[0, 11]`
        pub const fn month(&self) -> u8 {
            self.month
        }

        /// Returns day of the month in `[1, 31]`
        pub const fn month_day(&self) -> u8 {
            self.month_day
        }

        /// Returns hours since midnight in `[0, 23]`
        pub const fn hour(&self) -> u8 {
            self.hour
        }

        /// Returns minutes in `[0, 59]`
        pub const fn minute(&self) -> u8 {
            self.minute
        }

        /// Returns seconds in `[0, 60]`, with a possible leap second
        pub const fn second(&self) -> u8 {
            self.second
        }

        /// Returns nanoseconds in `[0, 999_999_999]`
        pub const fn nanoseconds(&self) -> u32 {
            self.nanoseconds
        }

        /// Returns days since Sunday in `[0, 6]`
        pub const fn week_day(&self) -> u8 {
            week_day(self.year, self.month as usize, self.month_day as i64)
        }

        /// Returns days since January 1 in `[0, 365]`
        pub const fn year_day(&self) -> u16 {
            year_day(self.year, self.month as usize, self.month_day as i64)
        }
    };
}

impl UtcDateTime {
    impl_datetime!();
}

impl DateTime {
    impl_datetime!();

    /// Returns local time type
    pub const fn local_time_type(&self) -> &LocalTimeType {
        &self.local_time_type
    }

    /// Returns UTC Unix time in seconds
    pub const fn unix_time(&self) -> i64 {
        self.unix_time
    }
}

/// Compute the number of days since Sunday in `[0, 6]`
///
/// ## Inputs
///
/// * `year`: Years since 1900
/// * `month`: Month in `[0, 11]`
/// * `month_day`: Day of the month in `[1, 31]`
///
const fn week_day(year: i32, month: usize, month_day: i64) -> u8 {
    use crate::constants::*;

    let days_since_unix_epoch = days_since_unix_epoch(year, month, month_day);
    (4 + days_since_unix_epoch).rem_euclid(DAYS_PER_WEEK) as u8
}

/// Compute the number of days since January 1 in `[0, 365]`
///
/// ## Inputs
///
/// * `year`: Years since 1900
/// * `month`: Month in `[0, 11]`
/// * `month_day`: Day of the month in `[1, 31]`
///
const fn year_day(year: i32, month: usize, month_day: i64) -> u16 {
    use crate::constants::*;

    let leap = (month >= 2 && is_leap_year(year)) as i64;
    (CUMUL_DAY_IN_MONTHS_NORMAL_YEAR[month] + leap + month_day - 1) as u16
}

/// Check if a year is a leap year.
///
/// ## Inputs
///
/// * `year`: Years since 1900
///
pub(crate) const fn is_leap_year(year: i32) -> bool {
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
pub(crate) const fn days_since_unix_epoch(year: i32, month: usize, month_day: i64) -> i64 {
    use crate::constants::*;

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

    result += CUMUL_DAY_IN_MONTHS_NORMAL_YEAR[month as usize] + month_day - 1;

    result
}

/// Format a date time
///
/// ## Inputs
///
/// * `f`: Formatter
/// * `year`: Years since 1900
/// * `month`: Month in `[0, 11]`
/// * `month_day`: Day of the month in `[1, 31]`
/// * `hour`: Hours since midnight in `[0, 23]`
/// * `minute`: Minutes in `[0, 59]`
/// * `second`: Seconds in `[0, 60]`, with a possible leap second
/// * `nanoseconds`: Nanoseconds in `[0, 999_999_999]`
/// * `ut_offset`: Offset from UTC in seconds
///
#[allow(clippy::too_many_arguments)]
fn format_date_time(
    f: &mut fmt::Formatter,
    year: i32,
    month: u8,
    month_day: u8,
    hour: u8,
    minute: u8,
    second: u8,
    nanoseconds: u32,
    ut_offset: i32,
) -> fmt::Result {
    use crate::constants::*;

    write!(f, "{}-{:02}-{:02}T{:02}:{:02}:{:02}.{:09}", year, month, month_day, hour, minute, second, nanoseconds)?;

    if ut_offset != 0 {
        let ut_offset = ut_offset as i64;
        let ut_offset_abs = ut_offset.abs();

        let offset_hour = ut_offset / SECONDS_PER_HOUR;
        let offset_minute = (ut_offset_abs / SECONDS_PER_MINUTE) % MINUTES_PER_HOUR;
        let offset_second = ut_offset_abs % SECONDS_PER_MINUTE;

        write!(f, "{:+03}:{:02}", offset_hour, offset_minute)?;

        if offset_second != 0 {
            write!(f, ":{:02}", offset_second)?;
        }
    } else {
        write!(f, "Z")?;
    }

    Ok(())
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::timezone::*;
    use crate::Result;

    fn check_equal_date_time(x: &DateTime, y: &DateTime) {
        assert_eq!(x.year(), y.year());
        assert_eq!(x.month(), y.month());
        assert_eq!(x.month_day(), y.month_day());
        assert_eq!(x.hour(), y.hour());
        assert_eq!(x.minute(), y.minute());
        assert_eq!(x.second(), y.second());
        assert_eq!(x.local_time_type(), y.local_time_type());
        assert_eq!(x.unix_time(), y.unix_time());
        assert_eq!(x.nanoseconds(), y.nanoseconds());
    }

    #[test]
    fn test_date_time() -> Result<()> {
        let time_zone_utc = TimeZone::utc();
        let utc = LocalTimeType::utc();

        let time_zone_cet = TimeZone::fixed(3600)?;
        let cet = LocalTimeType::with_ut_offset(3600)?;

        let time_zone_eet = TimeZone::fixed(7200)?;
        let eet = LocalTimeType::with_ut_offset(7200)?;

        assert_eq!(DateTime::now(time_zone_utc.as_ref())?.local_time_type().ut_offset(), 0);
        assert_eq!(DateTime::now(time_zone_cet.as_ref())?.local_time_type().ut_offset(), 3600);
        assert_eq!(DateTime::now(time_zone_eet.as_ref())?.local_time_type().ut_offset(), 7200);

        let unix_times = [
            -93750523200,
            -11670955200,
            -11670868800,
            -8515195200,
            -8483659200,
            -8389051200,
            -8388964800,
            951825600,
            951912000,
            983448000,
            1078056000,
            1078142400,
            4107585600,
            32540356800,
        ];

        let nanoseconds_list = [10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23];

        #[rustfmt::skip]
        let date_times_utc = [
            DateTime { year: -2901, month: 2, month_day: 1,  hour: 12, minute: 0, second: 0, local_time_type: utc.clone(), unix_time: -93750523200, nanoseconds: 10 },
            DateTime { year: -300,  month: 1, month_day: 29, hour: 12, minute: 0, second: 0, local_time_type: utc.clone(), unix_time: -11670955200, nanoseconds: 11 },
            DateTime { year: -300,  month: 2, month_day: 1,  hour: 12, minute: 0, second: 0, local_time_type: utc.clone(), unix_time: -11670868800, nanoseconds: 12 },
            DateTime { year: -200,  month: 2, month_day: 1,  hour: 12, minute: 0, second: 0, local_time_type: utc.clone(), unix_time: -8515195200,  nanoseconds: 13 },
            DateTime { year: -199,  month: 2, month_day: 1,  hour: 12, minute: 0, second: 0, local_time_type: utc.clone(), unix_time: -8483659200,  nanoseconds: 14 },
            DateTime { year: -196,  month: 1, month_day: 29, hour: 12, minute: 0, second: 0, local_time_type: utc.clone(), unix_time: -8389051200,  nanoseconds: 15 },
            DateTime { year: -196,  month: 2, month_day: 1,  hour: 12, minute: 0, second: 0, local_time_type: utc.clone(), unix_time: -8388964800,  nanoseconds: 16 },
            DateTime { year: 100,   month: 1, month_day: 29, hour: 12, minute: 0, second: 0, local_time_type: utc.clone(), unix_time: 951825600,    nanoseconds: 17 },
            DateTime { year: 100,   month: 2, month_day: 1,  hour: 12, minute: 0, second: 0, local_time_type: utc.clone(), unix_time: 951912000,    nanoseconds: 18 },
            DateTime { year: 101,   month: 2, month_day: 1,  hour: 12, minute: 0, second: 0, local_time_type: utc.clone(), unix_time: 983448000,    nanoseconds: 19 },
            DateTime { year: 104,   month: 1, month_day: 29, hour: 12, minute: 0, second: 0, local_time_type: utc.clone(), unix_time: 1078056000,   nanoseconds: 20 },
            DateTime { year: 104,   month: 2, month_day: 1,  hour: 12, minute: 0, second: 0, local_time_type: utc.clone(), unix_time: 1078142400,   nanoseconds: 21 },
            DateTime { year: 200,   month: 2, month_day: 1,  hour: 12, minute: 0, second: 0, local_time_type: utc.clone(), unix_time: 4107585600,   nanoseconds: 22 },
            DateTime { year: 1101,  month: 2, month_day: 1,  hour: 12, minute: 0, second: 0, local_time_type: utc,         unix_time: 32540356800,  nanoseconds: 23 },
        ];

        #[rustfmt::skip]
         let date_times_cet = [
            DateTime { year: -2901, month: 2, month_day: 1,  hour: 13, minute: 0, second: 0, local_time_type: cet.clone(), unix_time: -93750523200, nanoseconds: 10 },
            DateTime { year: -300,  month: 1, month_day: 29, hour: 13, minute: 0, second: 0, local_time_type: cet.clone(), unix_time: -11670955200, nanoseconds: 11 },
            DateTime { year: -300,  month: 2, month_day: 1,  hour: 13, minute: 0, second: 0, local_time_type: cet.clone(), unix_time: -11670868800, nanoseconds: 12 },
            DateTime { year: -200,  month: 2, month_day: 1,  hour: 13, minute: 0, second: 0, local_time_type: cet.clone(), unix_time: -8515195200,  nanoseconds: 13 },
            DateTime { year: -199,  month: 2, month_day: 1,  hour: 13, minute: 0, second: 0, local_time_type: cet.clone(), unix_time: -8483659200,  nanoseconds: 14 },
            DateTime { year: -196,  month: 1, month_day: 29, hour: 13, minute: 0, second: 0, local_time_type: cet.clone(), unix_time: -8389051200,  nanoseconds: 15 },
            DateTime { year: -196,  month: 2, month_day: 1,  hour: 13, minute: 0, second: 0, local_time_type: cet.clone(), unix_time: -8388964800,  nanoseconds: 16 },
            DateTime { year: 100,   month: 1, month_day: 29, hour: 13, minute: 0, second: 0, local_time_type: cet.clone(), unix_time: 951825600,    nanoseconds: 17 },
            DateTime { year: 100,   month: 2, month_day: 1,  hour: 13, minute: 0, second: 0, local_time_type: cet.clone(), unix_time: 951912000,    nanoseconds: 18 },
            DateTime { year: 101,   month: 2, month_day: 1,  hour: 13, minute: 0, second: 0, local_time_type: cet.clone(), unix_time: 983448000,    nanoseconds: 19 },
            DateTime { year: 104,   month: 1, month_day: 29, hour: 13, minute: 0, second: 0, local_time_type: cet.clone(), unix_time: 1078056000,   nanoseconds: 20 },
            DateTime { year: 104,   month: 2, month_day: 1,  hour: 13, minute: 0, second: 0, local_time_type: cet.clone(), unix_time: 1078142400,   nanoseconds: 21 },
            DateTime { year: 200,   month: 2, month_day: 1,  hour: 13, minute: 0, second: 0, local_time_type: cet.clone(), unix_time: 4107585600,   nanoseconds: 22 },
            DateTime { year: 1101,  month: 2, month_day: 1,  hour: 13, minute: 0, second: 0, local_time_type: cet,         unix_time: 32540356800,  nanoseconds: 23 },
        ];

        #[rustfmt::skip]
         let date_times_eet = [
            DateTime { year: -2901, month: 2, month_day: 1,  hour: 14, minute: 0, second: 0, local_time_type: eet.clone(), unix_time: -93750523200, nanoseconds: 10 },
            DateTime { year: -300,  month: 1, month_day: 29, hour: 14, minute: 0, second: 0, local_time_type: eet.clone(), unix_time: -11670955200, nanoseconds: 11 },
            DateTime { year: -300,  month: 2, month_day: 1,  hour: 14, minute: 0, second: 0, local_time_type: eet.clone(), unix_time: -11670868800, nanoseconds: 12 },
            DateTime { year: -200,  month: 2, month_day: 1,  hour: 14, minute: 0, second: 0, local_time_type: eet.clone(), unix_time: -8515195200,  nanoseconds: 13 },
            DateTime { year: -199,  month: 2, month_day: 1,  hour: 14, minute: 0, second: 0, local_time_type: eet.clone(), unix_time: -8483659200,  nanoseconds: 14 },
            DateTime { year: -196,  month: 1, month_day: 29, hour: 14, minute: 0, second: 0, local_time_type: eet.clone(), unix_time: -8389051200,  nanoseconds: 15 },
            DateTime { year: -196,  month: 2, month_day: 1,  hour: 14, minute: 0, second: 0, local_time_type: eet.clone(), unix_time: -8388964800,  nanoseconds: 16 },
            DateTime { year: 100,   month: 1, month_day: 29, hour: 14, minute: 0, second: 0, local_time_type: eet.clone(), unix_time: 951825600,    nanoseconds: 17 },
            DateTime { year: 100,   month: 2, month_day: 1,  hour: 14, minute: 0, second: 0, local_time_type: eet.clone(), unix_time: 951912000,    nanoseconds: 18 },
            DateTime { year: 101,   month: 2, month_day: 1,  hour: 14, minute: 0, second: 0, local_time_type: eet.clone(), unix_time: 983448000,    nanoseconds: 19 },
            DateTime { year: 104,   month: 1, month_day: 29, hour: 14, minute: 0, second: 0, local_time_type: eet.clone(), unix_time: 1078056000,   nanoseconds: 20 },
            DateTime { year: 104,   month: 2, month_day: 1,  hour: 14, minute: 0, second: 0, local_time_type: eet.clone(), unix_time: 1078142400,   nanoseconds: 21 },
            DateTime { year: 200,   month: 2, month_day: 1,  hour: 14, minute: 0, second: 0, local_time_type: eet.clone(), unix_time: 4107585600,   nanoseconds: 22 },
            DateTime { year: 1101,  month: 2, month_day: 1,  hour: 14, minute: 0, second: 0, local_time_type: eet,         unix_time: 32540356800,  nanoseconds: 23 },
        ];

        for ((((unix_time, nanoseconds), date_time_utc), date_time_cet), date_time_eet) in
            unix_times.into_iter().zip(nanoseconds_list).zip(date_times_utc).zip(date_times_cet).zip(date_times_eet)
        {
            let utc_date_time = UtcDateTime::from_timespec(unix_time, nanoseconds)?;

            assert_eq!(UtcDateTime::from_timespec(utc_date_time.unix_time(), nanoseconds)?, utc_date_time);

            assert_eq!(utc_date_time.full_year(), date_time_utc.full_year());
            assert_eq!(utc_date_time.year(), date_time_utc.year());
            assert_eq!(utc_date_time.month(), date_time_utc.month());
            assert_eq!(utc_date_time.month_day(), date_time_utc.month_day());
            assert_eq!(utc_date_time.hour(), date_time_utc.hour());
            assert_eq!(utc_date_time.minute(), date_time_utc.minute());
            assert_eq!(utc_date_time.second(), date_time_utc.second());
            assert_eq!(utc_date_time.nanoseconds(), date_time_utc.nanoseconds());

            assert_eq!(utc_date_time.unix_time(), unix_time);
            assert_eq!(date_time_utc.unix_time(), unix_time);
            assert_eq!(date_time_cet.unix_time(), unix_time);
            assert_eq!(date_time_eet.unix_time(), unix_time);

            assert_eq!(date_time_utc, date_time_cet);
            assert_eq!(date_time_utc, date_time_eet);

            check_equal_date_time(&utc_date_time.project(time_zone_utc.as_ref())?, &date_time_utc);
            check_equal_date_time(&utc_date_time.project(time_zone_cet.as_ref())?, &date_time_cet);
            check_equal_date_time(&utc_date_time.project(time_zone_eet.as_ref())?, &date_time_eet);

            check_equal_date_time(&date_time_utc.project(time_zone_utc.as_ref())?, &date_time_utc);
            check_equal_date_time(&date_time_cet.project(time_zone_utc.as_ref())?, &date_time_utc);
            check_equal_date_time(&date_time_eet.project(time_zone_utc.as_ref())?, &date_time_utc);

            check_equal_date_time(&date_time_utc.project(time_zone_cet.as_ref())?, &date_time_cet);
            check_equal_date_time(&date_time_cet.project(time_zone_cet.as_ref())?, &date_time_cet);
            check_equal_date_time(&date_time_eet.project(time_zone_cet.as_ref())?, &date_time_cet);

            check_equal_date_time(&date_time_utc.project(time_zone_eet.as_ref())?, &date_time_eet);
            check_equal_date_time(&date_time_cet.project(time_zone_eet.as_ref())?, &date_time_eet);
            check_equal_date_time(&date_time_eet.project(time_zone_eet.as_ref())?, &date_time_eet);
        }

        Ok(())
    }

    #[test]
    fn test_date_time_leap_seconds() -> Result<()> {
        let utc_date_time = UtcDateTime::new(1972, 5, 30, 23, 59, 60, 1000)?;

        assert_eq!(UtcDateTime::from_timespec(utc_date_time.unix_time(), 1000)?, UtcDateTime::new(1972, 6, 1, 0, 0, 0, 1000)?);

        let date_time = utc_date_time.project(TimeZone::fixed(-3600)?.as_ref())?;

        let date_time_result = DateTime {
            year: 72,
            month: 5,
            month_day: 30,
            hour: 23,
            minute: 00,
            second: 00,
            local_time_type: LocalTimeType::with_ut_offset(-3600)?,
            unix_time: 78796800,
            nanoseconds: 1000,
        };

        check_equal_date_time(&date_time, &date_time_result);

        Ok(())
    }

    #[test]
    fn test_date_time_partial_eq_partial_ord() -> Result<()> {
        let time_zone_utc = TimeZone::utc();
        let time_zone_cet = TimeZone::fixed(3600)?;
        let time_zone_eet = TimeZone::fixed(7200)?;

        let utc_date_time_1 = UtcDateTime::from_timespec(1, 1)?;
        let utc_date_time_2 = UtcDateTime::from_timespec(2, 1)?;
        let utc_date_time_3 = UtcDateTime::from_timespec(3, 1)?;
        let utc_date_time_4 = UtcDateTime::from_timespec(3, 1000)?;

        let date_time_utc_1 = utc_date_time_1.project(time_zone_utc.as_ref())?;
        let date_time_utc_2 = utc_date_time_2.project(time_zone_utc.as_ref())?;
        let date_time_utc_3 = utc_date_time_3.project(time_zone_utc.as_ref())?;
        let date_time_utc_4 = utc_date_time_4.project(time_zone_utc.as_ref())?;

        let date_time_cet_1 = utc_date_time_1.project(time_zone_cet.as_ref())?;
        let date_time_cet_2 = utc_date_time_2.project(time_zone_cet.as_ref())?;
        let date_time_cet_3 = utc_date_time_3.project(time_zone_cet.as_ref())?;
        let date_time_cet_4 = utc_date_time_4.project(time_zone_cet.as_ref())?;

        let date_time_eet_1 = utc_date_time_1.project(time_zone_eet.as_ref())?;
        let date_time_eet_2 = utc_date_time_2.project(time_zone_eet.as_ref())?;
        let date_time_eet_3 = utc_date_time_3.project(time_zone_eet.as_ref())?;
        let date_time_eet_4 = utc_date_time_4.project(time_zone_eet.as_ref())?;

        assert_eq!(date_time_utc_1, date_time_cet_1);
        assert_eq!(date_time_utc_1, date_time_eet_1);

        assert_eq!(date_time_utc_2, date_time_cet_2);
        assert_eq!(date_time_utc_2, date_time_eet_2);

        assert_eq!(date_time_utc_3, date_time_cet_3);
        assert_eq!(date_time_utc_3, date_time_eet_3);

        assert_eq!(date_time_utc_4, date_time_cet_4);
        assert_eq!(date_time_utc_4, date_time_eet_4);

        assert_ne!(date_time_utc_1, date_time_utc_2);
        assert_ne!(date_time_utc_1, date_time_utc_3);
        assert_ne!(date_time_utc_1, date_time_utc_4);

        assert_eq!(date_time_utc_1.partial_cmp(&date_time_cet_1), Some(Ordering::Equal));
        assert_eq!(date_time_utc_1.partial_cmp(&date_time_eet_1), Some(Ordering::Equal));

        assert_eq!(date_time_utc_2.partial_cmp(&date_time_cet_2), Some(Ordering::Equal));
        assert_eq!(date_time_utc_2.partial_cmp(&date_time_eet_2), Some(Ordering::Equal));

        assert_eq!(date_time_utc_3.partial_cmp(&date_time_cet_3), Some(Ordering::Equal));
        assert_eq!(date_time_utc_3.partial_cmp(&date_time_eet_3), Some(Ordering::Equal));

        assert_eq!(date_time_utc_4.partial_cmp(&date_time_cet_4), Some(Ordering::Equal));
        assert_eq!(date_time_utc_4.partial_cmp(&date_time_eet_4), Some(Ordering::Equal));

        assert_eq!(date_time_utc_1.partial_cmp(&date_time_utc_2), Some(Ordering::Less));
        assert_eq!(date_time_utc_2.partial_cmp(&date_time_utc_3), Some(Ordering::Less));
        assert_eq!(date_time_utc_3.partial_cmp(&date_time_utc_4), Some(Ordering::Less));

        Ok(())
    }

    #[test]
    fn test_date_time_sync_and_send() {
        trait AssertSyncSendStatic: Sync + Send + 'static {}
        impl AssertSyncSendStatic for DateTime {}
    }

    #[test]
    fn test_utc_date_time_ord() -> Result<()> {
        let utc_date_time_1 = UtcDateTime::new(1972, 5, 30, 23, 59, 59, 1000)?;
        let utc_date_time_2 = UtcDateTime::new(1972, 5, 30, 23, 59, 60, 1000)?;
        let utc_date_time_3 = UtcDateTime::new(1972, 6, 1, 0, 0, 0, 1000)?;
        let utc_date_time_4 = UtcDateTime::new(1972, 6, 1, 0, 0, 0, 1001)?;

        assert_eq!(utc_date_time_1.cmp(&utc_date_time_1), Ordering::Equal);
        assert_eq!(utc_date_time_1.cmp(&utc_date_time_2), Ordering::Less);
        assert_eq!(utc_date_time_1.cmp(&utc_date_time_3), Ordering::Less);
        assert_eq!(utc_date_time_1.cmp(&utc_date_time_4), Ordering::Less);

        assert_eq!(utc_date_time_2.cmp(&utc_date_time_1), Ordering::Greater);
        assert_eq!(utc_date_time_2.cmp(&utc_date_time_2), Ordering::Equal);
        assert_eq!(utc_date_time_2.cmp(&utc_date_time_3), Ordering::Less);
        assert_eq!(utc_date_time_2.cmp(&utc_date_time_4), Ordering::Less);

        assert_eq!(utc_date_time_3.cmp(&utc_date_time_1), Ordering::Greater);
        assert_eq!(utc_date_time_3.cmp(&utc_date_time_2), Ordering::Greater);
        assert_eq!(utc_date_time_3.cmp(&utc_date_time_3), Ordering::Equal);
        assert_eq!(utc_date_time_3.cmp(&utc_date_time_4), Ordering::Less);

        assert_eq!(utc_date_time_4.cmp(&utc_date_time_1), Ordering::Greater);
        assert_eq!(utc_date_time_4.cmp(&utc_date_time_2), Ordering::Greater);
        assert_eq!(utc_date_time_4.cmp(&utc_date_time_3), Ordering::Greater);
        assert_eq!(utc_date_time_4.cmp(&utc_date_time_4), Ordering::Equal);

        assert_eq!(utc_date_time_1.cmp(&utc_date_time_1), utc_date_time_1.unix_time().cmp(&utc_date_time_1.unix_time()));
        assert_eq!(utc_date_time_1.cmp(&utc_date_time_2), utc_date_time_1.unix_time().cmp(&utc_date_time_2.unix_time()));
        assert_eq!(utc_date_time_1.cmp(&utc_date_time_3), utc_date_time_1.unix_time().cmp(&utc_date_time_3.unix_time()));
        assert_eq!(utc_date_time_1.cmp(&utc_date_time_4), utc_date_time_1.unix_time().cmp(&utc_date_time_4.unix_time()));

        assert_eq!(utc_date_time_2.cmp(&utc_date_time_1), utc_date_time_2.unix_time().cmp(&utc_date_time_1.unix_time()));
        assert_eq!(utc_date_time_2.cmp(&utc_date_time_2), utc_date_time_2.unix_time().cmp(&utc_date_time_2.unix_time()));

        assert_eq!(utc_date_time_3.cmp(&utc_date_time_1), utc_date_time_3.unix_time().cmp(&utc_date_time_1.unix_time()));
        assert_eq!(utc_date_time_3.cmp(&utc_date_time_3), utc_date_time_3.unix_time().cmp(&utc_date_time_3.unix_time()));

        assert_eq!(utc_date_time_4.cmp(&utc_date_time_1), utc_date_time_4.unix_time().cmp(&utc_date_time_1.unix_time()));
        assert_eq!(utc_date_time_4.cmp(&utc_date_time_4), utc_date_time_4.unix_time().cmp(&utc_date_time_4.unix_time()));

        Ok(())
    }

    #[test]
    fn test_date_time_format() -> Result<()> {
        let time_zones = [
            TimeZone::fixed(-49550)?,
            TimeZone::fixed(-5400)?,
            TimeZone::fixed(-3600)?,
            TimeZone::fixed(0)?,
            TimeZone::fixed(3600)?,
            TimeZone::fixed(5400)?,
            TimeZone::fixed(49550)?,
        ];

        let utc_date_times = [UtcDateTime::new(2000, 0, 2, 3, 4, 5, 0)?, UtcDateTime::new(2000, 0, 2, 3, 4, 5, 123_456_789)?];

        let utc_date_time_strings = ["2000-01-02T03:04:05.000000000Z", "2000-01-02T03:04:05.123456789Z"];

        let date_time_strings_list = [
            [
                "2000-01-01T13:18:15.000000000-13:45:50",
                "2000-01-02T01:34:05.000000000-01:30",
                "2000-01-02T02:04:05.000000000-01:00",
                "2000-01-02T03:04:05.000000000Z",
                "2000-01-02T04:04:05.000000000+01:00",
                "2000-01-02T04:34:05.000000000+01:30",
                "2000-01-02T16:49:55.000000000+13:45:50",
            ],
            [
                "2000-01-01T13:18:15.123456789-13:45:50",
                "2000-01-02T01:34:05.123456789-01:30",
                "2000-01-02T02:04:05.123456789-01:00",
                "2000-01-02T03:04:05.123456789Z",
                "2000-01-02T04:04:05.123456789+01:00",
                "2000-01-02T04:34:05.123456789+01:30",
                "2000-01-02T16:49:55.123456789+13:45:50",
            ],
        ];

        for ((utc_date_time, utc_date_time_string), date_time_strings) in utc_date_times.iter().zip(utc_date_time_strings).zip(date_time_strings_list) {
            for (time_zone, date_time_string) in time_zones.iter().zip(date_time_strings) {
                assert_eq!(utc_date_time.to_string(), utc_date_time_string);
                assert_eq!(utc_date_time.project(time_zone.as_ref())?.to_string(), date_time_string);
            }
        }

        Ok(())
    }

    #[test]
    fn test_date_time_overflow() -> Result<()> {
        assert!(matches!(UtcDateTime::new(i32::MIN, 0, 1, 0, 0, 0, 0), Err(DateTimeError(_))));
        assert!(matches!(UtcDateTime::new(i32::MAX, 11, 31, 23, 59, 60, 0), Err(DateTimeError(_))));

        assert!(matches!(UtcDateTime::from_timespec(UtcDateTime::MIN_UNIX_TIME - 1, 0), Err(OutOfRangeError(_))));
        assert!(matches!(UtcDateTime::from_timespec(UtcDateTime::MAX_UNIX_TIME + 1, 0), Err(OutOfRangeError(_))));

        assert!(matches!(UtcDateTime::from_timespec(UtcDateTime::MIN_UNIX_TIME, 0)?.project(TimeZone::fixed(-1)?.as_ref()), Err(ProjectDateTimeError(_))));
        assert!(matches!(UtcDateTime::from_timespec(UtcDateTime::MAX_UNIX_TIME, 0)?.project(TimeZone::fixed(1)?.as_ref()), Err(ProjectDateTimeError(_))));

        assert!(matches!(DateTime::from_timespec(i64::MIN, 0, TimeZone::fixed(-1)?.as_ref()), Err(ProjectDateTimeError(_))));
        assert!(matches!(DateTime::from_timespec(i64::MAX, 0, TimeZone::fixed(1)?.as_ref()), Err(ProjectDateTimeError(_))));

        Ok(())
    }

    #[test]
    fn test_week_day() {
        assert_eq!(week_day(70, 0, 1), 4);

        assert_eq!(week_day(100, 0, 1), 6);
        assert_eq!(week_day(100, 1, 28), 1);
        assert_eq!(week_day(100, 1, 29), 2);
        assert_eq!(week_day(100, 2, 1), 3);
        assert_eq!(week_day(100, 11, 31), 0);

        assert_eq!(week_day(101, 0, 1), 1);
        assert_eq!(week_day(101, 1, 28), 3);
        assert_eq!(week_day(101, 2, 1), 4);
        assert_eq!(week_day(101, 11, 31), 1);
    }

    #[test]
    fn test_year_day() {
        assert_eq!(year_day(100, 0, 1), 0);
        assert_eq!(year_day(100, 1, 28), 58);
        assert_eq!(year_day(100, 1, 29), 59);
        assert_eq!(year_day(100, 2, 1), 60);
        assert_eq!(year_day(100, 11, 31), 365);

        assert_eq!(year_day(101, 0, 1), 0);
        assert_eq!(year_day(101, 1, 28), 58);
        assert_eq!(year_day(101, 2, 1), 59);
        assert_eq!(year_day(101, 11, 31), 364);
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

    #[test]
    fn test_const() -> Result<()> {
        macro_rules! unwrap {
            ($x:expr) => {
                match $x {
                    Ok(x) => x,
                    Err(error) => panic!("{}", error.0),
                }
            };
        }

        macro_rules! to_const {
            ($type:ty, $x:expr) => {{
                const TMP: $type = $x;
                TMP
            }};
        }

        const TIME_ZONE_REF: TimeZoneRef = unwrap!(TimeZoneRef::new(
            &[
                Transition::new(-2334101314, 1),
                Transition::new(-1157283000, 2),
                Transition::new(-1155436200, 1),
                Transition::new(-880198200, 3),
                Transition::new(-769395600, 4),
                Transition::new(-765376200, 1),
                Transition::new(-712150200, 5),
            ],
            to_const!(
                &[LocalTimeType],
                &[
                    unwrap!(LocalTimeType::new(-37886, false, Some(b"LMT"))),
                    unwrap!(LocalTimeType::new(-37800, false, Some(b"HST"))),
                    unwrap!(LocalTimeType::new(-34200, true, Some(b"HDT"))),
                    unwrap!(LocalTimeType::new(-34200, true, Some(b"HWT"))),
                    unwrap!(LocalTimeType::new(-34200, true, Some(b"HPT"))),
                    unwrap!(LocalTimeType::new(-36000, false, Some(b"HST"))),
                ]
            ),
            &[
                LeapSecond::new(78796800, 1),
                LeapSecond::new(94694401, 2),
                LeapSecond::new(126230402, 3),
                LeapSecond::new(157766403, 4),
                LeapSecond::new(189302404, 5),
                LeapSecond::new(220924805, 6),
            ],
            to_const!(
                &Option<TransitionRule>,
                &Some(TransitionRule::Alternate(unwrap!(AlternateTime::new(
                    unwrap!(LocalTimeType::new(-36000, false, Some(b"HST"))),
                    unwrap!(LocalTimeType::new(-34200, true, Some(b"HPT"))),
                    RuleDay::MonthWeekDay(unwrap!(MonthWeekDay::new(10, 5, 0))),
                    93600,
                    RuleDay::MonthWeekDay(unwrap!(MonthWeekDay::new(3, 4, 4))),
                    7200,
                ))))
            ),
        ));

        const UTC: TimeZoneRef = TimeZoneRef::utc();

        const UNIX_EPOCH: UtcDateTime = unwrap!(UtcDateTime::from_timespec(0, 0));
        const UTC_DATE_TIME: UtcDateTime = unwrap!(UtcDateTime::new(2000, 0, 1, 0, 0, 0, 1000));

        const DATE_TIME_1: DateTime = unwrap!(UTC_DATE_TIME.project(TIME_ZONE_REF));
        const DATE_TIME_2: DateTime = unwrap!(DATE_TIME_1.project(UTC));

        const LOCAL_TIME_TYPE_1: &LocalTimeType = DATE_TIME_1.local_time_type();
        const LOCAL_TIME_TYPE_2: &LocalTimeType = DATE_TIME_2.local_time_type();

        assert_eq!(UNIX_EPOCH.unix_time(), 0);
        assert_eq!(DATE_TIME_2.unix_time(), UTC_DATE_TIME.unix_time());
        assert_eq!(DATE_TIME_2.nanoseconds(), UTC_DATE_TIME.nanoseconds());

        let date_time = UTC_DATE_TIME.project(TIME_ZONE_REF)?;
        assert_eq!(date_time.local_time_type().time_zone_designation(), LOCAL_TIME_TYPE_1.time_zone_designation());

        let date_time_1 = DateTime::from_timespec(UTC_DATE_TIME.unix_time(), 1000, TIME_ZONE_REF)?;
        let date_time_2 = date_time_1.project(UTC)?;

        assert_eq!(date_time, DATE_TIME_1);
        assert_eq!(date_time_1, DATE_TIME_1);
        assert_eq!(date_time_2, DATE_TIME_2);

        let local_time_type_1 = date_time_1.local_time_type();
        let local_time_type_2 = date_time_2.local_time_type();

        assert_eq!(local_time_type_1.ut_offset(), LOCAL_TIME_TYPE_1.ut_offset());
        assert_eq!(local_time_type_1.is_dst(), LOCAL_TIME_TYPE_1.is_dst());
        assert_eq!(local_time_type_1.time_zone_designation(), LOCAL_TIME_TYPE_1.time_zone_designation());

        assert_eq!(local_time_type_2.ut_offset(), LOCAL_TIME_TYPE_2.ut_offset());
        assert_eq!(local_time_type_2.is_dst(), LOCAL_TIME_TYPE_2.is_dst());
        assert_eq!(local_time_type_2.time_zone_designation(), LOCAL_TIME_TYPE_2.time_zone_designation());

        Ok(())
    }
}
