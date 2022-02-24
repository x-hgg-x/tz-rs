//! Types related to a date time.

mod unix_time;

use crate::error::*;
use crate::{LocalTimeType, TimeZone};
pub use self::unix_time::*;

use std::cmp::Ordering;
use std::time::SystemTime;

/// UTC date time exprimed in the [proleptic gregorian calendar](https://en.wikipedia.org/wiki/Proleptic_Gregorian_calendar)
#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd)]
pub struct UtcDateTime<U: UnixTime = i64> {
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
    nanoseconds: U::Nanoseconds,
}

impl<U: UnixTime> UtcDateTime<U> {
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
    pub fn new(full_year: i32, month: u8, month_day: u8, hour: u8, minute: u8, second: u8, nanoseconds: U::Nanoseconds) -> Result<Self> {
        use crate::constants::*;

        let year = full_year - 1900;

        if !(0..=11).contains(&month) {
            return Err(TzError::InvalidDateTime("invalid month"));
        }
        if !(1..=31).contains(&month_day) {
            return Err(TzError::InvalidDateTime("invalid month day"));
        }
        if !(0..=23).contains(&hour) {
            return Err(TzError::InvalidDateTime("invalid hour"));
        }
        if !(0..=59).contains(&minute) {
            return Err(TzError::InvalidDateTime("invalid minute"));
        }
        if !(0..=60).contains(&second) {
            return Err(TzError::InvalidDateTime("invalid second"));
        }
        U::validate_nanoseconds(nanoseconds)?;

        let leap = is_leap_year(year) as i64;

        let mut day_in_month = DAY_IN_MONTHS_NORMAL_YEAR[month as usize];
        if month == 1 {
            day_in_month += leap;
        }

        if month_day as i64 > day_in_month {
            return Err(TzError::InvalidDateTime("invalid month day"));
        }

        Ok(Self { year, month, month_day, hour, minute, second, nanoseconds })
    }

    /// Construct a UTC date time from a Unix time in seconds
    pub fn from_unix_time(unix_time: U) -> Result<Self> {
        use crate::constants::*;

        let seconds = unix_time.get_seconds()?.checked_sub(UNIX_OFFSET_SECS).ok_or(TzError::InvalidDateTime("invalid nanoseconds"))?;
        let nanoseconds = unix_time.get_nanoseconds();
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
            year: year.try_into()?,
            month: month.try_into()?,
            month_day: month_day.try_into()?,
            hour: hour.try_into()?,
            minute: minute.try_into()?,
            second: second.try_into()?,
            nanoseconds,
        })
    }

    /// Returns the current UTC date time
    pub fn now() -> Result<Self> {
        Self::from_unix_time(U::from_duration(&SystemTime::now().duration_since(SystemTime::UNIX_EPOCH)?)?)
    }

    /// Project the UTC date time into a time zone.
    ///
    /// Leap seconds are not preserved.
    ///
    pub fn project(&self, time_zone: &TimeZone) -> Result<DateTime<U>> {
        let unix_time = self.unix_time();
        let local_time_type = time_zone.find_local_time_type(unix_time.get_seconds()?)?;

        let utc_date_time_with_offset = UtcDateTime::from_unix_time(unix_time.add_seconds(local_time_type.ut_offset() as i64)?)?;

        Ok(DateTime {
            year: utc_date_time_with_offset.year,
            month: utc_date_time_with_offset.month,
            month_day: utc_date_time_with_offset.month_day,
            hour: utc_date_time_with_offset.hour,
            minute: utc_date_time_with_offset.minute,
            second: utc_date_time_with_offset.second,
            local_time_type: local_time_type.clone(),
            unix_time,
        })
    }

    /// Returns the Unix time in seconds associated to the UTC date time
    pub fn unix_time(&self) -> U {
        use crate::constants::*;

        let mut result = days_since_unix_epoch(self.year, self.month.into(), self.month_day.into());
        result *= HOURS_PER_DAY;
        result += self.hour as i64;
        result *= MINUTES_PER_HOUR;
        result += self.minute as i64;
        result *= SECONDS_PER_MINUTE;
        result += self.second as i64;

        U::from_seconds(result, self.nanoseconds)
    }
}

/// Date time associated to a local time type, exprimed in the [proleptic gregorian calendar](https://en.wikipedia.org/wiki/Proleptic_Gregorian_calendar)
#[derive(Debug, Clone)]
pub struct DateTime<U: UnixTime = i64> {
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
    unix_time: U,
}

impl<U: UnixTime> PartialEq for DateTime<U> {
    fn eq(&self, other: &Self) -> bool {
        self.unix_time == other.unix_time
    }
}

impl<U: UnixTime> PartialOrd for DateTime<U> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.unix_time.partial_cmp(&other.unix_time)
    }
}

impl<U: UnixTime> DateTime<U> {
    /// Returns the current date time associated to the specified time zone
    pub fn now(time_zone: &TimeZone) -> Result<Self> {
        let unix_time = U::from_duration(&SystemTime::now().duration_since(SystemTime::UNIX_EPOCH)?)?;
        let local_time_type = time_zone.find_local_time_type(unix_time.get_seconds()?)?;

        let utc_date_time_with_offset = UtcDateTime::from_unix_time(unix_time.add_seconds(local_time_type.ut_offset() as i64)?)?;

        Ok(DateTime {
            year: utc_date_time_with_offset.year,
            month: utc_date_time_with_offset.month,
            month_day: utc_date_time_with_offset.month_day,
            hour: utc_date_time_with_offset.hour,
            minute: utc_date_time_with_offset.minute,
            second: utc_date_time_with_offset.second,
            local_time_type: local_time_type.clone(),
            unix_time,
        })
    }

    /// Project the date time into another time zone.
    ///
    /// Leap seconds are not preserved.
    ///
    pub fn project(&self, time_zone: &TimeZone) -> Result<Self> {
        let local_time_type = time_zone.find_local_time_type(self.unix_time.get_seconds()?)?;

        let utc_date_time_with_offset = UtcDateTime::from_unix_time(
            self.unix_time.add_seconds(local_time_type.ut_offset() as i64)?
        )?;

        Ok(DateTime {
            year: utc_date_time_with_offset.year,
            month: utc_date_time_with_offset.month,
            month_day: utc_date_time_with_offset.month_day,
            hour: utc_date_time_with_offset.hour,
            minute: utc_date_time_with_offset.minute,
            second: utc_date_time_with_offset.second,
            local_time_type: local_time_type.clone(),
            unix_time: self.unix_time,
        })
    }

    /// Returns local time type
    pub fn local_time_type(&self) -> &LocalTimeType {
        &self.local_time_type
    }

    /// Returns UTC Unix time in seconds
    pub fn unix_time(&self) -> U {
        self.unix_time
    }
}

/// Macro for implementing date time getters
macro_rules! impl_datetime {
    ($struct_name:ident) => {
        impl<U: UnixTime> $struct_name::<U> {
            /// Returns year
            pub fn full_year(&self) -> i32 {
                self.year + 1900
            }

            /// Returns years since 1900
            pub fn year(&self) -> i32 {
                self.year
            }

            /// Returns month in `[0, 11]`
            pub fn month(&self) -> u8 {
                self.month
            }

            /// Returns day of the month in `[1, 31]`
            pub fn month_day(&self) -> u8 {
                self.month_day
            }

            /// Returns hours since midnight in `[0, 23]`
            pub fn hour(&self) -> u8 {
                self.hour
            }

            /// Returns minutes in `[0, 59]`
            pub fn minute(&self) -> u8 {
                self.minute
            }

            /// Returns seconds in `[0, 60]`, with a possible leap second
            pub fn second(&self) -> u8 {
                self.second
            }

            /// Returns days since Sunday in `[0, 6]`
            pub fn week_day(&self) -> u8 {
                week_day(self.year, self.month.into(), self.month_day.into())
            }

            /// Returns days since January 1 in `[0, 365]`
            pub fn year_day(&self) -> u16 {
                year_day(self.year, self.month.into(), self.month_day.into())
            }
        }
    };
}

impl_datetime!(UtcDateTime);
impl_datetime!(DateTime);

/// Compute the number of days since Sunday in `[0, 6]`
///
/// ## Inputs
///
/// * `year`: Years since 1900
/// * `month`: Month in `[0, 11]`
/// * `month_day`: Day of the month in `[1, 31]`
///
fn week_day(year: i32, month: usize, month_day: i64) -> u8 {
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
fn year_day(year: i32, month: usize, month_day: i64) -> u16 {
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
pub(crate) fn is_leap_year(year: i32) -> bool {
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
pub(crate) fn days_since_unix_epoch(year: i32, month: usize, month_day: i64) -> i64 {
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

#[cfg(test)]
mod test {
    use super::*;

    fn check_equal_date_time<U: UnixTime>(x: &DateTime<U>, y: &DateTime<U>) {
        assert_eq!(x.year, y.year);
        assert_eq!(x.month, y.month);
        assert_eq!(x.month_day, y.month_day);
        assert_eq!(x.hour, y.hour);
        assert_eq!(x.minute, y.minute);
        assert_eq!(x.second, y.second);
        assert_eq!(x.local_time_type, y.local_time_type);
        assert_eq!(x.unix_time, y.unix_time);
    }

    #[test]
    fn test_date_time() -> Result<()> {
        let time_zone_utc = TimeZone::utc();
        let utc = LocalTimeType::utc();

        let time_zone_cet = TimeZone::fixed(3600);
        let cet = LocalTimeType::with_ut_offset(3600);

        let time_zone_eet = TimeZone::fixed(7200);
        let eet = LocalTimeType::with_ut_offset(7200);

        assert_eq!(DateTime::<i64>::now(&time_zone_utc)?.local_time_type().ut_offset(), 0);
        assert_eq!(DateTime::<i64>::now(&time_zone_cet)?.local_time_type().ut_offset(), 3600);
        assert_eq!(DateTime::<i64>::now(&time_zone_eet)?.local_time_type().ut_offset(), 7200);

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

        let date_times_utc = [
            DateTime { year: -2901, month: 2, month_day: 1, hour: 12, minute: 0, second: 0, local_time_type: utc.clone(), unix_time: -93750523200 },
            DateTime { year: -300, month: 1, month_day: 29, hour: 12, minute: 0, second: 0, local_time_type: utc.clone(), unix_time: -11670955200 },
            DateTime { year: -300, month: 2, month_day: 1, hour: 12, minute: 0, second: 0, local_time_type: utc.clone(), unix_time: -11670868800 },
            DateTime { year: -200, month: 2, month_day: 1, hour: 12, minute: 0, second: 0, local_time_type: utc.clone(), unix_time: -8515195200 },
            DateTime { year: -199, month: 2, month_day: 1, hour: 12, minute: 0, second: 0, local_time_type: utc.clone(), unix_time: -8483659200 },
            DateTime { year: -196, month: 1, month_day: 29, hour: 12, minute: 0, second: 0, local_time_type: utc.clone(), unix_time: -8389051200 },
            DateTime { year: -196, month: 2, month_day: 1, hour: 12, minute: 0, second: 0, local_time_type: utc.clone(), unix_time: -8388964800 },
            DateTime { year: 100, month: 1, month_day: 29, hour: 12, minute: 0, second: 0, local_time_type: utc.clone(), unix_time: 951825600 },
            DateTime { year: 100, month: 2, month_day: 1, hour: 12, minute: 0, second: 0, local_time_type: utc.clone(), unix_time: 951912000 },
            DateTime { year: 101, month: 2, month_day: 1, hour: 12, minute: 0, second: 0, local_time_type: utc.clone(), unix_time: 983448000 },
            DateTime { year: 104, month: 1, month_day: 29, hour: 12, minute: 0, second: 0, local_time_type: utc.clone(), unix_time: 1078056000 },
            DateTime { year: 104, month: 2, month_day: 1, hour: 12, minute: 0, second: 0, local_time_type: utc.clone(), unix_time: 1078142400 },
            DateTime { year: 200, month: 2, month_day: 1, hour: 12, minute: 0, second: 0, local_time_type: utc.clone(), unix_time: 4107585600 },
            DateTime { year: 1101, month: 2, month_day: 1, hour: 12, minute: 0, second: 0, local_time_type: utc, unix_time: 32540356800 },
        ];

        let date_times_cet = [
            DateTime { year: -2901, month: 2, month_day: 1, hour: 13, minute: 0, second: 0, local_time_type: cet.clone(), unix_time: -93750523200 },
            DateTime { year: -300, month: 1, month_day: 29, hour: 13, minute: 0, second: 0, local_time_type: cet.clone(), unix_time: -11670955200 },
            DateTime { year: -300, month: 2, month_day: 1, hour: 13, minute: 0, second: 0, local_time_type: cet.clone(), unix_time: -11670868800 },
            DateTime { year: -200, month: 2, month_day: 1, hour: 13, minute: 0, second: 0, local_time_type: cet.clone(), unix_time: -8515195200 },
            DateTime { year: -199, month: 2, month_day: 1, hour: 13, minute: 0, second: 0, local_time_type: cet.clone(), unix_time: -8483659200 },
            DateTime { year: -196, month: 1, month_day: 29, hour: 13, minute: 0, second: 0, local_time_type: cet.clone(), unix_time: -8389051200 },
            DateTime { year: -196, month: 2, month_day: 1, hour: 13, minute: 0, second: 0, local_time_type: cet.clone(), unix_time: -8388964800 },
            DateTime { year: 100, month: 1, month_day: 29, hour: 13, minute: 0, second: 0, local_time_type: cet.clone(), unix_time: 951825600 },
            DateTime { year: 100, month: 2, month_day: 1, hour: 13, minute: 0, second: 0, local_time_type: cet.clone(), unix_time: 951912000 },
            DateTime { year: 101, month: 2, month_day: 1, hour: 13, minute: 0, second: 0, local_time_type: cet.clone(), unix_time: 983448000 },
            DateTime { year: 104, month: 1, month_day: 29, hour: 13, minute: 0, second: 0, local_time_type: cet.clone(), unix_time: 1078056000 },
            DateTime { year: 104, month: 2, month_day: 1, hour: 13, minute: 0, second: 0, local_time_type: cet.clone(), unix_time: 1078142400 },
            DateTime { year: 200, month: 2, month_day: 1, hour: 13, minute: 0, second: 0, local_time_type: cet.clone(), unix_time: 4107585600 },
            DateTime { year: 1101, month: 2, month_day: 1, hour: 13, minute: 0, second: 0, local_time_type: cet, unix_time: 32540356800 },
        ];

        let date_times_eet = [
            DateTime { year: -2901, month: 2, month_day: 1, hour: 14, minute: 0, second: 0, local_time_type: eet.clone(), unix_time: -93750523200 },
            DateTime { year: -300, month: 1, month_day: 29, hour: 14, minute: 0, second: 0, local_time_type: eet.clone(), unix_time: -11670955200 },
            DateTime { year: -300, month: 2, month_day: 1, hour: 14, minute: 0, second: 0, local_time_type: eet.clone(), unix_time: -11670868800 },
            DateTime { year: -200, month: 2, month_day: 1, hour: 14, minute: 0, second: 0, local_time_type: eet.clone(), unix_time: -8515195200 },
            DateTime { year: -199, month: 2, month_day: 1, hour: 14, minute: 0, second: 0, local_time_type: eet.clone(), unix_time: -8483659200 },
            DateTime { year: -196, month: 1, month_day: 29, hour: 14, minute: 0, second: 0, local_time_type: eet.clone(), unix_time: -8389051200 },
            DateTime { year: -196, month: 2, month_day: 1, hour: 14, minute: 0, second: 0, local_time_type: eet.clone(), unix_time: -8388964800 },
            DateTime { year: 100, month: 1, month_day: 29, hour: 14, minute: 0, second: 0, local_time_type: eet.clone(), unix_time: 951825600 },
            DateTime { year: 100, month: 2, month_day: 1, hour: 14, minute: 0, second: 0, local_time_type: eet.clone(), unix_time: 951912000 },
            DateTime { year: 101, month: 2, month_day: 1, hour: 14, minute: 0, second: 0, local_time_type: eet.clone(), unix_time: 983448000 },
            DateTime { year: 104, month: 1, month_day: 29, hour: 14, minute: 0, second: 0, local_time_type: eet.clone(), unix_time: 1078056000 },
            DateTime { year: 104, month: 2, month_day: 1, hour: 14, minute: 0, second: 0, local_time_type: eet.clone(), unix_time: 1078142400 },
            DateTime { year: 200, month: 2, month_day: 1, hour: 14, minute: 0, second: 0, local_time_type: eet.clone(), unix_time: 4107585600 },
            DateTime { year: 1101, month: 2, month_day: 1, hour: 14, minute: 0, second: 0, local_time_type: eet, unix_time: 32540356800 },
        ];

        for (((unix_time, date_time_utc), date_time_cet), date_time_eet) in unix_times.into_iter().zip(date_times_utc).zip(date_times_cet).zip(date_times_eet) {
            let utc_date_time = UtcDateTime::from_unix_time(unix_time)?;

            assert_eq!(utc_date_time.full_year(), date_time_utc.full_year());
            assert_eq!(utc_date_time.year(), date_time_utc.year());
            assert_eq!(utc_date_time.month(), date_time_utc.month());
            assert_eq!(utc_date_time.month_day(), date_time_utc.month_day());
            assert_eq!(utc_date_time.hour(), date_time_utc.hour());
            assert_eq!(utc_date_time.minute(), date_time_utc.minute());
            assert_eq!(utc_date_time.second(), date_time_utc.second());

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
        let utc_date_time = UtcDateTime::new(1972, 5, 30, 23, 59, 60, ())?;
        let date_time = utc_date_time.project(&TimeZone::fixed(-3600))?;

        let date_time_result = DateTime {
            year: 72,
            month: 5,
            month_day: 30,
            hour: 23,
            minute: 00,
            second: 00,
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
        impl AssertSyncSendStatic for DateTime::<i64> {}
        impl AssertSyncSendStatic for DateTime::<f64> {}
    }

    #[test]
    fn test_utc_date_time_ord() -> Result<()> {
        let utc_date_time_1 = UtcDateTime::<i64>::new(1972, 5, 30, 23, 59, 59, ())?;
        let utc_date_time_2 = UtcDateTime::<i64>::new(1972, 5, 30, 23, 59, 60, ())?;
        let utc_date_time_3 = UtcDateTime::<i64>::new(1972, 6, 1, 0, 0, 0, ())?;

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
}
