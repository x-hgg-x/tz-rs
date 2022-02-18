//! Some useful constants.

/// Number of seconds in one minute
pub const SECONDS_PER_MINUTE: i64 = 60;
/// Number of minutes in one hour
pub const MINUTES_PER_HOUR: i64 = 60;
/// Number of hours in one day
pub const HOURS_PER_DAY: i64 = 24;
/// Number of seconds in one hour
pub const SECONDS_PER_HOUR: i64 = 3600;
/// Number of seconds in one day
pub const SECONDS_PER_DAY: i64 = 86400;
/// Number of days in one week
pub const DAYS_PER_WEEK: i64 = 7;
/// Number of months in one year
pub const MONTHS_PER_YEAR: i64 = 12;
/// Number of days in a normal year
pub const DAYS_PER_NORMAL_YEAR: i64 = 365;
/// Number of days in 4 years (including 1 leap year)
pub const DAYS_PER_4_YEARS: i64 = DAYS_PER_NORMAL_YEAR * 4 + 1;
/// Number of days in 100 years (including 24 leap years)
pub const DAYS_PER_100_YEARS: i64 = DAYS_PER_NORMAL_YEAR * 100 + 24;
/// Number of days in 400 years (including 97 leap years)
pub const DAYS_PER_400_YEARS: i64 = DAYS_PER_NORMAL_YEAR * 400 + 97;

/// Month days in a normal year
pub const DAY_IN_MONTHS_NORMAL_YEAR: [i64; 12] = [31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31];
/// Cumulated month days in a normal year
pub const CUM_DAY_IN_MONTHS_NORMAL_YEAR: [i64; 12] = [0, 31, 59, 90, 120, 151, 181, 212, 243, 273, 304, 334];

/// Unix time at `2000-03-01T00:00:00Z` (Wednesday)
pub const UNIX_OFFSET_SECS: i64 = 951868800;
/// Number of cumulated days in January and February in a normal year
pub const OFFSET_DAYS: i64 = 31 + 28;
/// Number of years between `2000` and `1900`
pub const OFFSET_YEARS: i64 = 100;
/// Month days in a leap year from March
pub const DAY_IN_MONTHS_LEAP_YEAR_FROM_MARCH: [i64; 12] = [31, 30, 31, 30, 31, 31, 30, 31, 30, 31, 31, 29];
