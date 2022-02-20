//! Functions used for parsing a TZ string.

use crate::utils::*;
use crate::{LocalTimeType, RuleDay, TransitionRule};

use std::error;
use std::fmt;
use std::io;
use std::num::ParseIntError;
use std::str::{self, FromStr, Utf8Error};

/// Unified error type for parsing a TZ string
#[non_exhaustive]
#[derive(Debug)]
pub enum TzStringError {
    /// Utf-8 error
    Utf8Error(Utf8Error),
    // Integer parsing error
    ParseIntError(ParseIntError),
    /// I/O error
    IoError(io::Error),
    /// Invalid TZ string
    InvalidTzString(&'static str),
    /// Unsupported TZ string
    UnsupportedTzString(&'static str),
}

impl fmt::Display for TzStringError {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Self::Utf8Error(error) => error.fmt(f),
            Self::ParseIntError(error) => error.fmt(f),
            Self::IoError(error) => error.fmt(f),
            Self::InvalidTzString(error) => write!(f, "invalid TZ string: {}", error),
            Self::UnsupportedTzString(error) => write!(f, "unsupported TZ string: {}", error),
        }
    }
}

impl error::Error for TzStringError {}

impl From<Utf8Error> for TzStringError {
    fn from(error: Utf8Error) -> Self {
        Self::Utf8Error(error)
    }
}

impl From<ParseIntError> for TzStringError {
    fn from(error: ParseIntError) -> Self {
        Self::ParseIntError(error)
    }
}

impl From<io::Error> for TzStringError {
    fn from(error: io::Error) -> Self {
        Self::IoError(error)
    }
}

/// Parse integer from a slice of bytes
fn parse_int<T: FromStr<Err = ParseIntError>>(bytes: &[u8]) -> Result<T, TzStringError> {
    Ok(str::from_utf8(bytes)?.parse()?)
}

/// Parse time zone designation
fn parse_time_zone_designation<'a>(cursor: &mut Cursor<'a>) -> Result<&'a [u8], TzStringError> {
    let unquoted = if cursor.remaining().get(0) == Some(&b'<') {
        cursor.read_exact(1)?;
        let unquoted = cursor.read_until(|&x| x == b'>')?;
        cursor.read_exact(1)?;

        if !unquoted.iter().all(|&x| x.is_ascii_alphanumeric() || x == b'+' || x == b'-') {
            return Err(TzStringError::InvalidTzString("invalid characters in time zone designation"));
        }

        unquoted
    } else {
        cursor.read_while(u8::is_ascii_alphabetic)?
    };

    if unquoted.len() < 3 {
        return Err(TzStringError::InvalidTzString("time zone designation must have at least 3 characters"));
    }

    Ok(unquoted)
}

/// Parse hours, minutes and seconds
fn parse_hhmmss(cursor: &mut Cursor) -> Result<(i32, i32, i32), TzStringError> {
    let hour = parse_int(cursor.read_while(u8::is_ascii_digit)?)?;

    let mut minute = 0;
    let mut second = 0;

    if cursor.read_optional_tag(b":")? {
        minute = parse_int(cursor.read_while(u8::is_ascii_digit)?)?;

        if cursor.read_optional_tag(b":")? {
            second = parse_int(cursor.read_while(u8::is_ascii_digit)?)?;
        }
    }

    Ok((hour, minute, second))
}

/// Parse signed hours, minutes and seconds
fn parse_signed_hhmmss(cursor: &mut Cursor) -> Result<(i32, i32, i32, i32), TzStringError> {
    let mut sign = 1;
    if let Some(&c @ (b'+' | b'-')) = cursor.remaining().get(0) {
        cursor.read_exact(1)?;
        if c == b'-' {
            sign = -1;
        }
    }

    let (hour, minute, second) = parse_hhmmss(cursor)?;
    Ok((sign, hour, minute, second))
}

/// Parse time zone offset
fn parse_offset(cursor: &mut Cursor) -> Result<i32, TzStringError> {
    let (sign, hour, minute, second) = parse_signed_hhmmss(cursor)?;

    if !(0..=24).contains(&hour) {
        return Err(TzStringError::InvalidTzString("invalid offset hour"));
    }
    if !(0..=59).contains(&minute) {
        return Err(TzStringError::InvalidTzString("invalid offset minute"));
    }
    if !(0..=59).contains(&second) {
        return Err(TzStringError::InvalidTzString("invalid offset second"));
    }

    Ok(sign * (hour * 3600 + minute * 60 + second))
}

/// Parse transition rule day
fn parse_rule_day(cursor: &mut Cursor) -> Result<RuleDay, TzStringError> {
    match cursor.remaining().get(0) {
        Some(b'J') => {
            cursor.read_exact(1)?;
            Ok(RuleDay::Julian1WithoutLeap(parse_int(cursor.read_while(u8::is_ascii_digit)?)?))
        }
        Some(b'M') => {
            cursor.read_exact(1)?;

            let month = parse_int(cursor.read_while(u8::is_ascii_digit)?)?;
            cursor.read_tag(b".")?;
            let week = parse_int(cursor.read_while(u8::is_ascii_digit)?)?;
            cursor.read_tag(b".")?;
            let week_day = parse_int(cursor.read_while(u8::is_ascii_digit)?)?;

            if !(1..=12).contains(&month) {
                return Err(TzStringError::InvalidTzString("invalid rule day month"));
            }
            if !(1..=5).contains(&week) {
                return Err(TzStringError::InvalidTzString("invalid rule day week"));
            }
            if !(0..=6).contains(&week_day) {
                return Err(TzStringError::InvalidTzString("invalid rule day week day"));
            }

            Ok(RuleDay::MonthWeekDay { month, week, week_day })
        }
        _ => Ok(RuleDay::Julian0WithLeap(parse_int(cursor.read_while(u8::is_ascii_digit)?)?)),
    }
}

/// Parse transition rule time
fn parse_rule_time(cursor: &mut Cursor) -> Result<i32, TzStringError> {
    let (hour, minute, second) = parse_hhmmss(cursor)?;

    if !(0..=24).contains(&hour) {
        return Err(TzStringError::InvalidTzString("invalid day time hour"));
    }
    if !(0..=59).contains(&minute) {
        return Err(TzStringError::InvalidTzString("invalid day time minute"));
    }
    if !(0..=59).contains(&second) {
        return Err(TzStringError::InvalidTzString("invalid day time second"));
    }

    Ok(hour * 3600 + minute * 60 + second)
}

/// Parse transition rule time with TZ string extensions
fn parse_rule_time_extended(cursor: &mut Cursor) -> Result<i32, TzStringError> {
    let (sign, hour, minute, second) = parse_signed_hhmmss(cursor)?;

    if !(-167..=167).contains(&hour) {
        return Err(TzStringError::InvalidTzString("invalid day time hour"));
    }
    if !(0..=59).contains(&minute) {
        return Err(TzStringError::InvalidTzString("invalid day time minute"));
    }
    if !(0..=59).contains(&second) {
        return Err(TzStringError::InvalidTzString("invalid day time second"));
    }

    Ok(sign * (hour * 3600 + minute * 60 + second))
}

/// Parse transition rule
fn parse_rule_block(cursor: &mut Cursor, use_string_extensions: bool) -> Result<(RuleDay, i32), TzStringError> {
    let date = parse_rule_day(cursor)?;

    let time = if cursor.read_optional_tag(b"/")? {
        if use_string_extensions {
            parse_rule_time_extended(cursor)?
        } else {
            parse_rule_time(cursor)?
        }
    } else {
        2 * 3600
    };

    Ok((date, time))
}

/// Parse a POSIX TZ string containing a time zone description, as described in [the POSIX documentation of the `TZ` environment variable](https://pubs.opengroup.org/onlinepubs/9699919799/basedefs/V1_chap08.html).
///
/// TZ string extensions from [RFC 8536](https://datatracker.ietf.org/doc/html/rfc8536#section-3.3.1) may be used.
///
pub(crate) fn parse_posix_tz(tz_string: &[u8], use_string_extensions: bool) -> Result<TransitionRule, TzStringError> {
    let mut cursor = Cursor::new(tz_string);

    let std_time_zone = str::from_utf8(parse_time_zone_designation(&mut cursor)?)?.to_owned();
    let std_offset = parse_offset(&mut cursor)?;

    if cursor.is_empty() {
        return Ok(TransitionRule::Fixed(LocalTimeType { ut_offset: -std_offset, is_dst: false, time_zone_designation: std_time_zone }));
    }

    let dst_time_zone = str::from_utf8(parse_time_zone_designation(&mut cursor)?)?.to_owned();

    let dst_offset = match cursor.remaining().get(0) {
        Some(&b',') => std_offset - 3600,
        Some(_) => parse_offset(&mut cursor)?,
        None => return Err(TzStringError::UnsupportedTzString("DST start and end rules must be provided")),
    };

    if cursor.is_empty() {
        return Err(TzStringError::UnsupportedTzString("DST start and end rules must be provided"));
    }

    cursor.read_tag(b",")?;
    let (dst_start, dst_start_time) = parse_rule_block(&mut cursor, use_string_extensions)?;

    cursor.read_tag(b",")?;
    let (dst_end, dst_end_time) = parse_rule_block(&mut cursor, use_string_extensions)?;

    Ok(TransitionRule::Alternate {
        std: LocalTimeType { ut_offset: -std_offset, is_dst: false, time_zone_designation: std_time_zone },
        dst: LocalTimeType { ut_offset: -dst_offset, is_dst: true, time_zone_designation: dst_time_zone },
        dst_start,
        dst_start_time,
        dst_end,
        dst_end_time,
    })
}

#[cfg(test)]
mod test {
    use super::*;

    use crate::TzError;

    #[test]
    fn test_no_dst() -> Result<(), TzError> {
        let tz_string = b"HST10";

        let transition_rule = parse_posix_tz(tz_string, false)?;
        let transition_rule_result = TransitionRule::Fixed(LocalTimeType { ut_offset: -36000, is_dst: false, time_zone_designation: "HST".to_owned() });

        assert_eq!(transition_rule, transition_rule_result);
        assert_eq!(transition_rule.find_local_time_type(0)?.ut_offset(), -36000);

        Ok(())
    }

    #[test]
    fn test_quoted() -> Result<(), TzError> {
        let tz_string = b"<-03>+3<+03>-3,J1,J365";

        let transition_rule = parse_posix_tz(tz_string, false)?;

        let transition_rule_result = TransitionRule::Alternate {
            std: LocalTimeType { ut_offset: -10800, is_dst: false, time_zone_designation: "-03".to_owned() },
            dst: LocalTimeType { ut_offset: 10800, is_dst: true, time_zone_designation: "+03".to_owned() },
            dst_start: RuleDay::Julian1WithoutLeap(1),
            dst_start_time: 7200,
            dst_end: RuleDay::Julian1WithoutLeap(365),
            dst_end_time: 7200,
        };

        assert_eq!(transition_rule, transition_rule_result);

        Ok(())
    }

    #[test]
    fn test_full() -> Result<(), TzError> {
        let tz_string = b"NZST-12:00:00NZDT-13:00:00,M10.1.0/02:00:00,M3.3.0/02:00:00";

        let transition_rule = parse_posix_tz(tz_string, false)?;

        let transition_rule_result = TransitionRule::Alternate {
            std: LocalTimeType { ut_offset: 43200, is_dst: false, time_zone_designation: "NZST".to_owned() },
            dst: LocalTimeType { ut_offset: 46800, is_dst: true, time_zone_designation: "NZDT".to_owned() },
            dst_start: RuleDay::MonthWeekDay { month: 10, week: 1, week_day: 0 },
            dst_start_time: 7200,
            dst_end: RuleDay::MonthWeekDay { month: 3, week: 3, week_day: 0 },
            dst_end_time: 7200,
        };

        assert_eq!(transition_rule, transition_rule_result);

        assert_eq!(transition_rule.find_local_time_type(953384399)?.ut_offset(), 46800);
        assert_eq!(transition_rule.find_local_time_type(953384400)?.ut_offset(), 43200);
        assert_eq!(transition_rule.find_local_time_type(970322399)?.ut_offset(), 43200);
        assert_eq!(transition_rule.find_local_time_type(970322400)?.ut_offset(), 46800);

        Ok(())
    }

    #[test]
    fn test_negative_dst() -> Result<(), TzError> {
        let tz_string = b"IST-1GMT0,M10.5.0,M3.5.0/1";

        let transition_rule = parse_posix_tz(tz_string, false)?;

        let transition_rule_result = TransitionRule::Alternate {
            std: LocalTimeType { ut_offset: 3600, is_dst: false, time_zone_designation: "IST".to_owned() },
            dst: LocalTimeType { ut_offset: 0, is_dst: true, time_zone_designation: "GMT".to_owned() },
            dst_start: RuleDay::MonthWeekDay { month: 10, week: 5, week_day: 0 },
            dst_start_time: 7200,
            dst_end: RuleDay::MonthWeekDay { month: 3, week: 5, week_day: 0 },
            dst_end_time: 3600,
        };

        assert_eq!(transition_rule, transition_rule_result);

        assert_eq!(transition_rule.find_local_time_type(954032399)?.ut_offset(), 0);
        assert_eq!(transition_rule.find_local_time_type(954032400)?.ut_offset(), 3600);
        assert_eq!(transition_rule.find_local_time_type(972781199)?.ut_offset(), 3600);
        assert_eq!(transition_rule.find_local_time_type(972781200)?.ut_offset(), 0);

        Ok(())
    }

    #[test]
    fn test_negative_hour() -> Result<(), TzError> {
        let tz_string = b"<-03>3<-02>,M3.5.0/-2,M10.5.0/-1";

        assert!(parse_posix_tz(tz_string, false).is_err());

        let transition_rule = parse_posix_tz(tz_string, true)?;

        let transition_rule_result = TransitionRule::Alternate {
            std: LocalTimeType { ut_offset: -10800, is_dst: false, time_zone_designation: "-03".to_owned() },
            dst: LocalTimeType { ut_offset: -7200, is_dst: true, time_zone_designation: "-02".to_owned() },
            dst_start: RuleDay::MonthWeekDay { month: 3, week: 5, week_day: 0 },
            dst_start_time: -7200,
            dst_end: RuleDay::MonthWeekDay { month: 10, week: 5, week_day: 0 },
            dst_end_time: -3600,
        };

        assert_eq!(transition_rule, transition_rule_result);

        assert_eq!(transition_rule.find_local_time_type(954032399)?.ut_offset(), -10800);
        assert_eq!(transition_rule.find_local_time_type(954032400)?.ut_offset(), -7200);
        assert_eq!(transition_rule.find_local_time_type(972781199)?.ut_offset(), -7200);
        assert_eq!(transition_rule.find_local_time_type(972781200)?.ut_offset(), -10800);

        Ok(())
    }

    #[test]
    fn test_all_year_dst() -> Result<(), TzError> {
        let tz_string = b"EST5EDT,0/0,J365/25";

        assert!(parse_posix_tz(tz_string, false).is_err());

        let transition_rule = parse_posix_tz(tz_string, true)?;

        let transition_rule_result = TransitionRule::Alternate {
            std: LocalTimeType { ut_offset: -18000, is_dst: false, time_zone_designation: "EST".to_owned() },
            dst: LocalTimeType { ut_offset: -14400, is_dst: true, time_zone_designation: "EDT".to_owned() },
            dst_start: RuleDay::Julian0WithLeap(0),
            dst_start_time: 0,
            dst_end: RuleDay::Julian1WithoutLeap(365),
            dst_end_time: 90000,
        };

        assert_eq!(transition_rule, transition_rule_result);

        assert_eq!(transition_rule.find_local_time_type(946702799)?.ut_offset(), -14400);
        assert_eq!(transition_rule.find_local_time_type(946702800)?.ut_offset(), -14400);

        Ok(())
    }

    #[test]
    fn test_error() -> Result<(), TzError> {
        assert!(matches!(parse_posix_tz(b"IST-1GMT0", false), Err(TzStringError::UnsupportedTzString(_))));
        assert!(matches!(parse_posix_tz(b"EET-2EEST", false), Err(TzStringError::UnsupportedTzString(_))));

        Ok(())
    }
}
