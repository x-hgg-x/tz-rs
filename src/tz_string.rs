use crate::cursor::Cursor;
use crate::{LocalTimeType, RuleDay, TransitionRule};

use std::error;
use std::fmt;
use std::io;
use std::num::ParseIntError;
use std::str::{self, FromStr, Utf8Error};

#[derive(Debug)]
pub enum TzStringError {
    Utf8Error(Utf8Error),
    ParseIntError(ParseIntError),
    IoError(io::Error),
    InvalidTzString,
    UnsupportedTzString,
}

impl fmt::Display for TzStringError {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Self::Utf8Error(error) => error.fmt(f),
            Self::ParseIntError(error) => error.fmt(f),
            Self::IoError(error) => error.fmt(f),
            Self::InvalidTzString => write!(f, "invalid TZ string"),
            Self::UnsupportedTzString => write!(f, "unsupported TZ string"),
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

fn parse_int<T: FromStr<Err = ParseIntError>>(bytes: &[u8]) -> Result<T, TzStringError> {
    Ok(str::from_utf8(bytes)?.parse()?)
}

fn parse_time_zone_designation<'a>(cursor: &mut Cursor<'a>) -> Result<&'a [u8], TzStringError> {
    let unquoted = if cursor.remaining().get(0) == Some(&b'<') {
        cursor.read_exact(1)?;
        let unquoted = cursor.read_until(|&x| x == b'>')?;
        cursor.read_exact(1)?;

        if !unquoted.iter().all(|&x| x.is_ascii_alphanumeric() || x == b'+' || x == b'-') {
            return Err(TzStringError::InvalidTzString);
        }

        unquoted
    } else {
        cursor.read_while(u8::is_ascii_alphabetic)?
    };

    if unquoted.len() < 3 {
        return Err(TzStringError::InvalidTzString);
    }

    Ok(unquoted)
}

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

fn parse_offset(cursor: &mut Cursor) -> Result<i32, TzStringError> {
    let (sign, hour, minute, second) = parse_signed_hhmmss(cursor)?;

    if !((0..=24).contains(&hour) && (0..=59).contains(&minute) && (0..=59).contains(&second)) {
        return Err(TzStringError::InvalidTzString);
    }

    Ok(sign * (hour * 3600 + minute * 60 + second))
}

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

            if !((1..=12).contains(&month) && (1..=5).contains(&week) && (0..=6).contains(&week_day)) {
                return Err(TzStringError::InvalidTzString);
            }

            Ok(RuleDay::MonthWeekDay { month, week, week_day })
        }
        _ => Ok(RuleDay::Julian0WithLeap(parse_int(cursor.read_while(u8::is_ascii_digit)?)?)),
    }
}

fn parse_rule_time(cursor: &mut Cursor) -> Result<i32, TzStringError> {
    let (hour, minute, second) = parse_hhmmss(cursor)?;

    if !((0..=24).contains(&hour) && (0..=59).contains(&minute) && (0..=59).contains(&second)) {
        return Err(TzStringError::InvalidTzString);
    }

    Ok(hour * 3600 + minute * 60 + second)
}

fn parse_rule_time_extended(cursor: &mut Cursor) -> Result<i32, TzStringError> {
    let (sign, hour, minute, second) = parse_signed_hhmmss(cursor)?;

    if !((-167..=167).contains(&hour) && (0..=59).contains(&minute) && (0..=59).contains(&second)) {
        return Err(TzStringError::InvalidTzString);
    }

    Ok(sign * (hour * 3600 + minute * 60 + second))
}

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
        None => return Err(TzStringError::UnsupportedTzString),
    };

    if cursor.is_empty() {
        return Err(TzStringError::UnsupportedTzString);
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
