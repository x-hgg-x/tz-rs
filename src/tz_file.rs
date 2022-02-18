//! Functions used for parsing a TZif file.

use crate::cursor::Cursor;
use crate::tz_string::{self, TzStringError};
use crate::{LeapSecond, LocalTimeType, TimeZone, Transition, TransitionRule, TzError};

use std::array::TryFromSliceError;
use std::error;
use std::fmt;
use std::fs::File;
use std::io;
use std::iter;
use std::str::{self, Utf8Error};

/// Unified error type for parsing a TZif file
#[non_exhaustive]
#[derive(Debug)]
pub enum TzFileError {
    /// Utf-8 error
    Utf8Error(Utf8Error),
    /// Conversion from slice to array error
    TryFromSliceError(TryFromSliceError),
    /// I/O error
    IoError(io::Error),
    /// Unified error for parsing a TZ string
    TzStringError(TzStringError),
    /// Invalid TZif file
    InvalidTzFile(&'static str),
    /// Unsupported TZif file
    UnsupportedTzFile(&'static str),
}

impl fmt::Display for TzFileError {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Self::Utf8Error(error) => error.fmt(f),
            Self::TryFromSliceError(error) => error.fmt(f),
            Self::IoError(error) => error.fmt(f),
            Self::TzStringError(error) => error.fmt(f),
            Self::InvalidTzFile(error) => write!(f, "invalid TZ file: {}", error),
            Self::UnsupportedTzFile(error) => write!(f, "unsupported TZ file: {}", error),
        }
    }
}

impl error::Error for TzFileError {}

impl From<Utf8Error> for TzFileError {
    fn from(error: Utf8Error) -> Self {
        Self::Utf8Error(error)
    }
}

impl From<TryFromSliceError> for TzFileError {
    fn from(error: TryFromSliceError) -> Self {
        Self::TryFromSliceError(error)
    }
}

impl From<io::Error> for TzFileError {
    fn from(error: io::Error) -> Self {
        Self::IoError(error)
    }
}

impl From<TzStringError> for TzFileError {
    fn from(error: TzStringError) -> Self {
        Self::TzStringError(error)
    }
}

/// TZif version
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
enum Version {
    /// Version 1
    V1,
    /// Version 2
    V2,
    /// Version 3
    V3,
}

/// TZif header
#[derive(Debug)]
struct Header {
    /// TZif version
    version: Version,
    /// Number of UT/local indicators
    ut_local_count: usize,
    /// Number of standard/wall indicators
    std_wall_count: usize,
    /// Number of leap-second records
    leap_count: usize,
    /// Number of transition times
    transition_count: usize,
    /// Number of local time type records
    type_count: usize,
    /// Number of time zone designations bytes
    char_count: usize,
}

/// Parse TZif header
fn parse_header(cursor: &mut Cursor) -> Result<Header, TzFileError> {
    let magic = cursor.read_exact(4)?;
    if magic != *b"TZif" {
        return Err(TzFileError::InvalidTzFile("invalid magic number"));
    }

    let version = match cursor.read_exact(1)? {
        [0x00] => Version::V1,
        [0x32] => Version::V2,
        [0x33] => Version::V3,
        _ => return Err(TzFileError::UnsupportedTzFile("unsupported TZif version")),
    };

    cursor.read_exact(15)?;

    let ut_local_count = u32::from_be_bytes(cursor.read_exact(4)?.try_into()?);
    let std_wall_count = u32::from_be_bytes(cursor.read_exact(4)?.try_into()?);
    let leap_count = u32::from_be_bytes(cursor.read_exact(4)?.try_into()?);
    let transition_count = u32::from_be_bytes(cursor.read_exact(4)?.try_into()?);
    let type_count = u32::from_be_bytes(cursor.read_exact(4)?.try_into()?);
    let char_count = u32::from_be_bytes(cursor.read_exact(4)?.try_into()?);

    if !(type_count != 0 && char_count != 0 && (ut_local_count == 0 || ut_local_count == type_count) && (std_wall_count == 0 || std_wall_count == type_count)) {
        return Err(TzFileError::InvalidTzFile("invalid header"));
    }

    Ok(Header {
        version,
        ut_local_count: ut_local_count as usize,
        std_wall_count: std_wall_count as usize,
        leap_count: leap_count as usize,
        transition_count: transition_count as usize,
        type_count: type_count as usize,
        char_count: char_count as usize,
    })
}

/// TZif data blocks
struct DataBlock<'a> {
    /// Time size in bytes
    time_size: usize,
    /// Transition times data block
    transition_times: &'a [u8],
    /// Transition types data block
    transition_types: &'a [u8],
    /// Local time types data block
    local_time_types: &'a [u8],
    /// Time zone designations data block
    time_zone_designations: &'a [u8],
    /// Leap seconds data block
    leap_seconds: &'a [u8],
    /// UT/local indicators data block
    std_walls: &'a [u8],
    /// Standard/wall indicators data block
    ut_locals: &'a [u8],
}

impl<'a> DataBlock<'a> {
    /// Read TZif data blocks
    fn new(cursor: &mut Cursor<'a>, header: &Header, version: Version) -> Result<Self, TzFileError> {
        let time_size = match version {
            Version::V1 => 4,
            Version::V2 | Version::V3 => 8,
        };

        Ok(Self {
            time_size,
            transition_times: cursor.read_exact(header.transition_count * time_size)?,
            transition_types: cursor.read_exact(header.transition_count)?,
            local_time_types: cursor.read_exact(header.type_count * 6)?,
            time_zone_designations: cursor.read_exact(header.char_count)?,
            leap_seconds: cursor.read_exact(header.leap_count * (time_size + 4))?,
            std_walls: cursor.read_exact(header.std_wall_count)?,
            ut_locals: cursor.read_exact(header.ut_local_count)?,
        })
    }

    /// Parse time values
    fn parse_time(&self, arr: &[u8], version: Version) -> Result<i64, TzFileError> {
        Ok(match version {
            Version::V1 => i32::from_be_bytes(arr.try_into()?).into(),
            Version::V2 | Version::V3 => i64::from_be_bytes(arr.try_into()?),
        })
    }

    /// Parse time zone data
    fn parse(&self, header: &Header) -> Result<TimeZone, TzFileError> {
        let mut transitions = Vec::with_capacity(header.transition_count);
        for (arr_time, &local_time_type_index) in self.transition_times.chunks_exact(self.time_size).zip(self.transition_types) {
            let unix_leap_time = self.parse_time(&arr_time[0..self.time_size], header.version)?;

            let local_time_type_index = local_time_type_index as usize;
            if local_time_type_index >= header.type_count {
                return Err(TzFileError::InvalidTzFile("invalid local time type index"));
            }

            transitions.push(Transition { unix_leap_time, local_time_type_index });
        }

        if !transitions.windows(2).all(|x| x[0].unix_leap_time < x[1].unix_leap_time) {
            return Err(TzFileError::InvalidTzFile("invalid transition"));
        }

        let mut local_time_types = Vec::with_capacity(header.type_count);
        for arr in self.local_time_types.chunks_exact(6) {
            let ut_offset = i32::from_be_bytes(arr[0..4].try_into()?);
            if ut_offset == i32::MIN {
                return Err(TzFileError::InvalidTzFile("invalid UTC offset"));
            }

            let is_dst = match arr[4] {
                0 => false,
                1 => true,
                _ => return Err(TzFileError::InvalidTzFile("invalid DST indicator")),
            };

            let char_index = arr[5] as usize;
            if char_index >= header.char_count {
                return Err(TzFileError::InvalidTzFile("invalid time zone designation char index"));
            }

            let time_zone_designation = match self.time_zone_designations[char_index..].iter().position(|&c| c == b'\0') {
                Some(position) => str::from_utf8(&self.time_zone_designations[char_index..char_index + position])?.to_owned(),
                None => return Err(TzFileError::InvalidTzFile("invalid time zone designation char index")),
            };

            local_time_types.push(LocalTimeType { ut_offset, is_dst, time_zone_designation });
        }

        let mut leap_seconds = Vec::with_capacity(header.leap_count);
        for arr in self.leap_seconds.chunks_exact(self.time_size + 4) {
            leap_seconds.push(LeapSecond {
                unix_leap_time: self.parse_time(&arr[0..self.time_size], header.version)?,
                correction: i32::from_be_bytes(arr[self.time_size..self.time_size + 4].try_into()?),
            });
        }

        if let Some(leap_second) = leap_seconds.get(0) {
            if !(leap_second.unix_leap_time >= 0 && leap_second.correction.abs() == 1) {
                return Err(TzFileError::InvalidTzFile("invalid leap second"));
            }
        }

        if !leap_seconds.windows(2).all(|x| x[1].unix_leap_time >= x[0].unix_leap_time + 2419199 && (x[1].correction - x[0].correction).abs() == 1) {
            return Err(TzFileError::InvalidTzFile("invalid leap second"));
        }

        let std_walls_iter = self.std_walls.iter().copied().chain(iter::repeat(0));
        let ut_locals_iter = self.ut_locals.iter().copied().chain(iter::repeat(0));
        for (std_wall, ut_local) in std_walls_iter.zip(ut_locals_iter).take(header.type_count) {
            if !matches!((std_wall, ut_local), (0, 0) | (1, 0) | (1, 1)) {
                return Err(TzFileError::InvalidTzFile("invalid couple of standard/wall and UT/local indicators"));
            }
        }

        Ok(TimeZone { transitions, local_time_types, leap_seconds, extra_rule: None })
    }
}

/// Parse TZif footer
fn parse_footer(footer: &[u8], use_string_extensions: bool) -> Result<Option<TransitionRule>, TzFileError> {
    let footer = str::from_utf8(footer)?;
    if !(footer.starts_with('\n') && footer.ends_with('\n')) {
        return Err(TzFileError::InvalidTzFile("invalid footer"));
    }

    let tz_string = footer.trim_matches(|c: char| c.is_ascii_whitespace());
    if tz_string.starts_with(':') || tz_string.contains('\0') {
        return Err(TzFileError::InvalidTzFile("invalid footer"));
    }

    if !tz_string.is_empty() {
        Ok(Some(tz_string::parse_posix_tz(tz_string.as_bytes(), use_string_extensions)).transpose()?)
    } else {
        Ok(None)
    }
}

/// Parse TZif file as described in [RFC 8536](https://datatracker.ietf.org/doc/html/rfc8536)
pub(crate) fn parse_tz_file(bytes: &[u8]) -> Result<TimeZone, TzError> {
    let mut cursor = Cursor::new(bytes);

    let header = parse_header(&mut cursor)?;

    match header.version {
        Version::V1 => {
            let data_block = DataBlock::new(&mut cursor, &header, header.version)?;

            if !cursor.is_empty() {
                return Err(TzFileError::InvalidTzFile("remaining data after end of TZif v1 data block").into());
            }

            Ok(data_block.parse(&header)?)
        }
        Version::V2 | Version::V3 => {
            // Skip v1 data block
            DataBlock::new(&mut cursor, &header, Version::V1)?;

            let header = parse_header(&mut cursor)?;
            let data_block = DataBlock::new(&mut cursor, &header, header.version)?;

            let mut time_zone = data_block.parse(&header)?;

            let footer = cursor.read_exact(cursor.remaining().len())?;

            if !cursor.is_empty() {
                return Err(TzFileError::InvalidTzFile("remaining data after end of TZif v2/v3 footer").into());
            }

            time_zone.extra_rule = parse_footer(footer, header.version == Version::V3)?;

            // Check extra rule
            if let (Some(extra_rule), Some(last_transition)) = (&time_zone.extra_rule, time_zone.transitions.last()) {
                let last_local_time_type = &time_zone.local_time_types[last_transition.local_time_type_index];
                let rule_local_time_type = extra_rule.find_local_time_type(time_zone.unix_leap_time_to_unix_time(last_transition.unix_leap_time))?;

                if last_local_time_type != rule_local_time_type {
                    return Err(TzFileError::InvalidTzFile("extra transition rule is inconsistent with the last transition").into());
                }
            }

            Ok(time_zone)
        }
    }
}

/// Open the TZif file corresponding to a TZ string
pub(crate) fn get_tz_file(tz_string: &str) -> Result<File, TzFileError> {
    // Possible system timezone directories
    const ZONE_INFO_DIRECTORIES: [&str; 3] = ["/usr/share/zoneinfo", "/share/zoneinfo", "/etc/zoneinfo"];

    if tz_string.starts_with('/') {
        Ok(File::open(tz_string)?)
    } else {
        for folder in ZONE_INFO_DIRECTORIES {
            if let Ok(file) = File::open(format!("{}/{}", folder, tz_string)) {
                return Ok(file);
            }
        }
        Err(TzFileError::IoError(io::ErrorKind::NotFound.into()))
    }
}
