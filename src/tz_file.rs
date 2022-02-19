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
                Some(position) => str::from_utf8(&self.time_zone_designations[char_index..char_index + position])?.into(),
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
    // Don't check system timezone directories on non-UNIX platforms
    #[cfg(not(unix))]
    return Ok(File::open(tz_string)?);

    #[cfg(unix)]
    {
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
}

#[cfg(test)]
mod test {
    use super::*;

    use crate::RuleDay;

    #[test]
    fn test_v1_file_with_leap_seconds() -> Result<(), TzError> {
        let bytes = b"TZif\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\x01\0\0\0\x01\0\0\0\x1b\0\0\0\0\0\0\0\x01\0\0\0\x04\0\0\0\0\0\0UTC\0\x04\xb2\x58\0\0\0\0\x01\x05\xa4\xec\x01\0\0\0\x02\x07\x86\x1f\x82\0\0\0\x03\x09\x67\x53\x03\0\0\0\x04\x0b\x48\x86\x84\0\0\0\x05\x0d\x2b\x0b\x85\0\0\0\x06\x0f\x0c\x3f\x06\0\0\0\x07\x10\xed\x72\x87\0\0\0\x08\x12\xce\xa6\x08\0\0\0\x09\x15\x9f\xca\x89\0\0\0\x0a\x17\x80\xfe\x0a\0\0\0\x0b\x19\x62\x31\x8b\0\0\0\x0c\x1d\x25\xea\x0c\0\0\0\x0d\x21\xda\xe5\x0d\0\0\0\x0e\x25\x9e\x9d\x8e\0\0\0\x0f\x27\x7f\xd1\x0f\0\0\0\x10\x2a\x50\xf5\x90\0\0\0\x11\x2c\x32\x29\x11\0\0\0\x12\x2e\x13\x5c\x92\0\0\0\x13\x30\xe7\x24\x13\0\0\0\x14\x33\xb8\x48\x94\0\0\0\x15\x36\x8c\x10\x15\0\0\0\x16\x43\xb7\x1b\x96\0\0\0\x17\x49\x5c\x07\x97\0\0\0\x18\x4f\xef\x93\x18\0\0\0\x19\x55\x93\x2d\x99\0\0\0\x1a\x58\x68\x46\x9a\0\0\0\x1b\0\0";

        let time_zone = parse_tz_file(bytes)?;

        let time_zone_result = TimeZone {
            transitions: Vec::new(),
            local_time_types: vec![LocalTimeType { ut_offset: 0, is_dst: false, time_zone_designation: "UTC".into() }],
            leap_seconds: vec![
                LeapSecond { unix_leap_time: 78796800, correction: 1 },
                LeapSecond { unix_leap_time: 94694401, correction: 2 },
                LeapSecond { unix_leap_time: 126230402, correction: 3 },
                LeapSecond { unix_leap_time: 157766403, correction: 4 },
                LeapSecond { unix_leap_time: 189302404, correction: 5 },
                LeapSecond { unix_leap_time: 220924805, correction: 6 },
                LeapSecond { unix_leap_time: 252460806, correction: 7 },
                LeapSecond { unix_leap_time: 283996807, correction: 8 },
                LeapSecond { unix_leap_time: 315532808, correction: 9 },
                LeapSecond { unix_leap_time: 362793609, correction: 10 },
                LeapSecond { unix_leap_time: 394329610, correction: 11 },
                LeapSecond { unix_leap_time: 425865611, correction: 12 },
                LeapSecond { unix_leap_time: 489024012, correction: 13 },
                LeapSecond { unix_leap_time: 567993613, correction: 14 },
                LeapSecond { unix_leap_time: 631152014, correction: 15 },
                LeapSecond { unix_leap_time: 662688015, correction: 16 },
                LeapSecond { unix_leap_time: 709948816, correction: 17 },
                LeapSecond { unix_leap_time: 741484817, correction: 18 },
                LeapSecond { unix_leap_time: 773020818, correction: 19 },
                LeapSecond { unix_leap_time: 820454419, correction: 20 },
                LeapSecond { unix_leap_time: 867715220, correction: 21 },
                LeapSecond { unix_leap_time: 915148821, correction: 22 },
                LeapSecond { unix_leap_time: 1136073622, correction: 23 },
                LeapSecond { unix_leap_time: 1230768023, correction: 24 },
                LeapSecond { unix_leap_time: 1341100824, correction: 25 },
                LeapSecond { unix_leap_time: 1435708825, correction: 26 },
                LeapSecond { unix_leap_time: 1483228826, correction: 27 },
            ],
            extra_rule: None,
        };

        assert_eq!(time_zone, time_zone_result);

        assert_eq!(time_zone.unix_leap_time_to_unix_time(1136073621), 1136073599);
        assert_eq!(time_zone.unix_leap_time_to_unix_time(1136073622), 1136073600);
        assert_eq!(time_zone.unix_leap_time_to_unix_time(1136073623), 1136073600);
        assert_eq!(time_zone.unix_leap_time_to_unix_time(1136073624), 1136073601);

        assert_eq!(time_zone.unix_time_to_unix_leap_time(1136073599), 1136073621);
        assert_eq!(time_zone.unix_time_to_unix_leap_time(1136073600), 1136073623);
        assert_eq!(time_zone.unix_time_to_unix_leap_time(1136073601), 1136073624);

        Ok(())
    }

    #[test]
    fn test_v2_file() -> Result<(), TzError> {
        let bytes = b"TZif2\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\x06\0\0\0\x06\0\0\0\0\0\0\0\x07\0\0\0\x06\0\0\0\x14\x80\0\0\0\xbb\x05\x43\x48\xbb\x21\x71\x58\xcb\x89\x3d\xc8\xd2\x23\xf4\x70\xd2\x61\x49\x38\xd5\x8d\x73\x48\x01\x02\x01\x03\x04\x01\x05\xff\xff\x6c\x02\0\0\xff\xff\x6c\x58\0\x04\xff\xff\x7a\x68\x01\x08\xff\xff\x7a\x68\x01\x0c\xff\xff\x7a\x68\x01\x10\xff\xff\x73\x60\0\x04LMT\0HST\0HDT\0HWT\0HPT\0\0\0\0\0\x01\0\0\0\0\0\x01\0TZif2\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\x06\0\0\0\x06\0\0\0\0\0\0\0\x07\0\0\0\x06\0\0\0\x14\xff\xff\xff\xff\x74\xe0\x70\xbe\xff\xff\xff\xff\xbb\x05\x43\x48\xff\xff\xff\xff\xbb\x21\x71\x58\xff\xff\xff\xff\xcb\x89\x3d\xc8\xff\xff\xff\xff\xd2\x23\xf4\x70\xff\xff\xff\xff\xd2\x61\x49\x38\xff\xff\xff\xff\xd5\x8d\x73\x48\x01\x02\x01\x03\x04\x01\x05\xff\xff\x6c\x02\0\0\xff\xff\x6c\x58\0\x04\xff\xff\x7a\x68\x01\x08\xff\xff\x7a\x68\x01\x0c\xff\xff\x7a\x68\x01\x10\xff\xff\x73\x60\0\x04LMT\0HST\0HDT\0HWT\0HPT\0\0\0\0\0\x01\0\0\0\0\0\x01\0\x0aHST10\x0a";

        let time_zone = parse_tz_file(bytes)?;

        let time_zone_result = TimeZone {
            transitions: vec![
                Transition { unix_leap_time: -2334101314, local_time_type_index: 1 },
                Transition { unix_leap_time: -1157283000, local_time_type_index: 2 },
                Transition { unix_leap_time: -1155436200, local_time_type_index: 1 },
                Transition { unix_leap_time: -880198200, local_time_type_index: 3 },
                Transition { unix_leap_time: -769395600, local_time_type_index: 4 },
                Transition { unix_leap_time: -765376200, local_time_type_index: 1 },
                Transition { unix_leap_time: -712150200, local_time_type_index: 5 },
            ],
            local_time_types: vec![
                LocalTimeType { ut_offset: -37886, is_dst: false, time_zone_designation: "LMT".into() },
                LocalTimeType { ut_offset: -37800, is_dst: false, time_zone_designation: "HST".into() },
                LocalTimeType { ut_offset: -34200, is_dst: true, time_zone_designation: "HDT".into() },
                LocalTimeType { ut_offset: -34200, is_dst: true, time_zone_designation: "HWT".into() },
                LocalTimeType { ut_offset: -34200, is_dst: true, time_zone_designation: "HPT".into() },
                LocalTimeType { ut_offset: -36000, is_dst: false, time_zone_designation: "HST".into() },
            ],
            leap_seconds: Vec::new(),
            extra_rule: Some(TransitionRule::Fixed(LocalTimeType { ut_offset: -36000, is_dst: false, time_zone_designation: "HST".into() })),
        };

        assert_eq!(time_zone, time_zone_result);

        assert_eq!(*time_zone.find_local_time_type(-1156939200)?, LocalTimeType { ut_offset: -34200, is_dst: true, time_zone_designation: "HDT".into() });
        assert_eq!(*time_zone.find_local_time_type(1546300800)?, LocalTimeType { ut_offset: -36000, is_dst: false, time_zone_designation: "HST".into() });

        Ok(())
    }

    #[test]
    fn test_v3_file() -> Result<(), TzError> {
        let bytes = b"TZif3\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\x01\0\0\0\x04\0\0\x1c\x20\0\0IST\0TZif3\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\x01\0\0\0\x01\0\0\0\0\0\0\0\x01\0\0\0\x01\0\0\0\x04\0\0\0\0\x7f\xe8\x17\x80\0\0\0\x1c\x20\0\0IST\0\x01\x01\x0aIST-2IDT,M3.4.4/26,M10.5.0\x0a";

        let time_zone = parse_tz_file(bytes)?;

        let time_zone_result = TimeZone {
            transitions: vec![Transition { unix_leap_time: 2145916800, local_time_type_index: 0 }],
            local_time_types: vec![LocalTimeType { ut_offset: 7200, is_dst: false, time_zone_designation: "IST".into() }],
            leap_seconds: Vec::new(),
            extra_rule: Some(TransitionRule::Alternate {
                std: LocalTimeType { ut_offset: 7200, is_dst: false, time_zone_designation: "IST".into() },
                dst: LocalTimeType { ut_offset: 10800, is_dst: true, time_zone_designation: "IDT".into() },
                dst_start: RuleDay::MonthWeekDay { month: 3, week: 4, week_day: 4 },
                dst_start_time: 93600,
                dst_end: RuleDay::MonthWeekDay { month: 10, week: 5, week_day: 0 },
                dst_end_time: 7200,
            }),
        };

        assert_eq!(time_zone, time_zone_result);

        Ok(())
    }
}
