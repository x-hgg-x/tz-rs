//! Error types.

use std::array::TryFromSliceError;
use std::error;
use std::fmt;
use std::io;
use std::num::ParseIntError;
use std::num::TryFromIntError;
use std::result;
use std::str::Utf8Error;
use std::time::SystemTimeError;

/// Unified error type for parsing a TZ string
#[non_exhaustive]
#[derive(Debug)]
pub enum TzStringError {
    /// UTF-8 error
    Utf8Error(Utf8Error),
    /// Integer parsing error
    ParseIntError(ParseIntError),
    /// I/O error
    IoError(io::Error),
    /// Invalid TZ string
    InvalidTzString(&'static str),
    /// Unsupported TZ string
    UnsupportedTzString(&'static str),
}

impl fmt::Display for TzStringError {
    fn fmt(&self, f: &mut fmt::Formatter) -> result::Result<(), fmt::Error> {
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

/// Unified error type for parsing a TZif file
#[non_exhaustive]
#[derive(Debug)]
pub enum TzFileError {
    /// Conversion from slice to array error
    TryFromSliceError(TryFromSliceError),
    /// I/O error
    IoError(io::Error),
    /// Empty vector error
    EmptyVectorError,
    /// Unified error for parsing a TZ string
    TzStringError(TzStringError),
    /// Invalid TZif file
    InvalidTzFile(&'static str),
    /// Unsupported TZif file
    UnsupportedTzFile(&'static str),
}

impl fmt::Display for TzFileError {
    fn fmt(&self, f: &mut fmt::Formatter) -> result::Result<(), fmt::Error> {
        match self {
            Self::TryFromSliceError(error) => error.fmt(f),
            Self::IoError(error) => error.fmt(f),
            Self::EmptyVectorError => write!(f, "vector must be non-empty"),
            Self::TzStringError(error) => error.fmt(f),
            Self::InvalidTzFile(error) => write!(f, "invalid TZ file: {}", error),
            Self::UnsupportedTzFile(error) => write!(f, "unsupported TZ file: {}", error),
        }
    }
}

impl error::Error for TzFileError {}

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

/// Unified error type for everything in the crate
#[non_exhaustive]
#[derive(Debug)]
pub enum TzError {
    /// UTF-8 error
    Utf8Error(Utf8Error),
    /// Integer conversion error
    ConversionError(TryFromIntError),
    /// Conversion from slice to array error
    TryFromSliceError(TryFromSliceError),
    /// I/O error
    IoError(io::Error),
    /// System time error
    SystemTimeError(SystemTimeError),
    /// Unified error for parsing a TZif file
    TzFileError(TzFileError),
    /// Unified error for parsing a TZ string
    TzStringError(TzStringError),
    /// Date time is invalid
    InvalidDateTime(&'static str),
    /// Local time type is invalid
    InvalidLocalTimeType(&'static str),
    /// Transition rule is invalid
    InvalidTransitionRule(&'static str),
    /// Time zone is invalid
    InvalidTimeZone(&'static str),
    /// No available local time type
    NoLocalTimeType,
}

impl fmt::Display for TzError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Utf8Error(error) => error.fmt(f),
            Self::ConversionError(error) => error.fmt(f),
            Self::TryFromSliceError(error) => error.fmt(f),
            Self::IoError(error) => error.fmt(f),
            Self::SystemTimeError(error) => error.fmt(f),
            Self::TzFileError(error) => error.fmt(f),
            Self::TzStringError(error) => error.fmt(f),
            Self::InvalidDateTime(error) => write!(f, "invalid date time: {}", error),
            Self::InvalidLocalTimeType(error) => write!(f, "invalid local time type: {}", error),
            Self::InvalidTransitionRule(error) => write!(f, "invalid transition rule: {}", error),
            Self::InvalidTimeZone(error) => write!(f, "invalid time zone: {}", error),
            Self::NoLocalTimeType => write!(f, "no local time type is available for the specified timestamp"),
        }
    }
}

impl error::Error for TzError {}

impl From<Utf8Error> for TzError {
    fn from(error: Utf8Error) -> Self {
        Self::Utf8Error(error)
    }
}

impl From<TryFromIntError> for TzError {
    fn from(error: TryFromIntError) -> Self {
        Self::ConversionError(error)
    }
}

impl From<TryFromSliceError> for TzError {
    fn from(error: TryFromSliceError) -> Self {
        Self::TryFromSliceError(error)
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

/// Alias for [`std::result::Result`] with the crate unified error
pub type Result<T> = result::Result<T, TzError>;
