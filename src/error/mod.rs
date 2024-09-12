//! Error types.

use core::error::Error;
use core::fmt;

/// Parsing error types.
#[cfg(feature = "alloc")]
mod parse {
    use super::*;

    use alloc::boxed::Box;
    use core::num::ParseIntError;
    use core::str::Utf8Error;

    /// Parse data error
    #[non_exhaustive]
    #[derive(Debug)]
    pub enum ParseDataError {
        /// Unexpected end of data
        UnexpectedEof,
        /// Invalid data
        InvalidData,
    }

    impl fmt::Display for ParseDataError {
        fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
            match self {
                Self::UnexpectedEof => f.write_str("unexpected end of data"),
                Self::InvalidData => f.write_str("invalid data"),
            }
        }
    }

    impl Error for ParseDataError {}

    /// Unified error type for parsing a TZ string
    #[non_exhaustive]
    #[derive(Debug)]
    pub enum TzStringError {
        /// UTF-8 error
        Utf8(Utf8Error),
        /// Integer parsing error
        ParseInt(ParseIntError),
        /// Parse data error
        ParseData(ParseDataError),
        /// Invalid TZ string
        InvalidTzString(&'static str),
        /// Unsupported TZ string
        UnsupportedTzString(&'static str),
    }

    impl fmt::Display for TzStringError {
        fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
            match self {
                Self::Utf8(error) => error.fmt(f),
                Self::ParseInt(error) => error.fmt(f),
                Self::ParseData(error) => error.fmt(f),
                Self::InvalidTzString(error) => write!(f, "invalid TZ string: {error}"),
                Self::UnsupportedTzString(error) => write!(f, "unsupported TZ string: {error}"),
            }
        }
    }

    impl Error for TzStringError {}

    impl From<Utf8Error> for TzStringError {
        fn from(error: Utf8Error) -> Self {
            Self::Utf8(error)
        }
    }

    impl From<ParseIntError> for TzStringError {
        fn from(error: ParseIntError) -> Self {
            Self::ParseInt(error)
        }
    }

    impl From<ParseDataError> for TzStringError {
        fn from(error: ParseDataError) -> Self {
            Self::ParseData(error)
        }
    }

    /// Unified error type for parsing a TZif file
    #[non_exhaustive]
    #[derive(Debug)]
    pub enum TzFileError {
        /// File was not found
        FileNotFound,
        /// UTF-8 error
        Utf8(Utf8Error),
        /// Parse data error
        ParseData(ParseDataError),
        /// I/O error
        Io(Box<dyn Error + Send + Sync + 'static>),
        /// Unified error for parsing a TZ string
        TzString(TzStringError),
        /// Invalid TZif file
        InvalidTzFile(&'static str),
        /// Unsupported TZif file
        UnsupportedTzFile(&'static str),
    }

    impl fmt::Display for TzFileError {
        fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
            match self {
                Self::FileNotFound => f.write_str("file was not found"),
                Self::Utf8(error) => error.fmt(f),
                Self::ParseData(error) => error.fmt(f),
                Self::Io(error) => error.fmt(f),
                Self::TzString(error) => error.fmt(f),
                Self::InvalidTzFile(error) => write!(f, "invalid TZ file: {error}"),
                Self::UnsupportedTzFile(error) => write!(f, "unsupported TZ file: {error}"),
            }
        }
    }

    impl Error for TzFileError {}

    impl From<Utf8Error> for TzFileError {
        fn from(error: Utf8Error) -> Self {
            Self::Utf8(error)
        }
    }

    impl From<ParseDataError> for TzFileError {
        fn from(error: ParseDataError) -> Self {
            Self::ParseData(error)
        }
    }

    impl From<TzStringError> for TzFileError {
        fn from(error: TzStringError) -> Self {
            Self::TzString(error)
        }
    }
}

#[doc(inline)]
#[cfg(feature = "alloc")]
pub use parse::{ParseDataError, TzFileError, TzStringError};

/// Create a new error type
macro_rules! create_error {
    (#[$doc:meta], $name:ident) => {
        #[$doc]
        #[derive(Debug)]
        pub struct $name(
            /// Error description
            pub &'static str,
        );

        impl fmt::Display for $name {
            fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
                self.0.fmt(f)
            }
        }

        impl Error for $name {}
    };
}

create_error!(#[doc = "Out of range error"], OutOfRangeError);
create_error!(#[doc = "Local time type error"], LocalTimeTypeError);
create_error!(#[doc = "Transition rule error"], TransitionRuleError);
create_error!(#[doc = "Time zone error"], TimeZoneError);
create_error!(#[doc = "Date time error"], DateTimeError);
create_error!(#[doc = "Local time type search error"], FindLocalTimeTypeError);
create_error!(#[doc = "Date time projection error"], ProjectDateTimeError);

impl From<OutOfRangeError> for ProjectDateTimeError {
    fn from(error: OutOfRangeError) -> Self {
        Self(error.0)
    }
}

impl From<FindLocalTimeTypeError> for ProjectDateTimeError {
    fn from(error: FindLocalTimeTypeError) -> Self {
        Self(error.0)
    }
}

/// Unified error type for everything in the crate
#[non_exhaustive]
#[derive(Debug)]
pub enum TzError {
    /// Unified error for parsing a TZif file
    #[cfg(feature = "alloc")]
    TzFile(TzFileError),
    /// Unified error for parsing a TZ string
    #[cfg(feature = "alloc")]
    TzString(TzStringError),
    /// Out of range error
    OutOfRange(OutOfRangeError),
    /// Local time type error
    LocalTimeType(LocalTimeTypeError),
    /// Transition rule error
    TransitionRule(TransitionRuleError),
    /// Time zone error
    TimeZone(TimeZoneError),
    /// Date time error
    DateTime(DateTimeError),
    /// Local time type search error
    FindLocalTimeType(FindLocalTimeTypeError),
    /// Date time projection error
    ProjectDateTime(ProjectDateTimeError),
}

impl fmt::Display for TzError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            #[cfg(feature = "alloc")]
            Self::TzFile(error) => error.fmt(f),
            #[cfg(feature = "alloc")]
            Self::TzString(error) => error.fmt(f),
            Self::OutOfRange(error) => error.fmt(f),
            Self::LocalTimeType(error) => write!(f, "invalid local time type: {error}"),
            Self::TransitionRule(error) => write!(f, "invalid transition rule: {error}"),
            Self::TimeZone(error) => write!(f, "invalid time zone: {error}"),
            Self::DateTime(error) => write!(f, "invalid date time: {error}"),
            Self::FindLocalTimeType(error) => error.fmt(f),
            Self::ProjectDateTime(error) => error.fmt(f),
        }
    }
}

impl Error for TzError {}

#[cfg(feature = "alloc")]
impl From<TzFileError> for TzError {
    fn from(error: TzFileError) -> Self {
        Self::TzFile(error)
    }
}

#[cfg(feature = "alloc")]
impl From<TzStringError> for TzError {
    fn from(error: TzStringError) -> Self {
        Self::TzString(error)
    }
}

impl From<OutOfRangeError> for TzError {
    fn from(error: OutOfRangeError) -> Self {
        Self::OutOfRange(error)
    }
}

impl From<LocalTimeTypeError> for TzError {
    fn from(error: LocalTimeTypeError) -> Self {
        Self::LocalTimeType(error)
    }
}

impl From<TransitionRuleError> for TzError {
    fn from(error: TransitionRuleError) -> Self {
        Self::TransitionRule(error)
    }
}

impl From<TimeZoneError> for TzError {
    fn from(error: TimeZoneError) -> Self {
        Self::TimeZone(error)
    }
}

impl From<DateTimeError> for TzError {
    fn from(error: DateTimeError) -> Self {
        Self::DateTime(error)
    }
}

impl From<FindLocalTimeTypeError> for TzError {
    fn from(error: FindLocalTimeTypeError) -> Self {
        Self::FindLocalTimeType(error)
    }
}

impl From<ProjectDateTimeError> for TzError {
    fn from(error: ProjectDateTimeError) -> Self {
        Self::ProjectDateTime(error)
    }
}
