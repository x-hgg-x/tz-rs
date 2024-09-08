//! Error types.

use core::array::TryFromSliceError;
use core::error::Error;
use core::fmt;
use core::num::TryFromIntError;

#[cfg(feature = "std")]
mod parse {
    use super::*;

    use core::num::ParseIntError;
    use core::str::Utf8Error;

    /// Parse data error
    #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
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
    #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
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
                Self::InvalidTzString(error) => write!(f, "invalid TZ string: {}", error),
                Self::UnsupportedTzString(error) => write!(f, "unsupported TZ string: {}", error),
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
    #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
    #[non_exhaustive]
    #[derive(Debug)]
    pub enum TzFileError {
        /// UTF-8 error
        Utf8(Utf8Error),
        /// Conversion from slice to array error
        TryFromSlice(TryFromSliceError),
        /// Parse data error
        ParseData(ParseDataError),
        /// I/O error
        Io(std::io::Error),
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
                Self::Utf8(error) => error.fmt(f),
                Self::TryFromSlice(error) => error.fmt(f),
                Self::ParseData(error) => error.fmt(f),
                Self::Io(error) => error.fmt(f),
                Self::TzString(error) => error.fmt(f),
                Self::InvalidTzFile(error) => write!(f, "invalid TZ file: {}", error),
                Self::UnsupportedTzFile(error) => write!(f, "unsupported TZ file: {}", error),
            }
        }
    }

    impl Error for TzFileError {}

    impl From<Utf8Error> for TzFileError {
        fn from(error: Utf8Error) -> Self {
            Self::Utf8(error)
        }
    }

    impl From<TryFromSliceError> for TzFileError {
        fn from(error: TryFromSliceError) -> Self {
            Self::TryFromSlice(error)
        }
    }

    impl From<std::io::Error> for TzFileError {
        fn from(error: std::io::Error) -> Self {
            Self::Io(error)
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

#[cfg(feature = "std")]
pub use parse::{ParseDataError, TzFileError, TzStringError};

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
    /// Conversion from slice to array error
    TryFromSlice(TryFromSliceError),
    /// I/O error
    #[cfg(feature = "std")]
    #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
    Io(std::io::Error),
    /// System time error
    #[cfg(feature = "std")]
    #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
    SystemTime(std::time::SystemTimeError),
    /// Unified error for parsing a TZif file
    #[cfg(feature = "std")]
    #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
    TzFile(TzFileError),
    /// Unified error for parsing a TZ string
    #[cfg(feature = "std")]
    #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
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
            Self::TryFromSlice(error) => error.fmt(f),
            #[cfg(feature = "std")]
            Self::Io(error) => error.fmt(f),
            #[cfg(feature = "std")]
            Self::SystemTime(error) => error.fmt(f),
            #[cfg(feature = "std")]
            Self::TzFile(error) => error.fmt(f),
            #[cfg(feature = "std")]
            Self::TzString(error) => error.fmt(f),
            Self::OutOfRange(error) => error.fmt(f),
            Self::LocalTimeType(error) => write!(f, "invalid local time type: {}", error),
            Self::TransitionRule(error) => write!(f, "invalid transition rule: {}", error),
            Self::TimeZone(error) => write!(f, "invalid time zone: {}", error),
            Self::DateTime(error) => write!(f, "invalid date time: {}", error),
            Self::FindLocalTimeType(error) => error.fmt(f),
            Self::ProjectDateTime(error) => error.fmt(f),
        }
    }
}

impl Error for TzError {}

impl From<TryFromSliceError> for TzError {
    fn from(error: TryFromSliceError) -> Self {
        Self::TryFromSlice(error)
    }
}

#[cfg(feature = "std")]
#[cfg_attr(docsrs, doc(cfg(feature = "std")))]
impl From<std::io::Error> for TzError {
    fn from(error: std::io::Error) -> Self {
        Self::Io(error)
    }
}

#[cfg(feature = "std")]
#[cfg_attr(docsrs, doc(cfg(feature = "std")))]
impl From<std::time::SystemTimeError> for TzError {
    fn from(error: std::time::SystemTimeError) -> Self {
        Self::SystemTime(error)
    }
}

#[cfg(feature = "std")]
#[cfg_attr(docsrs, doc(cfg(feature = "std")))]
impl From<TzFileError> for TzError {
    fn from(error: TzFileError) -> Self {
        Self::TzFile(error)
    }
}

#[cfg(feature = "std")]
#[cfg_attr(docsrs, doc(cfg(feature = "std")))]
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

impl From<TryFromIntError> for TzError {
    fn from(_: TryFromIntError) -> Self {
        Self::OutOfRange(OutOfRangeError("out of range integer conversion"))
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
