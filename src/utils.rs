//! Some useful utilities.

use std::io::{Error, ErrorKind};
use std::ops::Index;

/// A `Cursor` contains a slice of a buffer and a read count.
#[derive(Debug, Default, Eq, PartialEq)]
pub struct Cursor<'a> {
    /// Slice representing the remaining data to be read
    remaining: &'a [u8],
    /// Number of already read bytes
    read_count: usize,
}

impl<'a> Cursor<'a> {
    /// Construct a new `Cursor` from remaining data
    pub fn new(remaining: &'a [u8]) -> Self {
        Self { remaining, read_count: 0 }
    }

    /// Returns remaining data
    pub fn remaining(&self) -> &'a [u8] {
        self.remaining
    }

    /// Returns `true` if data is remaining
    pub fn is_empty(&self) -> bool {
        self.remaining.is_empty()
    }

    /// Read exactly `count` bytes, reducing remaining data and incrementing read count
    pub fn read_exact(&mut self, count: usize) -> Result<&'a [u8], Error> {
        match (self.remaining.get(..count), self.remaining.get(count..)) {
            (Some(result), Some(remaining)) => {
                self.remaining = remaining;
                self.read_count += count;
                Ok(result)
            }
            _ => Err(Error::from(ErrorKind::UnexpectedEof)),
        }
    }

    /// Read bytes and compare them to the provided tag
    pub fn read_tag(&mut self, tag: &[u8]) -> Result<(), Error> {
        if self.read_exact(tag.len())? == tag {
            Ok(())
        } else {
            Err(Error::from(ErrorKind::InvalidData))
        }
    }

    /// Read bytes if the remaining data is prefixed by the provided tag
    pub fn read_optional_tag(&mut self, tag: &[u8]) -> Result<bool, Error> {
        if self.remaining.starts_with(tag) {
            self.read_exact(tag.len())?;
            Ok(true)
        } else {
            Ok(false)
        }
    }

    /// Read bytes as long as the provided predicate is true
    pub fn read_while<F: Fn(&u8) -> bool>(&mut self, f: F) -> Result<&'a [u8], Error> {
        match self.remaining.iter().position(|x| !f(x)) {
            None => self.read_exact(self.remaining.len()),
            Some(position) => self.read_exact(position),
        }
    }

    /// Read bytes until the provided predicate is false
    pub fn read_until<F: Fn(&u8) -> bool>(&mut self, f: F) -> Result<&'a [u8], Error> {
        match self.remaining.iter().position(f) {
            None => self.read_exact(self.remaining.len()),
            Some(position) => self.read_exact(position),
        }
    }
}

/// Vector type guaranteed to hold at least one element
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct NonEmptyVec<T> {
    /// First element
    pub first: T,
    /// Other elements
    pub tail: Vec<T>,
}

impl<T> NonEmptyVec<T> {
    /// Construct a `NonEmptyVec` with one element
    pub fn one(first: T) -> Self {
        Self { first, tail: Vec::new() }
    }
}

impl<T> Index<usize> for NonEmptyVec<T> {
    type Output = T;

    fn index(&self, index: usize) -> &Self::Output {
        if index == 0 {
            &self.first
        } else {
            &self.tail[index - 1]
        }
    }
}
