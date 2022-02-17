use std::io::{Error, ErrorKind};

#[derive(Debug, Default, Eq, PartialEq)]
pub struct Cursor<'a> {
    remaining: &'a [u8],
    read_count: usize,
}

impl<'a> Cursor<'a> {
    pub fn new(remaining: &'a [u8]) -> Self {
        Self { remaining, read_count: 0 }
    }

    pub fn remaining(&self) -> &'a [u8] {
        self.remaining
    }

    pub fn is_empty(&self) -> bool {
        self.remaining.is_empty()
    }

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

    pub fn read_tag(&mut self, tag: &[u8]) -> Result<(), Error> {
        if self.read_exact(tag.len())? == tag {
            Ok(())
        } else {
            Err(Error::from(ErrorKind::InvalidData))
        }
    }

    pub fn read_optional_tag(&mut self, tag: &[u8]) -> Result<bool, Error> {
        if self.remaining.starts_with(tag) {
            self.read_exact(tag.len())?;
            Ok(true)
        } else {
            Ok(false)
        }
    }

    pub fn read_while<F: Fn(&u8) -> bool>(&mut self, f: F) -> Result<&'a [u8], Error> {
        match self.remaining.iter().position(|x| !f(x)) {
            None => self.read_exact(self.remaining.len()),
            Some(position) => self.read_exact(position),
        }
    }

    pub fn read_until<F: Fn(&u8) -> bool>(&mut self, f: F) -> Result<&'a [u8], Error> {
        match self.remaining.iter().position(f) {
            None => self.read_exact(self.remaining.len()),
            Some(position) => self.read_exact(position),
        }
    }
}
