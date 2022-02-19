# tz-rs

[![version](https://img.shields.io/crates/v/tz-rs?color=blue&style=flat-square)](https://crates.io/crates/tz-rs)

A pure Rust reimplementation of libc functions `localtime`, `gmtime` and `mktime`.

## Documentation

Documentation is hosted on [docs.rs](https://docs.rs/tz-rs/latest/tz).

## Platform support

This crate is mainly intended for UNIX platforms.

Since the time zone database files are not included in this crate, Windows users can download a copy of the database on the [IANA site](https://www.iana.org/time-zones) and compile the time zone database files to a local directory.

The database files can then be read by specifying an absolute path in the `TZ` string:

```rust
    TimeZone::from_posix_tz(format!("{}/usr/share/zoneinfo/Pacific/Auckland", local_database_dir))?;
```

## License

This project is licensed under either of

- [Apache License, Version 2.0](https://github.com/x-hgg-x/tz-rs/blob/master/LICENSE-Apache)
- [MIT license](https://github.com/x-hgg-x/tz-rs/blob/master/LICENSE-MIT)

at your option.

Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in
time by you, as defined in the Apache-2.0 license, shall be dual licensed as above, without any
additional terms or conditions.
