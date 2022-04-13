#![no_main]
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    use tz::TimeZone;

    if let Ok(data) = std::str::from_utf8(data) {
        let _ = TimeZone::from_posix_tz(data);
    }
});
