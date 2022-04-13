#![no_main]
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    use tz::TimeZone;

    let _ = TimeZone::from_tz_data(data);
});
