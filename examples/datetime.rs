use tz::*;

fn main() -> Result<(), TzError> {
    //
    // TimeZone
    //

    // 2000-01-01T00:00:00Z
    let unix_time = 946684800;

    // Get UTC time zone
    let time_zone_utc = TimeZone::utc();
    assert_eq!(time_zone_utc.find_local_time_type(unix_time)?.ut_offset(), 0);

    // Get fixed time zone at GMT-1
    let time_zone_fixed = TimeZone::fixed(-3600);
    assert_eq!(time_zone_fixed.find_local_time_type(unix_time)?.ut_offset(), -3600);

    // Get local time zone
    let time_zone_local = TimeZone::local()?;

    // Get the current local time type
    let _current_local_time_type = time_zone_local.find_current_local_time_type()?;

    // Get time zone from a TZ string:
    // From an absolute file
    let _ = TimeZone::from_posix_tz("/usr/share/zoneinfo/Pacific/Auckland");
    // From a file relative to the system timezone directory
    let _ = TimeZone::from_posix_tz("Pacific/Auckland");
    // From a time zone description
    TimeZone::from_posix_tz("HST10")?;
    TimeZone::from_posix_tz("<-03>3")?;
    TimeZone::from_posix_tz("NZST-12:00:00NZDT-13:00:00,M10.1.0,M3.3.0")?;

    //
    // DateTime
    //

    // Create a new UTC date time
    // 2000-01-01T00:00:00Z
    let utc_date_time = UtcDateTime::new(2000, 0, 1, 0, 0, 0)?;
    let date_time = utc_date_time.to_date_time();
    assert_eq!(date_time.second(), 0);
    assert_eq!(date_time.minute(), 0);
    assert_eq!(date_time.hour(), 0);
    assert_eq!(date_time.month_day(), 1);
    assert_eq!(date_time.month(), 0);
    assert_eq!(date_time.year(), 100);
    assert_eq!(date_time.full_year(), 2000);
    assert_eq!(date_time.week_day(), 6);
    assert_eq!(date_time.year_day(), 0);
    assert_eq!(date_time.local_time_type().ut_offset(), 0);

    // Create a date time from a time zone and an UTC date time
    let time_zone_fixed = TimeZone::fixed(-3600);

    // 2000-01-01T00:00:00Z
    let utc_date_time = UtcDateTime::new(2000, 0, 1, 0, 0, 0)?;
    let date_time = DateTime::from_utc_date_time(&time_zone_fixed, utc_date_time)?;
    assert_eq!(date_time.second(), 0);
    assert_eq!(date_time.minute(), 0);
    assert_eq!(date_time.hour(), 23);
    assert_eq!(date_time.month_day(), 31);
    assert_eq!(date_time.month(), 11);
    assert_eq!(date_time.year(), 99);
    assert_eq!(date_time.full_year(), 1999);
    assert_eq!(date_time.week_day(), 5);
    assert_eq!(date_time.year_day(), 364);
    assert_eq!(date_time.local_time_type().ut_offset(), -3600);

    // Create a date time from a time zone and an unix time
    // 2000-01-01T00:00:00Z
    let date_time = DateTime::from_unix_time(&time_zone_fixed, 946684800)?;
    assert_eq!(date_time.second(), 0);
    assert_eq!(date_time.minute(), 0);
    assert_eq!(date_time.hour(), 23);
    assert_eq!(date_time.month_day(), 31);
    assert_eq!(date_time.month(), 11);
    assert_eq!(date_time.year(), 99);
    assert_eq!(date_time.full_year(), 1999);
    assert_eq!(date_time.week_day(), 5);
    assert_eq!(date_time.year_day(), 364);
    assert_eq!(date_time.local_time_type().ut_offset(), -3600);

    // Get the corresponding UTC unix time
    let unix_time = date_time.unix_time();
    assert_eq!(unix_time, 946684800);

    // Get the current date time at the local time zone
    let time_zone_local = TimeZone::local()?;
    let _date_time = DateTime::now(&time_zone_local)?;

    Ok(())
}
