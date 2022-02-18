use tz::*;

fn main() -> Result<()> {
    //
    // TimeZone
    //

    // 2000-01-01T00:00:00Z
    let unix_time = 946684800;

    // Get UTC time zone
    let time_zone_utc = TimeZone::utc();
    println!("{:?}", time_zone_utc.find_local_time_type(unix_time)?);

    // Get fixed time zone at GMT-1
    let time_zone_fixed = TimeZone::fixed(-3600);
    println!("{:?}", time_zone_fixed.find_local_time_type(unix_time)?.ut_offset());

    // Get local time zone
    let time_zone_local = TimeZone::local()?;
    println!("{:?}", time_zone_local.find_local_time_type(unix_time)?.ut_offset());

    // Get the current local time type
    let current_local_time_type = time_zone_local.find_current_local_time_type()?;
    println!("{:?}", current_local_time_type);

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
    println!("{:#?}", date_time);

    // Create a date time from a time zone and an UTC date time
    let time_zone_fixed = TimeZone::fixed(-3600);

    // 2000-01-01T00:00:00Z
    let utc_date_time = UtcDateTime::new(2000, 0, 1, 0, 0, 0)?;
    let date_time = DateTime::from_utc_date_time(&time_zone_fixed, utc_date_time)?;
    println!("{:#?}", date_time);

    // Create a date time from a time zone and an unix time
    // 2000-01-01T00:00:00Z
    let date_time = DateTime::from_unix_time(&time_zone_fixed, 946684800)?;
    println!("{:#?}", date_time);

    // Get the corresponding UTC unix time
    println!("{}", date_time.unix_time());

    // Get the current date time at the local time zone
    let time_zone_local = TimeZone::local()?;
    let date_time = DateTime::now(&time_zone_local)?;
    println!("{:#?}", date_time);

    Ok(())
}
