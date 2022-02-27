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
    let time_zone_fixed = TimeZone::fixed(-3600)?;
    println!("{:?}", time_zone_fixed.find_local_time_type(unix_time)?.ut_offset());

    // Get local time zone (UNIX only)
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
    // Use a leading colon to force searching for a corresponding file
    let _ = TimeZone::from_posix_tz(":UTC");

    //
    // DateTime
    //

    // Get the current UTC date time
    let current_utc_date_time = UtcDateTime::now()?;
    println!("{:?}", current_utc_date_time);

    // Create a new UTC date time (2000-01-01T00:00:00.123456789Z)
    let utc_date_time = UtcDateTime::new(2000, 0, 1, 0, 0, 0, 123_456_789)?;
    println!("{}", utc_date_time);
    println!("{:?}", utc_date_time);

    // Create a new UTC date time from a Unix time with nanoseconds (2000-01-01T00:00:00.123456789Z)
    let other_utc_date_time = UtcDateTime::from_timespec(946684800, 123_456_789)?;
    println!("{}", other_utc_date_time);
    println!("{:?}", other_utc_date_time);

    // Project the UTC date time to a time zone
    let date_time = utc_date_time.project(TimeZone::fixed(-3600)?.as_ref())?;
    println!("{}", date_time);
    println!("{:#?}", date_time);

    // Project the date time to another time zone
    let other_date_time = date_time.project(TimeZone::fixed(3600)?.as_ref())?;
    println!("{}", other_date_time);
    println!("{:#?}", other_date_time);

    // Create a new date time from a Unix time with nanoseconds and a time zone (2000-01-01T00:00:00.123456789Z)
    let another_date_time = DateTime::from_timespec(946684800, 123_456_789, TimeZone::fixed(86400)?.as_ref())?;
    println!("{}", another_date_time);
    println!("{:#?}", another_date_time);

    // Get the corresponding UTC Unix times with nanoseconds
    println!("{}.{:09}", utc_date_time.unix_time(), utc_date_time.nanoseconds());
    println!("{}.{:09}", other_utc_date_time.unix_time(), other_utc_date_time.nanoseconds());
    println!("{}.{:09}", date_time.unix_time(), date_time.nanoseconds());
    println!("{}.{:09}", other_date_time.unix_time(), other_date_time.nanoseconds());

    // Get the current date time at the local time zone (UNIX only)
    let time_zone_local = TimeZone::local()?;
    let date_time = DateTime::now(time_zone_local.as_ref())?;
    println!("{:#?}", date_time);

    Ok(())
}
