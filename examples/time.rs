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

    // Get the current UTC date time (with full seconds)
    let current_utc_date_time = UtcDateTime::<i64>::now()?;
    println!("{:?}", current_utc_date_time);

    // Get the current UTC date time (with sub-second times)
    let current_utc_date_time = UtcDateTime::<f64>::now()?;
    println!("{:?}", current_utc_date_time);

    // Create a new UTC date time (2000-01-01T00:00:00Z)
    let utc_date_time = UtcDateTime::<i64>::new(2000, 0, 1, 0, 0, 0, ())?;
    println!("{:?}", utc_date_time);

    // Create a new UTC date time from a Unix time (2000-01-01T00:00:00Z)
    let other_utc_date_time = UtcDateTime::from_unix_time(946684800)?;
    println!("{:?}", other_utc_date_time);

    // Project the UTC date time to a time zone
    let date_time = utc_date_time.project(&TimeZone::fixed(-3600))?;
    println!("{:#?}", date_time);

    // Project the date time to another time zone
    let other_date_time = date_time.project(&TimeZone::fixed(3600))?;
    println!("{:#?}", other_date_time);

    // Get the corresponding UTC Unix times
    println!("{}", utc_date_time.unix_time());
    println!("{}", other_utc_date_time.unix_time());
    println!("{}", date_time.unix_time());
    println!("{}", other_date_time.unix_time());

    // Get the current date time at the local time zone (UNIX only)
    let time_zone_local = TimeZone::local()?;
    let date_time = DateTime::<i64>::now(&time_zone_local)?;
    println!("{:#?}", date_time);

    Ok(())
}
