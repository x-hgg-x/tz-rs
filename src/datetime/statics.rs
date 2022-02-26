//! Types related to a static date time.

use super::*;

use crate::timezone::statics::StaticTimeZone;

impl UtcDateTime {
    /// Project the UTC date time into a time zone, returning a static date time.
    ///
    /// Leap seconds are not preserved.
    ///
    pub const fn project_const(&self, time_zone: &StaticTimeZone) -> Result<StaticDateTime, ProjectDateTimeError> {
        let unix_time = self.unix_time();

        let local_time_type = match time_zone.find_local_time_type(unix_time) {
            Ok(local_time_type) => local_time_type.clone(),
            Err(FindLocalTimeTypeError(error)) => return Err(ProjectDateTimeError(error)),
        };

        let utc_date_time_with_offset = match UtcDateTime::from_unix_time(unix_time + local_time_type.ut_offset() as i64) {
            Ok(utc_date_time_with_offset) => utc_date_time_with_offset,
            Err(ConversionError(error)) => return Err(ProjectDateTimeError(error)),
        };

        let UtcDateTime { year, month, month_day, hour, minute, second } = utc_date_time_with_offset;
        Ok(StaticDateTime { year, month, month_day, hour, minute, second, local_time_type, unix_time })
    }
}

/// Static date time associated to a local time type, exprimed in the [proleptic gregorian calendar](https://en.wikipedia.org/wiki/Proleptic_Gregorian_calendar)
pub type StaticDateTime = GenericDateTime<&'static str>;

impl StaticDateTime {
    /// Project the date time into another time zone.
    ///
    /// Leap seconds are not preserved.
    ///
    pub const fn project(&self, time_zone: &StaticTimeZone) -> Result<Self, ProjectDateTimeError> {
        let local_time_type = match time_zone.find_local_time_type(self.unix_time) {
            Ok(local_time_type) => local_time_type.clone(),
            Err(FindLocalTimeTypeError(error)) => return Err(ProjectDateTimeError(error)),
        };

        let utc_date_time_with_offset = match UtcDateTime::from_unix_time(self.unix_time + local_time_type.ut_offset() as i64) {
            Ok(utc_date_time_with_offset) => utc_date_time_with_offset,
            Err(ConversionError(error)) => return Err(ProjectDateTimeError(error)),
        };

        let UtcDateTime { year, month, month_day, hour, minute, second } = utc_date_time_with_offset;
        Ok(StaticDateTime { year, month, month_day, hour, minute, second, local_time_type, unix_time: self.unix_time })
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use crate::timezone::statics::*;
    use crate::timezone::*;

    macro_rules! unwrap {
        ($x:expr) => {
            match $x {
                Ok(x) => x,
                Err(error) => panic!("{}", error.0),
            }
        };
    }

    macro_rules! to_const {
        ($x:expr) => {{
            const TMP: &[StaticLocalTimeType] = $x;
            TMP
        }};
    }

    #[test]
    fn test_const() {
        const TIME_ZONE: StaticTimeZone = unwrap!(StaticTimeZone::new(
            &[
                Transition::new(-2334101314, 1),
                Transition::new(-1157283000, 2),
                Transition::new(-1155436200, 1),
                Transition::new(-880198200, 3),
                Transition::new(-769395600, 4),
                Transition::new(-765376200, 1),
                Transition::new(-712150200, 5),
            ],
            to_const!(&[
                unwrap!(StaticLocalTimeType::new(-37886, false, Some("LMT"))),
                unwrap!(StaticLocalTimeType::new(-37800, false, Some("HST"))),
                unwrap!(StaticLocalTimeType::new(-34200, true, Some("HDT"))),
                unwrap!(StaticLocalTimeType::new(-34200, true, Some("HWT"))),
                unwrap!(StaticLocalTimeType::new(-34200, true, Some("HPT"))),
                unwrap!(StaticLocalTimeType::new(-36000, false, Some("HST"))),
            ]),
            &[
                LeapSecond::new(78796800, 1),
                LeapSecond::new(94694401, 2),
                LeapSecond::new(126230402, 3),
                LeapSecond::new(157766403, 4),
                LeapSecond::new(189302404, 5),
                LeapSecond::new(220924805, 6),
            ],
            Some(StaticTransitionRule::Alternate(unwrap!(StaticAlternateTime::new(
                unwrap!(StaticLocalTimeType::new(-36000, false, Some("HST"))),
                unwrap!(StaticLocalTimeType::new(-34200, true, Some("HPT"))),
                RuleDay::MonthWeekDay(unwrap!(MonthWeekDay::new(10, 5, 0))),
                93600,
                RuleDay::MonthWeekDay(unwrap!(MonthWeekDay::new(3, 4, 4))),
                7200,
            )))),
        ));

        const UTC: StaticTimeZone = StaticTimeZone::utc();

        const UNIX_EPOCH: UtcDateTime = unwrap!(UtcDateTime::from_unix_time(0));
        const UTC_DATE_TIME: UtcDateTime = unwrap!(UtcDateTime::new(2000, 0, 1, 0, 0, 0));

        const DATE_TIME_1: StaticDateTime = unwrap!(UTC_DATE_TIME.project_const(&TIME_ZONE));
        const DATE_TIME_2: StaticDateTime = unwrap!(DATE_TIME_1.project(&UTC));

        assert_eq!(UNIX_EPOCH.unix_time(), 0);
        assert_eq!(DATE_TIME_2.unix_time(), UTC_DATE_TIME.unix_time());
    }
}
