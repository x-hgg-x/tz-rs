//! Types related to a static time zone.

use super::*;

/// Static local time type associated to a time zone
pub type StaticLocalTimeType = GenericLocalTimeType<&'static str>;

impl StaticLocalTimeType {
    /// Construct a static local time type
    pub const fn new(ut_offset: i32, is_dst: bool, time_zone_designation: Option<&'static str>) -> Result<Self, LocalTimeTypeError> {
        match Self::check_inputs(ut_offset, time_zone_designation) {
            Ok(_) => Ok(Self { ut_offset, is_dst, time_zone_designation }),
            Err(error) => Err(error),
        }
    }

    /// Returns time zone designation
    pub const fn time_zone_designation(&self) -> &str {
        match self.time_zone_designation {
            Some(x) => x,
            None => "",
        }
    }

    /// Returns a copy of the value
    pub const fn clone(&self) -> Self {
        Self { ut_offset: self.ut_offset, is_dst: self.is_dst, time_zone_designation: self.time_zone_designation }
    }
}

/// Static transition rule representing alternate local time types
pub type StaticAlternateTime = GenericAlternateTime<&'static str>;

impl StaticAlternateTime {
    /// Construct a static transition rule representing alternate local time types
    pub const fn new(
        std: StaticLocalTimeType,
        dst: StaticLocalTimeType,
        dst_start: RuleDay,
        dst_start_time: i32,
        dst_end: RuleDay,
        dst_end_time: i32,
    ) -> Result<Self, TransitionRuleError> {
        use crate::constants::*;

        if !((dst_start_time.abs() as i64) < SECONDS_PER_WEEK && (dst_end_time.abs() as i64) < SECONDS_PER_WEEK) {
            return Err(TransitionRuleError("invalid DST start or end time"));
        }

        Ok(Self { std, dst, dst_start, dst_start_time, dst_end, dst_end_time })
    }
}

/// Static transition rule
pub type StaticTransitionRule = GenericTransitionRule<&'static str>;

impl<'a> TimeZoneRef<'a, &'static str> {
    /// Check extra rule
    const fn check_extra_rule(&self) -> Result<(), TimeZoneError> {
        match self.find_last_local_time_types() {
            Err(ConversionError(error)) => Err(TimeZoneError(error)),
            Ok(None) => Ok(()),
            Ok(Some((last_local_time_type, rule_local_time_type))) => {
                if last_local_time_type.ut_offset == rule_local_time_type.ut_offset
                    && last_local_time_type.is_dst == rule_local_time_type.is_dst
                    && equal(last_local_time_type.time_zone_designation().as_bytes(), rule_local_time_type.time_zone_designation().as_bytes())
                {
                    Ok(())
                } else {
                    Err(TimeZoneError("extra transition rule is inconsistent with the last transition"))
                }
            }
        }
    }
}

/// Static time zone
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct StaticTimeZone {
    /// List of transitions
    transitions: &'static [Transition],
    /// List of local time types (cannot be empty)
    local_time_types: &'static [StaticLocalTimeType],
    /// List of leap seconds
    leap_seconds: &'static [LeapSecond],
    /// Extra transition rule applicable after the last transition
    extra_rule: Option<StaticTransitionRule>,
}

impl StaticTimeZone {
    /// Construct a static time zone
    pub const fn new(
        transitions: &'static [Transition],
        local_time_types: &'static [StaticLocalTimeType],
        leap_seconds: &'static [LeapSecond],
        extra_rule: Option<StaticTransitionRule>,
    ) -> Result<Self, TimeZoneError> {
        let time_zone_ref = TimeZoneRef::new(transitions, local_time_types, leap_seconds, &extra_rule);

        if let Err(error) = time_zone_ref.check_inputs() {
            return Err(error);
        }
        if let Err(error) = time_zone_ref.check_extra_rule() {
            return Err(error);
        }

        Ok(Self { transitions, local_time_types, leap_seconds, extra_rule })
    }

    /// Returns a reference to the time zone
    pub const fn as_ref(&self) -> TimeZoneRef<&'static str> {
        TimeZoneRef::new(self.transitions, self.local_time_types, self.leap_seconds, &self.extra_rule)
    }

    /// Construct the time zone associated to UTC
    pub const fn utc() -> Self {
        const UTC: StaticLocalTimeType = StaticLocalTimeType::utc();
        Self { transitions: &[], local_time_types: &[UTC], leap_seconds: &[], extra_rule: None }
    }

    /// Find the local time type associated to the time zone at the specified Unix time in seconds
    pub const fn find_local_time_type(&self, unix_time: i64) -> Result<&StaticLocalTimeType, FindLocalTimeTypeError> {
        self.as_ref().find_local_time_type(unix_time)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    macro_rules! unwrap {
        ($x:expr) => {
            match $x {
                Ok(x) => x,
                Err(error) => panic!("{}", error.0),
            }
        };
    }

    #[test]
    fn test_const() {
        const _: StaticTimeZone = unwrap!(StaticTimeZone::new(
            &[
                Transition::new(-2334101314, 1),
                Transition::new(-1157283000, 2),
                Transition::new(-1155436200, 1),
                Transition::new(-880198200, 3),
                Transition::new(-769395600, 4),
                Transition::new(-765376200, 1),
                Transition::new(-712150200, 5),
            ],
            {
                const TMP: &[StaticLocalTimeType] = &[
                    unwrap!(StaticLocalTimeType::new(-37886, false, Some("LMT"))),
                    unwrap!(StaticLocalTimeType::new(-37800, false, Some("HST"))),
                    unwrap!(StaticLocalTimeType::new(-34200, true, Some("HDT"))),
                    unwrap!(StaticLocalTimeType::new(-34200, true, Some("HWT"))),
                    unwrap!(StaticLocalTimeType::new(-34200, true, Some("HPT"))),
                    unwrap!(StaticLocalTimeType::new(-36000, false, Some("HST"))),
                ];
                TMP
            },
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

        const _: StaticTimeZone = StaticTimeZone::utc();
    }
}
