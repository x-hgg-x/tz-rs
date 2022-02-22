use crate::{LeapSecond, LocalTimeType, TimeZoneImpl, Transition, TransitionRule};

use std::fmt;

#[derive(Debug)]
pub struct StaticTimeZoneError(pub &'static str);

impl fmt::Display for StaticTimeZoneError {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        self.0.fmt(f)
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct StaticTimeZone {
    transitions: &'static [Transition],
    local_time_types: (LocalTimeType<&'static str>, &'static [LocalTimeType<&'static str>]),
    leap_seconds: &'static [LeapSecond],
    extra_rule: Option<TransitionRule<&'static str>>,
}

impl StaticTimeZone {
    pub const fn new(
        transitions: &'static [Transition],
        local_time_types: (LocalTimeType<&'static str>, &'static [LocalTimeType<&'static str>]),
        leap_seconds: &'static [LeapSecond],
        extra_rule: Option<TransitionRule<&'static str>>,
    ) -> Result<Self, StaticTimeZoneError> {
        if let Err(e) = Self::check_transitions(transitions, &local_time_types) {
            return Err(e);
        }

        if let Err(e) = Self::check_local_time_types(&local_time_types) {
            return Err(e);
        }

        if let Err(e) = Self::check_leap_seconds(leap_seconds) {
            return Err(e);
        }

        Ok(StaticTimeZone { transitions, local_time_types, leap_seconds, extra_rule })
    }

    const fn check_transitions(
        transitions: &'static [Transition],
        local_time_types: &(LocalTimeType<&'static str>, &'static [LocalTimeType<&'static str>]),
    ) -> Result<(), StaticTimeZoneError> {
        let mut i = 0;

        while i < transitions.len() {
            if transitions[i].local_time_type_index > local_time_types.1.len() {
                return Err(StaticTimeZoneError("invalid local time type index"));
            }

            if i + 1 < transitions.len() && transitions[i].unix_leap_time >= transitions[i + 1].unix_leap_time {
                return Err(StaticTimeZoneError("invalid transition"));
            }

            i += 1;
        }

        Ok(())
    }

    const fn check_local_time_types(
        local_time_types: &(LocalTimeType<&'static str>, &'static [LocalTimeType<&'static str>]),
    ) -> Result<(), StaticTimeZoneError> {
        if local_time_types.0.ut_offset == i32::MIN {
            return Err(StaticTimeZoneError("invalid UTC offset"));
        }

        let mut i = 0;
        while i < local_time_types.1.len() {
            if local_time_types.0.ut_offset == i32::MIN {
                return Err(StaticTimeZoneError("invalid UTC offset"));
            }
            i += 1;
        }

        Ok(())
    }

    const fn check_leap_seconds(leap_seconds: &'static [LeapSecond]) -> Result<(), StaticTimeZoneError> {
        if !(leap_seconds.is_empty() || leap_seconds[0].unix_leap_time >= 0 && leap_seconds[0].correction.abs() == 1) {
            return Err(StaticTimeZoneError("invalid leap second"));
        }

        let mut i = 0;
        while i < leap_seconds.len() {
            if i + 1 < leap_seconds.len() {
                let x0 = leap_seconds[i];
                let x1 = leap_seconds[i + 1];

                if !(x1.unix_leap_time >= x0.unix_leap_time + 2419199 && (x1.correction - x0.correction).abs() == 1) {
                    return Err(StaticTimeZoneError("invalid leap second"));
                }
            }

            i += 1;
        }

        Ok(())
    }
}

impl TimeZoneImpl<&'static str> for StaticTimeZone {
    fn transitions(&self) -> &[Transition] {
        self.transitions
    }

    fn local_time_type(&self, index: usize) -> &LocalTimeType<&'static str> {
        if index == 0 {
            &self.local_time_types.0
        } else {
            &self.local_time_types.1[index - 1]
        }
    }

    fn leap_seconds(&self) -> &[LeapSecond] {
        self.leap_seconds
    }

    fn extra_rule(&self) -> Option<&TransitionRule<&'static str>> {
        self.extra_rule.as_ref()
    }
}
