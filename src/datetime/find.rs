//! Types related to the [`DateTime::find`] method.

use crate::datetime::*;
use crate::timezone::TransitionRule;
use crate::Result;

/// Type of a found date time created by the [`DateTime::find`] method
#[derive(Debug, Clone, PartialEq)]
pub enum FoundDateTimeKind {
    /// Found date time is valid
    Normal(DateTime),
    /// Found date time is invalid because it was skipped by a forward transition.
    ///
    /// This variant gives the two [`DateTime`] corresponding to the transition instant, just before and just after the transition.
    ///
    /// This is different from the `mktime` behavior, which allows invalid date times when no DST information is available (by specifying `tm_isdst = -1`).
    Skipped {
        /// Date time just before the forward transition
        before_transition: DateTime,
        /// Date time just after the forward transition
        after_transition: DateTime,
    },
}

/// List containing the found date times created by the [`DateTime::find`] method.
///
/// It can be empty if no local time type was found for the provided date, time and time zone.
#[derive(Debug, Clone, PartialEq)]
pub struct FoundDateTimeList(Vec<FoundDateTimeKind>);

impl FoundDateTimeList {
    /// Returns the found date time if existing and unique
    pub fn unique(&self) -> Option<DateTime> {
        match *self.0.as_slice() {
            [FoundDateTimeKind::Normal(date_time)] => Some(date_time),
            _ => None,
        }
    }

    /// Returns the earliest found date time if existing
    pub fn earliest(&self) -> Option<DateTime> {
        // Found date times are computed in ascending order of Unix time
        match *self.0.first()? {
            FoundDateTimeKind::Normal(date_time) => Some(date_time),
            FoundDateTimeKind::Skipped { before_transition, .. } => Some(before_transition),
        }
    }

    /// Returns the latest found date time if existing
    pub fn latest(&self) -> Option<DateTime> {
        // Found date times are computed in ascending order of Unix time
        match *self.0.last()? {
            FoundDateTimeKind::Normal(date_time) => Some(date_time),
            FoundDateTimeKind::Skipped { after_transition, .. } => Some(after_transition),
        }
    }

    /// Extracts and returns the inner list of found date times
    pub fn into_inner(self) -> Vec<FoundDateTimeKind> {
        self.0
    }
}

/// Find the possible date times correponding to a date, a time and a time zone
///
/// ## Inputs
///
/// * `year`: Year
/// * `month`: Month in `[1, 12]`
/// * `month_day`: Day of the month in `[1, 31]`
/// * `hour`: Hours since midnight in `[0, 23]`
/// * `minute`: Minutes in `[0, 59]`
/// * `second`: Seconds in `[0, 60]`, with a possible leap second
/// * `nanoseconds`: Nanoseconds in `[0, 999_999_999]`
/// * `time_zone_ref`: Reference to a time zone
///
#[allow(clippy::too_many_arguments)]
pub fn find_date_time(
    year: i32,
    month: u8,
    month_day: u8,
    hour: u8,
    minute: u8,
    second: u8,
    nanoseconds: u32,
    time_zone_ref: TimeZoneRef,
) -> Result<FoundDateTimeList> {
    let transitions = time_zone_ref.transitions();
    let local_time_types = time_zone_ref.local_time_types();
    let extra_rule = time_zone_ref.extra_rule();

    if transitions.is_empty() && extra_rule.is_none() {
        let date_time = DateTime::new(year, month, month_day, hour, minute, second, nanoseconds, local_time_types[0])?;
        return Ok(FoundDateTimeList(vec![FoundDateTimeKind::Normal(date_time)]));
    }

    let new_datetime = |local_time_type, unix_time| DateTime { year, month, month_day, hour, minute, second, local_time_type, unix_time, nanoseconds };

    let mut found_date_times = Vec::new();

    check_date_time_inputs(year, month, month_day, hour, minute, second, nanoseconds)?;
    let utc_unix_time = unix_time(year, month, month_day, hour, minute, second);

    // Process transitions
    if !transitions.is_empty() {
        let possible_times = local_time_types
            .iter()
            .map(|local_time_type| {
                // Overflow is not possible
                let unix_time = utc_unix_time - local_time_type.ut_offset() as i64;
                let unix_leap_time = time_zone_ref.unix_time_to_unix_leap_time(unix_time)?;
                Ok((unix_time, unix_leap_time))
            })
            .collect::<Result<Vec<_>>>()?;

        let mut previous_transition_unix_leap_time = i64::MIN;
        let mut previous_local_time_type_index = 0;

        // Check transitions in order
        for (index, transition) in transitions.iter().enumerate() {
            let local_time_type_before = local_time_types[previous_local_time_type_index];
            let (unix_time_before, unix_leap_time_before) = possible_times[previous_local_time_type_index];

            if previous_transition_unix_leap_time <= unix_leap_time_before && unix_leap_time_before < transition.unix_leap_time() {
                UtcDateTime::check_unix_time(unix_time_before)?;
                found_date_times.push(FoundDateTimeKind::Normal(new_datetime(local_time_type_before, unix_time_before)));
            } else {
                // The last transition is ignored if no extra rules are defined
                if index < transitions.len() - 1 || extra_rule.is_some() {
                    let local_time_type_after = local_time_types[transition.local_time_type_index()];
                    let (_, unix_leap_time_after) = possible_times[transition.local_time_type_index()];

                    // Check for a forward transition
                    if unix_leap_time_before >= transition.unix_leap_time() && unix_leap_time_after < transition.unix_leap_time() {
                        let transition_unix_time = time_zone_ref.unix_leap_time_to_unix_time(transition.unix_leap_time())?;

                        found_date_times.push(FoundDateTimeKind::Skipped {
                            before_transition: DateTime::from_timespec_and_local(transition_unix_time, nanoseconds, local_time_type_before)?,
                            after_transition: DateTime::from_timespec_and_local(transition_unix_time, nanoseconds, local_time_type_after)?,
                        });
                    }
                }
            }

            previous_transition_unix_leap_time = transition.unix_leap_time();
            previous_local_time_type_index = transition.local_time_type_index();
        }
    }

    // Process extra rule
    match extra_rule {
        None => {}
        Some(TransitionRule::Fixed(local_time_type)) => {
            // Overflow is not possible
            let unix_time = utc_unix_time - local_time_type.ut_offset() as i64;

            let condition = match transitions.last() {
                Some(last_transition) => unix_time >= time_zone_ref.unix_leap_time_to_unix_time(last_transition.unix_leap_time())?,
                None => true,
            };

            if condition {
                UtcDateTime::check_unix_time(unix_time)?;
                found_date_times.push(FoundDateTimeKind::Normal(new_datetime(*local_time_type, unix_time)));
            }
        }
        Some(TransitionRule::Alternate(alternate_time)) => {
            let std_ut_offset = alternate_time.std().ut_offset() as i64;
            let dst_ut_offset = alternate_time.dst().ut_offset() as i64;

            // Overflow is not possible
            let unix_time_std = utc_unix_time - std_ut_offset;
            let unix_time_dst = utc_unix_time - dst_ut_offset;

            let dst_start_time_in_utc = alternate_time.dst_start_time() as i64 - std_ut_offset;
            let dst_end_time_in_utc = alternate_time.dst_end_time() as i64 - dst_ut_offset;

            // Check if the associated UTC date times are valid
            UtcDateTime::check_unix_time(unix_time_std)?;
            UtcDateTime::check_unix_time(unix_time_dst)?;

            // Check if the year is valid for the following computations
            if !(i32::MIN + 2 <= year && year <= i32::MAX - 2) {
                return Err(OutOfRangeError("out of range date time").into());
            }

            // Check DST start/end Unix times for previous/current/next years to support for transition day times outside of [0h, 24h] range.
            // This is sufficient since the absolute value of DST start/end time in UTC is less than 2 weeks.
            // Moreover, inconsistent DST transition rules are not allowed, so there won't be additional transitions at the year boundary.
            let mut additional_transition_times = [
                alternate_time.dst_start().unix_time(year - 1, dst_start_time_in_utc),
                alternate_time.dst_end().unix_time(year - 1, dst_end_time_in_utc),
                alternate_time.dst_start().unix_time(year, dst_start_time_in_utc),
                alternate_time.dst_end().unix_time(year, dst_end_time_in_utc),
                alternate_time.dst_start().unix_time(year + 1, dst_start_time_in_utc),
                alternate_time.dst_end().unix_time(year + 1, dst_end_time_in_utc),
                i64::MAX,
            ];

            // Sort transitions
            let sorted = additional_transition_times.windows(2).all(|x| x[0] <= x[1]);

            if !sorted {
                for chunk in additional_transition_times.chunks_exact_mut(2) {
                    chunk.swap(0, 1);
                }
            };

            let transition_start = (alternate_time.std(), alternate_time.dst(), unix_time_std, unix_time_dst);
            let transition_end = (alternate_time.dst(), alternate_time.std(), unix_time_dst, unix_time_std);

            let additional_transitions = if sorted {
                [&transition_start, &transition_end, &transition_start, &transition_end, &transition_start, &transition_end, &transition_start]
            } else {
                [&transition_end, &transition_start, &transition_end, &transition_start, &transition_end, &transition_start, &transition_end]
            };

            let mut previous_transition_unix_time = match transitions.last() {
                Some(last_transition) => time_zone_ref.unix_leap_time_to_unix_time(last_transition.unix_leap_time())?,
                None => i64::MIN,
            };

            // Check transitions in order
            if let Some(first_valid) = additional_transition_times.iter().position(|&unix_time| previous_transition_unix_time < unix_time) {
                let valid_transition_times = &additional_transition_times[first_valid..];
                let valid_transitions = &additional_transitions[first_valid..];

                let valid_iter = valid_transition_times.iter().copied().zip(valid_transitions.iter().copied());

                for (transition_unix_time, &(&local_time_type_before, &local_time_type_after, unix_time_before, unix_time_after)) in valid_iter {
                    if previous_transition_unix_time <= unix_time_before && unix_time_before < transition_unix_time {
                        found_date_times.push(FoundDateTimeKind::Normal(new_datetime(local_time_type_before, unix_time_before)));
                    } else {
                        // Check for a forward transition
                        if unix_time_before >= transition_unix_time && unix_time_after < transition_unix_time {
                            found_date_times.push(FoundDateTimeKind::Skipped {
                                before_transition: DateTime::from_timespec_and_local(transition_unix_time, nanoseconds, local_time_type_before)?,
                                after_transition: DateTime::from_timespec_and_local(transition_unix_time, nanoseconds, local_time_type_after)?,
                            });
                        }
                    }

                    previous_transition_unix_time = transition_unix_time;
                }
            }
        }
    }

    Ok(FoundDateTimeList(found_date_times))
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::datetime::test::check_equal_date_time;
    use crate::timezone::*;

    fn check_equal_option_date_time(x: &Option<DateTime>, y: &Option<DateTime>) {
        match (x, y) {
            (None, None) => (),
            (Some(x), Some(y)) => check_equal_date_time(x, y),
            _ => panic!("not equal"),
        }
    }

    enum Check {
        Normal([i32; 1]),
        Skipped([(i32, u8, u8, u8, u8, u8, i32); 2]),
    }

    fn check(
        time_zone_ref: TimeZoneRef,
        posssible_date_time_results: &[Check],
        searched: (i32, u8, u8, u8, u8, u8),
        result_indices: &[usize],
        unique: Option<[usize; 2]>,
        earlier: Option<[usize; 2]>,
        later: Option<[usize; 2]>,
    ) -> Result<()> {
        let new_date_time = |(year, month, month_day, hour, minute, second, ut_offset)| {
            Result::Ok(DateTime::new(year, month, month_day, hour, minute, second, 0, LocalTimeType::with_ut_offset(ut_offset)?)?)
        };

        let (year, month, month_day, hour, minute, second) = searched;

        let found_date_times = find_date_time(year, month, month_day, hour, minute, second, 0, time_zone_ref)?;

        let indexed_date_time = |[index_1, index_2]: [usize; 2]| match posssible_date_time_results[index_1] {
            Check::Normal(arr) => new_date_time((year, month, month_day, hour, minute, second, arr[index_2])),
            Check::Skipped(arr) => new_date_time(arr[index_2]),
        };

        check_equal_option_date_time(&found_date_times.unique(), &unique.map(indexed_date_time).transpose()?);
        check_equal_option_date_time(&found_date_times.earliest(), &earlier.map(indexed_date_time).transpose()?);
        check_equal_option_date_time(&found_date_times.latest(), &later.map(indexed_date_time).transpose()?);

        let found_date_times_inner = found_date_times.into_inner();
        assert_eq!(found_date_times_inner.len(), result_indices.len());

        for (found_date_time, &result_index) in found_date_times_inner.iter().zip(result_indices) {
            match posssible_date_time_results[result_index] {
                Check::Normal([ut_offset]) => {
                    assert_eq!(*found_date_time, FoundDateTimeKind::Normal(new_date_time((year, month, month_day, hour, minute, second, ut_offset))?));
                }
                Check::Skipped([before, after]) => {
                    let skipped = FoundDateTimeKind::Skipped { before_transition: new_date_time(before)?, after_transition: new_date_time(after)? };
                    assert_eq!(*found_date_time, skipped);
                }
            };
        }

        Ok(())
    }

    #[test]
    fn test_find_date_time_fixed() -> Result<()> {
        let local_time_type = LocalTimeType::with_ut_offset(3600)?;

        let results = &[Check::Normal([3600])];

        let time_zone_1 = TimeZone::new(vec![], vec![local_time_type], vec![], None)?;
        let time_zone_2 = TimeZone::new(vec![], vec![local_time_type], vec![], Some(TransitionRule::Fixed(local_time_type)))?;

        check(time_zone_1.as_ref(), results, (2000, 1, 1, 0, 0, 0), &[0], Some([0, 0]), Some([0, 0]), Some([0, 0]))?;
        check(time_zone_2.as_ref(), results, (2000, 1, 1, 0, 0, 0), &[0], Some([0, 0]), Some([0, 0]), Some([0, 0]))?;

        let time_zone_3 = TimeZone::new(vec![Transition::new(0, 0)], vec![local_time_type], vec![], Some(TransitionRule::Fixed(local_time_type)))?;

        check(time_zone_3.as_ref(), results, (1960, 1, 1, 0, 0, 0), &[0], Some([0, 0]), Some([0, 0]), Some([0, 0]))?;
        check(time_zone_3.as_ref(), results, (1980, 1, 1, 0, 0, 0), &[0], Some([0, 0]), Some([0, 0]), Some([0, 0]))?;

        Ok(())
    }

    #[test]
    fn test_find_date_time_no_offset() -> Result<()> {
        let local_time_types = [
            LocalTimeType::new(0, false, Some(b"STD1"))?,
            LocalTimeType::new(0, true, Some(b"DST1"))?,
            LocalTimeType::new(0, false, Some(b"STD2"))?,
            LocalTimeType::new(0, true, Some(b"DST2"))?,
        ];

        let time_zone = TimeZone::new(
            vec![Transition::new(3600, 1), Transition::new(7200, 2)],
            local_time_types.to_vec(),
            vec![],
            Some(TransitionRule::Alternate(AlternateTime::new(
                local_time_types[2],
                local_time_types[3],
                RuleDay::Julian0WithLeap(Julian0WithLeap::new(0)?),
                10800,
                RuleDay::Julian0WithLeap(Julian0WithLeap::new(0)?),
                14400,
            )?)),
        )?;

        let time_zone_ref = time_zone.as_ref();

        assert_eq!(local_time_types[0], *find_date_time(1970, 1, 1, 0, 30, 0, 0, time_zone_ref)?.unique().unwrap().local_time_type());
        assert_eq!(local_time_types[1], *find_date_time(1970, 1, 1, 1, 30, 0, 0, time_zone_ref)?.unique().unwrap().local_time_type());
        assert_eq!(local_time_types[2], *find_date_time(1970, 1, 1, 2, 30, 0, 0, time_zone_ref)?.unique().unwrap().local_time_type());
        assert_eq!(local_time_types[3], *find_date_time(1970, 1, 1, 3, 30, 0, 0, time_zone_ref)?.unique().unwrap().local_time_type());
        assert_eq!(local_time_types[2], *find_date_time(1970, 1, 1, 4, 30, 0, 0, time_zone_ref)?.unique().unwrap().local_time_type());

        Ok(())
    }

    #[test]
    fn test_find_date_time_extra_rule_only() -> Result<()> {
        let time_zone = TimeZone::new(
            vec![],
            vec![LocalTimeType::utc(), LocalTimeType::with_ut_offset(3600)?],
            vec![],
            Some(TransitionRule::Alternate(AlternateTime::new(
                LocalTimeType::utc(),
                LocalTimeType::with_ut_offset(3600)?,
                RuleDay::Julian1WithoutLeap(Julian1WithoutLeap::new(1)?),
                7200,
                RuleDay::Julian1WithoutLeap(Julian1WithoutLeap::new(1)?),
                12600,
            )?)),
        )?;

        let time_zone_ref = time_zone.as_ref();

        let results = &[
            Check::Normal([0]),
            Check::Normal([3600]),
            Check::Skipped([(2000, 1, 1, 2, 0, 0, 0), (2000, 1, 1, 3, 0, 0, 3600)]),
            Check::Skipped([(2010, 1, 1, 2, 0, 0, 0), (2010, 1, 1, 3, 0, 0, 3600)]),
        ];

        check(time_zone_ref, results, (2000, 1, 1, 1, 45, 0), &[0], Some([0, 0]), Some([0, 0]), Some([0, 0]))?;
        check(time_zone_ref, results, (2000, 1, 1, 2, 15, 0), &[2], None, Some([2, 0]), Some([2, 1]))?;
        check(time_zone_ref, results, (2000, 1, 1, 2, 45, 0), &[2, 0], None, Some([2, 0]), Some([0, 0]))?;
        check(time_zone_ref, results, (2000, 1, 1, 3, 15, 0), &[1, 0], None, Some([1, 0]), Some([0, 0]))?;
        check(time_zone_ref, results, (2000, 1, 1, 3, 45, 0), &[0], Some([0, 0]), Some([0, 0]), Some([0, 0]))?;

        check(time_zone_ref, results, (2010, 1, 1, 1, 45, 0), &[0], Some([0, 0]), Some([0, 0]), Some([0, 0]))?;
        check(time_zone_ref, results, (2010, 1, 1, 2, 15, 0), &[3], None, Some([3, 0]), Some([3, 1]))?;
        check(time_zone_ref, results, (2010, 1, 1, 2, 45, 0), &[3, 0], None, Some([3, 0]), Some([0, 0]))?;
        check(time_zone_ref, results, (2010, 1, 1, 3, 15, 0), &[1, 0], None, Some([1, 0]), Some([0, 0]))?;
        check(time_zone_ref, results, (2010, 1, 1, 3, 45, 0), &[0], Some([0, 0]), Some([0, 0]), Some([0, 0]))?;

        Ok(())
    }

    #[test]
    fn test_find_date_time_transitions_only() -> Result<()> {
        let time_zone = TimeZone::new(
            vec![
                Transition::new(0, 0),
                Transition::new(7200, 1),
                Transition::new(14400, 2),
                Transition::new(25200, 3),
                Transition::new(28800, 4),
                Transition::new(32400, 0),
            ],
            vec![
                LocalTimeType::new(0, false, None)?,
                LocalTimeType::new(3600, false, None)?,
                LocalTimeType::new(-10800, false, None)?,
                LocalTimeType::new(-19800, false, None)?,
                LocalTimeType::new(-16200, false, None)?,
            ],
            vec![],
            None,
        )?;

        let time_zone_ref = time_zone.as_ref();

        let results = &[
            Check::Normal([0]),
            Check::Normal([3600]),
            Check::Normal([-10800]),
            Check::Normal([-19800]),
            Check::Normal([-16200]),
            Check::Skipped([(1970, 1, 1, 2, 0, 0, 0), (1970, 1, 1, 3, 0, 0, 3600)]),
            Check::Skipped([(1970, 1, 1, 2, 30, 0, -19800), (1970, 1, 1, 3, 30, 0, -16200)]),
        ];

        check(time_zone_ref, results, (1970, 1, 1, 0, 0, 0), &[0], Some([0, 0]), Some([0, 0]), Some([0, 0]))?;
        check(time_zone_ref, results, (1970, 1, 1, 1, 0, 0), &[0, 2], None, Some([0, 0]), Some([2, 0]))?;
        check(time_zone_ref, results, (1970, 1, 1, 1, 15, 0), &[0, 2], None, Some([0, 0]), Some([2, 0]))?;
        check(time_zone_ref, results, (1970, 1, 1, 1, 30, 0), &[0, 2, 3], None, Some([0, 0]), Some([3, 0]))?;
        check(time_zone_ref, results, (1970, 1, 1, 1, 45, 0), &[0, 2, 3], None, Some([0, 0]), Some([3, 0]))?;
        check(time_zone_ref, results, (1970, 1, 1, 2, 0, 0), &[5, 2, 3], None, Some([5, 0]), Some([3, 0]))?;
        check(time_zone_ref, results, (1970, 1, 1, 2, 15, 0), &[5, 2, 3], None, Some([5, 0]), Some([3, 0]))?;
        check(time_zone_ref, results, (1970, 1, 1, 2, 30, 0), &[5, 2, 6], None, Some([5, 0]), Some([6, 1]))?;
        check(time_zone_ref, results, (1970, 1, 1, 2, 45, 0), &[5, 2, 6], None, Some([5, 0]), Some([6, 1]))?;
        check(time_zone_ref, results, (1970, 1, 1, 3, 0, 0), &[1, 2, 6], None, Some([1, 0]), Some([6, 1]))?;
        check(time_zone_ref, results, (1970, 1, 1, 3, 15, 0), &[1, 2, 6], None, Some([1, 0]), Some([6, 1]))?;
        check(time_zone_ref, results, (1970, 1, 1, 3, 30, 0), &[1, 2, 4], None, Some([1, 0]), Some([4, 0]))?;
        check(time_zone_ref, results, (1970, 1, 1, 3, 45, 0), &[1, 2, 4], None, Some([1, 0]), Some([4, 0]))?;
        check(time_zone_ref, results, (1970, 1, 1, 4, 0, 0), &[1, 4], None, Some([1, 0]), Some([4, 0]))?;
        check(time_zone_ref, results, (1970, 1, 1, 4, 15, 0), &[1, 4], None, Some([1, 0]), Some([4, 0]))?;
        check(time_zone_ref, results, (1970, 1, 1, 4, 30, 0), &[1], Some([1, 0]), Some([1, 0]), Some([1, 0]))?;
        check(time_zone_ref, results, (1970, 1, 1, 4, 45, 0), &[1], Some([1, 0]), Some([1, 0]), Some([1, 0]))?;
        check(time_zone_ref, results, (1970, 1, 1, 5, 0, 0), &[], None, None, None)?;

        Ok(())
    }

    #[test]
    fn test_find_date_time_transitions_with_extra_rule() -> Result<()> {
        let time_zone = TimeZone::new(
            vec![Transition::new(0, 0), Transition::new(3600, 1), Transition::new(7200, 0), Transition::new(10800, 2)],
            vec![LocalTimeType::utc(), LocalTimeType::with_ut_offset(i32::MAX)?, LocalTimeType::with_ut_offset(3600)?],
            vec![],
            Some(TransitionRule::Alternate(AlternateTime::new(
                LocalTimeType::utc(),
                LocalTimeType::with_ut_offset(3600)?,
                RuleDay::Julian1WithoutLeap(Julian1WithoutLeap::new(300)?),
                0,
                RuleDay::Julian1WithoutLeap(Julian1WithoutLeap::new(90)?),
                3600,
            )?)),
        )?;

        let time_zone_ref = time_zone.as_ref();

        let results = &[
            Check::Normal([0]),
            Check::Normal([3600]),
            Check::Normal([i32::MAX]),
            Check::Skipped([(1970, 1, 1, 1, 0, 0, 0), (2038, 1, 19, 4, 14, 7, i32::MAX)]),
            Check::Skipped([(1970, 1, 1, 3, 0, 0, 0), (1970, 1, 1, 4, 0, 0, 3600)]),
            Check::Skipped([(1970, 10, 27, 0, 0, 0, 0), (1970, 10, 27, 1, 0, 0, 3600)]),
            Check::Skipped([(2000, 10, 27, 0, 0, 0, 0), (2000, 10, 27, 1, 0, 0, 3600)]),
            Check::Skipped([(2030, 10, 27, 0, 0, 0, 0), (2030, 10, 27, 1, 0, 0, 3600)]),
            Check::Skipped([(2038, 10, 27, 0, 0, 0, 0), (2038, 10, 27, 1, 0, 0, 3600)]),
        ];

        check(time_zone_ref, results, (1970, 1, 1, 0, 30, 0), &[0], Some([0, 0]), Some([0, 0]), Some([0, 0]))?;
        check(time_zone_ref, results, (1970, 1, 1, 1, 30, 0), &[3], None, Some([3, 0]), Some([3, 1]))?;
        check(time_zone_ref, results, (1970, 1, 1, 2, 30, 0), &[3, 0], None, Some([3, 0]), Some([0, 0]))?;
        check(time_zone_ref, results, (1970, 1, 1, 3, 30, 0), &[3, 4], None, Some([3, 0]), Some([4, 1]))?;
        check(time_zone_ref, results, (1970, 1, 1, 4, 30, 0), &[3, 1], None, Some([3, 0]), Some([1, 0]))?;

        check(time_zone_ref, results, (1970, 2, 1, 0, 0, 0), &[3, 1], None, Some([3, 0]), Some([1, 0]))?;
        check(time_zone_ref, results, (1970, 3, 31, 0, 30, 0), &[3, 1, 0], None, Some([3, 0]), Some([0, 0]))?;
        check(time_zone_ref, results, (1970, 6, 1, 0, 0, 0), &[3, 0], None, Some([3, 0]), Some([0, 0]))?;
        check(time_zone_ref, results, (1970, 10, 27, 0, 30, 0), &[3, 5], None, Some([3, 0]), Some([5, 1]))?;
        check(time_zone_ref, results, (1970, 11, 1, 0, 0, 0), &[3, 1], None, Some([3, 0]), Some([1, 0]))?;

        check(time_zone_ref, results, (2000, 2, 1, 0, 0, 0), &[3, 1], None, Some([3, 0]), Some([1, 0]))?;
        check(time_zone_ref, results, (2000, 3, 31, 0, 30, 0), &[3, 1, 0], None, Some([3, 0]), Some([0, 0]))?;
        check(time_zone_ref, results, (2000, 6, 1, 0, 0, 0), &[3, 0], None, Some([3, 0]), Some([0, 0]))?;
        check(time_zone_ref, results, (2000, 10, 27, 0, 30, 0), &[3, 6], None, Some([3, 0]), Some([6, 1]))?;
        check(time_zone_ref, results, (2000, 11, 1, 0, 0, 0), &[3, 1], None, Some([3, 0]), Some([1, 0]))?;

        check(time_zone_ref, results, (2030, 2, 1, 0, 0, 0), &[3, 1], None, Some([3, 0]), Some([1, 0]))?;
        check(time_zone_ref, results, (2030, 3, 31, 0, 30, 0), &[3, 1, 0], None, Some([3, 0]), Some([0, 0]))?;
        check(time_zone_ref, results, (2030, 6, 1, 0, 0, 0), &[3, 0], None, Some([3, 0]), Some([0, 0]))?;
        check(time_zone_ref, results, (2030, 10, 27, 0, 30, 0), &[3, 7], None, Some([3, 0]), Some([7, 1]))?;
        check(time_zone_ref, results, (2030, 11, 1, 0, 0, 0), &[3, 1], None, Some([3, 0]), Some([1, 0]))?;

        check(time_zone_ref, results, (2038, 1, 19, 5, 0, 0), &[2, 1], None, Some([2, 0]), Some([1, 0]))?;
        check(time_zone_ref, results, (2038, 2, 1, 0, 0, 0), &[1], Some([1, 0]), Some([1, 0]), Some([1, 0]))?;
        check(time_zone_ref, results, (2038, 3, 31, 0, 30, 0), &[1, 0], None, Some([1, 0]), Some([0, 0]))?;
        check(time_zone_ref, results, (2038, 6, 1, 0, 0, 0), &[0], Some([0, 0]), Some([0, 0]), Some([0, 0]))?;
        check(time_zone_ref, results, (2038, 10, 27, 0, 30, 0), &[8], None, Some([8, 0]), Some([8, 1]))?;
        check(time_zone_ref, results, (2038, 11, 1, 0, 0, 0), &[1], Some([1, 0]), Some([1, 0]), Some([1, 0]))?;

        Ok(())
    }
}
