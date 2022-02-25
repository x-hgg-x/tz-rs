use tz::datetime::*;
use tz::statics::*;
use tz::timezone::*;
use tz::Result;

macro_rules! unwrap {
    ($x:expr) => {
        match $x {
            Ok(x) => x,
            Err(error) => panic!("{}", error.0),
        }
    };
}

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

const UTC: StaticTimeZone = StaticTimeZone::utc();

const UNIX_EPOCH: UtcDateTime = unwrap!(UtcDateTime::from_unix_time(0));
const UTC_DATE_TIME: UtcDateTime = unwrap!(UtcDateTime::new(2000, 0, 1, 0, 0, 0));

const DATE_TIME_1: StaticDateTime = unwrap!(UTC_DATE_TIME.project_const(&TIME_ZONE));
const DATE_TIME_2: StaticDateTime = unwrap!(DATE_TIME_1.project(&UTC));

fn main() -> Result<()> {
    println!("{:#?}", TIME_ZONE);
    println!("{:?}", TIME_ZONE.find_local_time_type(0));

    println!("{:?}", UNIX_EPOCH);
    println!("{:?}", UTC_DATE_TIME);

    println!("{:#?}", DATE_TIME_1);
    println!("{:#?}", DATE_TIME_2);

    Ok(())
}
