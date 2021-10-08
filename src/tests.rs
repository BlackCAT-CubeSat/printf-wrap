// Copyright (c) 2021 The Pennsylvania State University. All rights reserved.

//! Tests of the crate's functionality.

#![cfg(test)]

use libc::{c_char, c_int, c_ulonglong};
use crate::NullString;

macro_rules! generate_construction_panic_case {
    ( $( $fn_name:ident, $str:expr, $args:tt ; )* ) => {
        $( generate_construction_panic_case!(@ $fn_name, $str, $args); )*
    };

    ( @ $fn_name:ident, $str:expr, ( $($arg:ty),* ) ) => {
        #[test]
        #[should_panic]
        fn $fn_name() {
            use $crate::PrintfFmt;

            let fmt: PrintfFmt<($($arg ,)*)>
                = PrintfFmt::new_or_panic(concat!($str, "\0"));
            assert!(!(fmt.as_ptr().is_null()));
        }
    };
}

generate_construction_panic_case! {
    not_enough_conversions, " %d %d ",     (c_int, c_int, c_int);
    too_many_conversions,   "  %d %d %d ", (c_int, c_int);
    wrong_order,            " %s %d ",     (c_int, NullString);
    improper_percent,       " %% %d ",     (c_char, c_int);

    no_needed_star,         " %llx ",      ((c_int, c_ulonglong));
    too_many_stars_str,     " %*.*s ",     (&str);
    not_enough_stars_str,   " %s ",        (&str);
    no_precision_str,       " %*s ",       (&str);
}

macro_rules! generate_successful_case {
    ( $( $fn_name:ident, $str:expr, $args:tt ; )* ) => {
        $( generate_successful_case!(@ $fn_name, $str, $args); )*
    };

    ( @ $fn_name:ident, $str:expr, ( $($arg:ty),* ) ) => {
        #[test]
        fn $fn_name() {
            match $crate::PrintfFmt::<($($arg ,)*)>::new(concat!($str, "\0")) {
                Ok(fmt) => { assert!(!(fmt.as_ptr().is_null())); }
                Err(_)  => { panic!("Format that should work isn\'t!"); }
            }
        }
    };
}

generate_successful_case! {
    no_conversions,        " test format string ",  ();
    percent_escape,        "test of %% - %%",       ();
    one_int,               "there are %d lights",   (c_int);
    int_with_width,        "%5d bananas",           (c_int);

    int_with_flags,        "% 05ddays",             (c_int);
    int_with_precision,    "%.6d",                  (c_int);
    int_width_precision,   "%14.2d",                (c_int);
    int_starred_width,     "%*d",                   ((c_int, c_int));

    int_starred_precision, "%5.*d",                 ((c_int, c_int));
    null_string_basic,     "The %s Show",           (NullString);
    nullstr_star_prec,     "[<=n chars: %.*s]",     ((c_int, NullString));
    str_usage,             "Need * precision: %.*s", (&str);

    two_conversions,       "%d * %c",               (c_int, c_char);
}
