// Copyright (c) 2021 The Pennsylvania State University. All rights reserved.

//! Tests of the crate's functionality.

#![cfg(test)]

use libc::{c_char, c_uchar, c_ushort, c_int, c_uint, c_long, c_ulonglong};
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
    no_conversions,        " test format string ", ();
    percent_escape,        "test of %% - %%",      ();
    one_int,               "there are %d lights",  (c_int);
    int_with_width,        "%5d bananas",          (c_int);

    int_with_flags,        "% 03ddays",            (c_int);
    int_with_precision,    "%.6d",                 (c_int);
    int_width_precision,   "%14.2d",               (c_int);
    int_starred_width,     "%*d",                  ((c_int, c_int));

    int_starred_precision, "%5.*d",                ((c_int, c_int));
    null_string_basic,     "The %s Show",          (NullString);
    nullstr_star_prec,     "[<=n chars: %.*s]",    ((c_int, NullString));
    str_usage,             "Need * precision: %.*s", (&str);

    two_conversions,       "%d * %c",              (c_int, c_uchar);
    two_conv_and_one_star, "%x * %.*s",            (c_uint, (c_int, NullString));
    conv_with_percent,     "Progress: %d%%",       (c_uint);
    octal_conv,            "mode: %04o\n",         (c_uint);

    char_int_conv,         "%hhu",                 (c_char);
    short_int_conv,        "%hx",                  (c_ushort);
    long_conv,             "%ld",                  (c_long);
    long_long_conv,        "%llX",                 (c_ulonglong);

    length_with_star,      "%*llu",                ((c_int, c_ulonglong));
    str_with_padding,      "%10.*s",               (&str);
    pointer_conv,          "at address %p",        (*const u32);
    f32_conv,              "cost: %5.2g",          (f32);
    f64_conv,              "cost: %5.2f",          (f64);

    complex_conversion,    "(%08.*x, %F, %%, %s)", ((c_int, c_uint), f64, NullString);
}

/// Tests checking that we are indeed passing arguments the right way
/// to the C function we're wrapping, using snprintf(3) as our guinea pig.
mod abi_check {
    use crate::example::*;

    #[allow(unused_imports)]
    use libc::{c_char, c_uchar, c_short, c_ushort, c_int, c_uint,
               c_long, c_ulong, c_longlong, c_ulonglong};

    macro_rules! test_using_snprintf {
        ($( $fn_name:ident, $snprintf_variant:ident, $fmt:expr, $args:tt :
            $buf_sz:expr, $expected:expr ;)*) => {
            $(
                test_using_snprintf!(@ $fn_name, $snprintf_variant, $fmt, $args:
                                       $buf_sz, $expected);
            )*
        };

        (@ $fn_name:ident, $snprintf_variant:ident, $fmt:expr, ( $($arg:expr),* ) :
           $buf_sz:expr, $expected:expr) => {
            #[test]
            #[allow(non_snake_case)]
            fn $fn_name() {
                // b'\t' is used as a byte value that won't be written by
                // snprintf(3) given the format strings we use.
                let mut buf: [u8; $buf_sz] = [b'\t'; $buf_sz];
                let p: &mut [u8] = &mut buf[..];

                $snprintf_variant(
                    p,
                    $crate::PrintfFmt::new(concat!($fmt, "\0")).unwrap(),
                    $( $arg ),*
                );
                assert_eq!(p, $expected, "snprintf was not given the arguments correctly");
            }
        };
    }

    test_using_snprintf! {
        args_nil,  snprintf0, "fmt!", ():
            6, b"fmt!\0\t";
        args_c, snprintf1, "x%cz", (b'y' as c_char):
            5, b"xyz\0\t";
        args_cc, snprintf2, "a%cc%ce", (b'B' as c_char, b'D' as c_char):
            8, b"aBcDe\0\t\t";
        args_d, snprintf1, " %dc", (-5 as c_int):
            7, b" -5c\0\t\t";
        args_dd, snprintf2, ":%X,%d", (42 as c_uint, 3 as c_int):
            8, b":2A,3\0\t\t";
        args_dcdcd, snprintf5, "%d%c%d%c%d",
            (1 as c_int, b'A' as c_char, 2 as c_int, b'B' as c_char, 3 as c_int):
            8, b"1A2B3\0\t\t";
        args_f, snprintf1, "A%.1f ", (2.0f64):
            8, b"A2.0 \0\t\t";

        // These are the *really* important tests in this set:
        // making sure our uses of structs in a couple of places play well
        // with the calling convention...

        args_Xd, snprintf1, "%*d", ((6 as c_int, -4 as c_int)):
            8, b"    -4\0\t";
        args_Xf, snprintf1, "X%.*fX", ((3 as c_int, 2.0f64)):
            9, b"X2.000X\0\t";
        args_Xs, snprintf1, " :%.*s: ", ("hello!"):
            13, b" :hello!: \0\t\t";
        args_XfXf, snprintf2, ":%.*f:%.*f:",
            ((4 as c_int, 2.0f64), (2 as c_int, 2.5f64)):
            17, b":2.0000:2.50:\0\t\t\t";
        args_ddXd, snprintf3, ":%d:%u:%*d:",
            (1 as c_int, 2 as c_uint, (6 as c_int, 3 as c_int)):
            16, b":1:2:     3:\0\t\t\t";
        args_ccXd, snprintf3, ":%c:%c:%*d:",
            (b'a' as c_char, b'b' as c_char, (6 as c_int, 5 as c_uint)):
            19, b":a:b:     5:\0\t\t\t\t\t\t";
        args_ddXf, snprintf3, ":%d:%d:%*f:",
            (10 as c_int, -1 as c_int, (5 as c_int, 2.0f32)):
            15, b":10:-1:    2:\0\t";
        args_ddXs, snprintf3, ":%u:%u:%.*s:",
            (42 as c_uint, 9 as c_uint, "test"):
            14, b":42:9:test:\0\t\t";
        args_dXfd, snprintf3, ":04%o:%*f:%d:",
            (32 as c_uint, (5 as c_int, 2.5f64), 32 as c_int):
            18, b":0040:  2.5:32:\0\t\t";
        args_dXsd, snprintf3, ":%d:%.*s:%d:", (32 as c_int, "hi!", 4 as c_int):
            13, b":32:hi!:4:\0\t\t";

        args_cddXdd, snprintf5, ":%c:%d:%d:%*d:%d:",
            (b'@' as c_char, 1 as c_int, 2 as c_int, (5 as c_int, 3 as c_int), 4 as c_int):
            18, b":@:1:2:    3:4:\0\t\t";
        args_dddXfd, snprintf5, ":%d:%d:%d:%*f:%d:",
            (1 as c_int, 2 as c_int, 3 as c_int, (3 as c_int, 4.0f32), 5 as c_int):
            16, b":1:2:3:  4:5:\0\t\t";
        args_ddXfdd, snprintf5, ":%d:%d:%*f:%d:%d:",
            (1 as c_int, 2 as c_int, (3 as c_int, 3.0f32), 4 as c_int, 5 as c_int):
            16, b":1:2:  3:4:5:\0\t\t";
        args_dddddXd, snprintf6, ":%d:%d:%d:%d:%d:%*d:",
            (1 as c_int, 2 as c_int, 3 as c_int, 4 as c_int, 5 as c_int, (6 as c_int, 6 as c_int)):
            21, b":1:2:3:4:5:     6:\0\t\t";
        args_dddXs, snprintf4, ":%d:%d:%d:%.*s",
            (1 as c_int, 2 as c_int, 3 as c_int, "hi there!"):
            20, b":1:2:3:hi there!:\0\t\t";

        args_cddddXdd, snprintf7, ":%c:%d:%d:%d:%d:%*d:%d:",
            (b'^' as c_char, 1 as c_int, 2 as c_int, 3 as c_int, 4 as c_int,
             (5 as c_int, -40 as c_int), 6 as c_int):
            22, b":^:1:2:3:4:  -40:6:\0\t\t";
        args_dddXfddd, snprintf7, ":%d:%d:%d:%*f:%d:%d:%d:",
            (1 as c_int, 2 as c_int, 3 as c_int, (5 as c_int, -2.0f64),
             7 as c_int, 8 as c_int, 9 as c_int):
            22, b":1:2:3:   -2:7:8:9:\0\t\t";
    }
}
