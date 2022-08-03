//! An example of how to use the types and traits of this crate to safely
//! wrap functions with `printf(3)`-style format strings and varargs.

use crate::{PrintfArgument, PrintfFmt};
use libc::{c_char, c_int};

macro_rules! tuple_impl {
    ($num:tt, $p_name:ident, $snp_name:ident, ( $($t:ident),* ), ( $($var:ident),* )) => {
        #[doc = concat!("A safe wrapper around [`printf`](libc::printf) for ", stringify!($num), " argument(s).")]
        #[inline]
        pub fn $p_name<$($t),*>(fmt: PrintfFmt<($($t,)*)>, $($var: $t),*) -> c_int
            where $($t: PrintfArgument),* {

            unsafe {
                libc::printf(fmt.as_ptr() $(, $var.as_c_val())* )
            }
        }

        #[doc = concat!("A safe wrapper around [`snprintf`](libc::snprintf) for ", stringify!($num), " argument(s).")]
        #[inline]
        pub fn $snp_name<$($t),*>(dst: &mut [u8], fmt: PrintfFmt<($($t,)*)>, $($var: $t),*) -> c_int
            where $($t: PrintfArgument),* {

            unsafe {
                libc::snprintf(
                    dst.as_mut_ptr() as *mut c_char,
                    dst.len(),
                    fmt.as_ptr()
                    $(, $var.as_c_val())*
                )
            }
        }
    };
}

tuple_impl!(0, printf0, snprintf0, (), ());
tuple_impl!(1, printf1, snprintf1, (A), (a));
tuple_impl!(2, printf2, snprintf2, (A, B), (a, b));
tuple_impl!(3, printf3, snprintf3, (A, B, C), (a, b, c));
tuple_impl!(4, printf4, snprintf4, (A, B, C, D), (a, b, c, d));
tuple_impl!(5, printf5, snprintf5, (A, B, C, D, E), (a, b, c, d, e));
tuple_impl!(6, printf6, snprintf6, (A, B, C, D, E, F), (a, b, c, d, e, f));
tuple_impl!(7, printf7, snprintf7, (A, B, C, D, E, F, G), (a, b, c, d, e, f, g));
tuple_impl!(8, printf8, snprintf8, (A, B, C, D, E, F, G, H), (a, b, c, d, e, f, g, h));

#[cfg(test)]
mod tests {
    use super::*;
    use crate::PrintfFmt;

    #[test]
    fn snprintf_test_invocation() {
        let mut x: [u8; 12] = [5u8; 12];

        assert_eq!(
            snprintf2(&mut x[..], PrintfFmt::new("X %u Y %c\0").unwrap(), 15u32, b'Z'),
            8,
            "snprintf2 return value should be 8"
        );
        assert_eq!(&x, b"X 15 Y Z\0\x05\x05\x05", "contents of x");
    }

    #[test]
    fn snprintf_no_buffer_overflow() {
        let mut x: [u8; 8] = [5u8; 8];
        assert_eq!(
            snprintf1(&mut x[..4], PrintfFmt::new("a%d \0").unwrap(), -100),
            6,
            "snprintf1 return value should be 6"
        );
        assert_eq!(&x[4..], [5u8; 4], "only 4 bytes should have been written by snprintf1");
    }
}
