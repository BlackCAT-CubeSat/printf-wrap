// Copyright (c) 2021 The Pennsylvania State University. All rights reserved.

//! Types and whatnot for safe use of printf(3)-style format strings.

#![no_std]

// We use `libc` for types.
extern crate libc;

use core::ffi::c_void;
use libc::c_char;

/// An empty null-terminated string.
const EMPTY_C_STRING: [c_char; 1] = [b'\0' as c_char];

/// Information about how a type may be used with C's printf(3)
/// and similar functions.
pub trait PrintfArgument: Sized {
    /// Whether the type is consistent with C's `char`.
    const IS_CHAR: bool = false;
    /// Whether the type is consistent with C's `short int`.
    const IS_SHORT: bool = false;
    /// Whether the type is consistent with C's `int`.
    const IS_INT: bool = false;
    /// Whether the type is consistent with C's `long int`.
    const IS_LONG: bool = false;
    /// Whether the type is consistent with C's `long long int`.
    const IS_LONG_LONG: bool = false;
    /// Whether the type is consistent with C's `size_t`.
    const IS_SIZE: bool = false;
    /// Whether the type is consistent with C's `intmax_t`.
    const IS_MAX: bool = false;
    /// Whether the type is consistent with C's `ptrdiff_t`.
    const IS_PTRDIFF: bool = false;

    /// Whether the type is a signed integer type, as opposed to unsigned.
    const IS_SIGNED: bool = false;

    /// Whether the type is floating-point.
    const IS_FLOAT: bool = false;

    /// Whether the type is a slice of bytes.
    const IS_BYTE_SLICE: bool = false;

    /// Provides `self` as a slice length and `*const u8` to the start
    /// of the slice.
    /// Only expected to be meaningful if `IS_BYTE_SLICE == true`.
    #[inline]
    fn as_byte_slice(self) -> (usize, *const u8) {
        const EMPTY_ARRAY: [u8; 0] = [];
        let p: &'static [u8] = &EMPTY_ARRAY;
        (p.len(), p.as_ptr())
    }

    /// Whether the type is a null-terminated string.
    const IS_C_STRING: bool = false;

    /// Provides `self` as a [`*const c_char`] to a null-terminated (C-style)
    /// string.
    /// Only expected to be meaningful if `IS_C_STRING == true`.
    #[inline]
    fn as_c_string(self) -> *const c_char {
        EMPTY_C_STRING.as_ptr()
    }

    /// Whether the type is a pointer.
    const IS_POINTER: bool = false;

    /// Provides `self` as a [`*const c_void`].
    /// Only expected to be meaningful if `IS_POINTER == true`.
    #[inline]
    fn as_pointer(self) -> *const c_void {
        EMPTY_C_STRING.as_ptr() as *const c_void
    }
}

/// Are types `T` and `U` ABI-compatible, in the sense that using
/// one in the place of the other wouldn't affect structure layout,
/// stack layout if used as arguments, etc.?
///
/// Note that this doesn't check for whether substituting `T` with `U` (or vice
/// versa) is sensible or even valid;
/// the use-case is for types where any bit-pattern is
/// sensible and the types don't have non-trivial drop behavior.
const fn is_compat<T: Sized, U: Sized>() -> bool {
    use core::mem::{size_of, align_of};

    size_of::<T>() == size_of::<U>() && align_of::<T>() == align_of::<U>()
}

macro_rules! impl_printf_arg_integer {
    ( $( $t:ty, $sign:expr );* ) => {
        $(
            impl PrintfArgument for $t {
                const IS_SIGNED: bool = $sign;

                const IS_CHAR: bool      = is_compat::<$t, libc::c_char>();
                const IS_SHORT: bool     = is_compat::<$t, libc::c_short>();
                const IS_INT: bool       = is_compat::<$t, libc::c_int>();
                const IS_LONG: bool      = is_compat::<$t, libc::c_long>();
                const IS_LONG_LONG: bool = is_compat::<$t, libc::c_longlong>();

                const IS_SIZE: bool      = is_compat::<$t, libc::size_t>();
                const IS_MAX: bool       = is_compat::<$t, libc::intmax_t>();
                const IS_PTRDIFF: bool   = is_compat::<$t, libc::ptrdiff_t>();
            }
        )*
    };
}

impl_printf_arg_integer! {
    u8,   false;
    i8,   true;
    u16,  false;
    i16,  true;
    u32,  false;
    i32,  true;
    u64,  false;
    i64,  true;
    u128, false;
    i128, true;

    usize, false;
    isize, true
}

impl PrintfArgument for f32 {
    const IS_FLOAT: bool = true;
}

impl PrintfArgument for f64 {
    const IS_FLOAT: bool = true;
}

impl PrintfArgument for &[u8] {
    const IS_BYTE_SLICE: bool = true;

    #[inline]
    fn as_byte_slice(self) -> (usize, *const u8) {
        (self.len(), self.as_ptr())
    }

    const IS_POINTER: bool = true;

    #[inline]
    fn as_pointer(self) -> *const c_void {
        self.as_ptr() as *const c_void
    }
}

impl PrintfArgument for &[i8] {
    const IS_BYTE_SLICE: bool = true;

    #[inline]
    fn as_byte_slice(self) -> (usize, *const u8) {
        (self.len(), self.as_ptr() as *const u8)
    }

    const IS_POINTER: bool = true;

    #[inline]
    fn as_pointer(self) -> *const c_void {
        self.as_ptr() as *const c_void
    }
}

impl<T: Sized> PrintfArgument for *const T {
    const IS_POINTER: bool = true;

    #[inline]
    fn as_pointer(self) -> *const c_void {
        self as *const c_void
    }
}

impl<T: Sized> PrintfArgument for *mut T {
    const IS_POINTER: bool = true;

    #[inline]
    fn as_pointer(self) -> *const c_void {
        (self as *const T) as *const c_void
    }
}

mod private {
}

//pub const fn<T>

/// The type content of a printf(3) conversion specification (excepting "`%%`"):
/// the parts that define the number and types of arguments that are consumed.
struct ConversionSpecification {
    width_is_arg: bool,
    precision_is_arg: bool,
    length_modifier: Option<LengthModifier>,
    conversion: c_char,
}

/// A length modifier in a printf(3) conversion specifier.
enum LengthModifier {
    /// `hh`
    Char,
    /// `h`
    Short,
    /// `l`
    Long,
    /// `ll`
    LongLong,
    /// `L`
    LongDouble,
    /// `j`
    Max,
    /// `z`
    Size,
    /// `t`
    Ptrdiff,
}

const fn c(x: u8) -> c_char { x as c_char }

/// Returns the index of the initial '`%`'
/// of the next non-`%%` conversion specifier, if present;
/// else returns `None`.
const fn next_conversion_specifier(fmt: &[c_char]) -> Option<usize> {
    const PCT: c_char = b'%' as c_char;

    let len = fmt.len();
    let mut i: usize = 0;

    if len == 0 { return None; }

    while i < len {
        if fmt[i] == c(b'%') {
            if i < len-1 && fmt[i+1] == c(b'%') { // skip over '%%':
                i += 2;
            } else {
                return Some(i);
            }
        } else {
            i += 1;
        }
    }

    // if we get here, we got to the end of the string without hitting a
    // conversion specifier:
    None
}

/// Is `s` (a candidate for being a C string) null-terminated?
const fn is_null_terminated(s: &[c_char]) -> bool {
    s.len() > 0 && s[s.len() - 1] == c(b'\0')
}


#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
