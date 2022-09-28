// Copyright (c) 2021-2022 The Pennsylvania State University and the project contributors.
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Implementations of [`PrintfArgument`] and allied traits.

use crate::{is_compat, LargerOf, NullString};
use crate::{PrintfArgument, PrintfArgumentPrivate};

use core::ffi::{c_char, c_double, c_int, c_uint, c_void, CStr};

macro_rules! impl_empty_trait {
    ($trait_name:ident ; $($implementor:ty),*) => {
        $(
            impl $trait_name for $implementor { }
        )*
    };
}

impl_empty_trait!(PrintfArgumentPrivate;
    u8, u16, u32, u64, usize, i8, i16, i32, i64, isize, f32, f64,
    NullString
);

macro_rules! impl_printf_arg_integer {
    ( $( $t:ty, $signed:expr, $int_type:ty );* ) => {
        $(
            impl PrintfArgument for $t {
                const IS_SIGNED: bool = $signed;

                const IS_CHAR: bool      = is_compat::<$t, core::ffi::c_char>();
                const IS_SHORT: bool     = is_compat::<$t, core::ffi::c_short>();
                const IS_INT: bool       = is_compat::<$t, core::ffi::c_int>();
                const IS_LONG: bool      = is_compat::<$t, core::ffi::c_long>();
                const IS_LONG_LONG: bool = is_compat::<$t, core::ffi::c_longlong>();

                #[cfg(any(feature = "libc", test, all(doc, feature = "doccfg")))]
                const IS_SIZE: bool      = is_compat::<$t, libc::size_t>();

                #[cfg(any(feature = "libc", test, all(doc, feature = "doccfg")))]
                const IS_MAX: bool       = is_compat::<$t, libc::intmax_t>();

                #[cfg(any(feature = "libc", test, all(doc, feature = "doccfg")))]
                const IS_PTRDIFF: bool   = is_compat::<$t, libc::ptrdiff_t>();

                type CPrintfType = LargerOf<Self, $int_type>;

                #[inline]
                fn as_c_val(self) -> Self::CPrintfType {
                    self as LargerOf<Self, $int_type>
                }
            }
        )*
    };
}

impl_printf_arg_integer! {
    u8,   false, c_uint;
    i8,   true,  c_int;
    u16,  false, c_uint;
    i16,  true,  c_int;
    u32,  false, c_uint;
    i32,  true,  c_int;
    u64,  false, c_uint;
    i64,  true,  c_int;

    // explicitly not implementing for {u128, i128} (no ABI guarantees)

    usize, false, c_uint;
    isize, true,  c_int
}

impl PrintfArgument for f32 {
    const IS_FLOAT: bool = true;

    type CPrintfType = c_double;

    #[inline]
    fn as_c_val(self) -> c_double {
        self as c_double
    }
}

impl PrintfArgument for f64 {
    const IS_FLOAT: bool = true;

    type CPrintfType = c_double;

    #[inline]
    fn as_c_val(self) -> c_double {
        self as c_double
    }
}

impl PrintfArgument for NullString {
    type CPrintfType = *const c_char;

    const IS_C_STRING: bool = true;

    #[inline]
    fn as_c_val(self) -> *const c_char {
        self.as_ptr()
    }
}

impl<T: AsRef<CStr>> PrintfArgumentPrivate for &T {}

impl<T: AsRef<CStr>> PrintfArgument for &T {
    type CPrintfType = *const c_char;

    const IS_C_STRING: bool = true;

    #[inline]
    fn as_c_val(self) -> *const c_char {
        let cs: &CStr = self.as_ref();
        cs.as_ptr()
    }
}

impl<T: Sized> PrintfArgumentPrivate for *const T {}

impl<T: Sized> PrintfArgument for *const T {
    type CPrintfType = *const c_void;

    const IS_POINTER: bool = true;

    #[inline]
    fn as_c_val(self) -> *const c_void {
        self as *const c_void
    }
}

impl<T: Sized> PrintfArgumentPrivate for *mut T {}

impl<T: Sized> PrintfArgument for *mut T {
    type CPrintfType = *const c_void;

    const IS_POINTER: bool = true;

    #[inline]
    fn as_c_val(self) -> *const c_void {
        self as *mut c_void as *const c_void
    }
}
