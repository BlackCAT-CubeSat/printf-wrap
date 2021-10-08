// Copyright (c) 2021 The Pennsylvania State University. All rights reserved.

//! Implementations of [`PrintfArgument`] and allied traits.

use crate::{PrintfArgumentPrivate, PrintfArgument, PrimitivePrintfArgument};
use crate::{LargerOf, NullString, is_compat};

use core::ffi::c_void;
use libc::{c_char, c_int, c_uint, c_double};

macro_rules! impl_empty_trait {
    ($trait_name:ident ; $($implementor:ty),*) => {
        $(
            impl $trait_name for $implementor { }
        )*
    };
}

impl_empty_trait!(PrintfArgumentPrivate;
    u8, u16, u32, u64, usize, i8, i16, i32, i64, isize, f32, f64,
    &str, NullString
);


macro_rules! impl_printf_arg_integer {
    ( $( $t:ty, $signed:expr, $int_type:ty );* ) => {
        $(
            impl PrintfArgument for $t {
                const IS_SIGNED: bool = $signed;

                const IS_CHAR: bool      = is_compat::<$t, libc::c_char>();
                const IS_SHORT: bool     = is_compat::<$t, libc::c_short>();
                const IS_INT: bool       = is_compat::<$t, libc::c_int>();
                const IS_LONG: bool      = is_compat::<$t, libc::c_long>();
                const IS_LONG_LONG: bool = is_compat::<$t, libc::c_longlong>();

                const IS_SIZE: bool      = is_compat::<$t, libc::size_t>();
                const IS_MAX: bool       = is_compat::<$t, libc::intmax_t>();
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
    fn as_c_val(self) -> c_double { self as c_double }
}

impl PrintfArgument for f64 {
    const IS_FLOAT: bool = true;

    type CPrintfType = c_double;

    #[inline]
    fn as_c_val(self) -> c_double { self as c_double }
}

impl PrintfArgument for NullString {
    type CPrintfType = *const c_char;

    const IS_C_STRING: bool = true;

    #[inline]
    fn as_c_val(self) -> *const c_char { self.as_ptr() }
}

impl_empty_trait!(PrimitivePrintfArgument;
    u8, u16, u32, u64, usize, i8, i16, i32, i64, isize, f32, f64,
    NullString
);

#[cfg(feature = "std")]
impl PrintfArgumentPrivate for &std::ffi::CStr { }

#[cfg(feature = "std")]
impl PrintfArgument for &std::ffi::CStr {
    type CPrintfType = *const c_char;

    const IS_C_STRING: bool = true;

    #[inline]
    fn as_c_val(self) -> *const c_char { self.as_ptr() }
}

#[cfg(feature = "std")]
impl PrimitivePrintfArgument for &std::ffi::CStr { }

#[cfg(feature = "std")]
impl PrintfArgumentPrivate for &std::ffi::CString { }

#[cfg(feature = "std")]
impl PrintfArgument for &std::ffi::CString {
    type CPrintfType = *const c_char;

    const IS_C_STRING: bool = true;

    #[inline]
    fn as_c_val(self) -> *const c_char { self.as_ptr() }
}

#[cfg(feature = "std")]
impl PrimitivePrintfArgument for &std::ffi::CString { }

impl<T: Sized> PrintfArgumentPrivate for *const T { }

impl<T: Sized> PrintfArgument for *const T {
    type CPrintfType = *const c_void;

    const IS_POINTER: bool = true;

    #[inline]
    fn as_c_val(self) -> *const c_void { self as *const c_void }
}

impl<T: Sized> PrimitivePrintfArgument for *const T { }

impl<T: Sized> PrintfArgumentPrivate for *mut T { }

impl<T: Sized> PrintfArgument for *mut T {
    type CPrintfType = *const c_void;

    const IS_POINTER: bool = true;

    #[inline]
    fn as_c_val(self) -> *const c_void { self as *mut c_void as *const c_void }
}

impl<T: Sized> PrimitivePrintfArgument for *mut T { }

/// Representation of the arguments corresponding to a printf(3) `%.*s`
/// conversion.
#[repr(C)]
pub struct StrSlice {
    sz: usize,
    ptr: *const u8,
}

// Because &str's CPrintfType already takes up two 8-byte words on x86_64,
// we can't allow this to be used with a(n additional) star argument in
// a tuple (otherwise the `CPrintType` structure will not always be laid
// out as a function argument in the same manner as the corresponding
// disaggregated values (treated as multiple arguments)),
// so &str isn't also `PrimitivePrintArgument`.
impl PrintfArgument for &str {
    const NUM_STARS_USED: usize = 1;
    const NEEDS_STAR_PRECISION: bool = true;

    type CPrintfType = StrSlice;

    const IS_C_STRING: bool = true;

    #[inline]
    fn as_c_val(self) -> StrSlice {
        StrSlice {
            sz: self.len(),
            ptr: self.as_ptr(),
        }
    }
}

// IntArg is a hack needed to make sure the layout of StarredArgument,
// when used as a function argument, is the same as the layout of
// StarredArgument's star_arg and arg fields if they were used
// as two sequential function arguments.

#[cfg(not(target_arch = "x86_64"))]
#[repr(C)]
struct IntArg {
  n: c_int,
}

#[cfg(target_arch = "x86_64")]
#[repr(C)]
union IntArg {
    n: c_int,
    _ll: u64,
}

/// A structure for two C-side arguments to a printf(3)-style function;
/// used as [`CPrintfType`](PrintfArgument::CPrintfType)s by pairs.
///
/// It must be two machine words in size or less in order for the
/// structure representation (in registers and/or memory)
/// as a function argument to _always_ be the same
/// as passing `star_arg` and `arg` as two separate-but-adjacent
/// function arguments on x86-64.
#[repr(C)]
pub struct StarredArgument<T> {
    star_arg: IntArg,
    arg: T,
}

impl<T: PrimitivePrintfArgument> PrintfArgumentPrivate for (c_int, T) { }

impl<T: PrimitivePrintfArgument> PrintfArgument for (c_int, T) {
    const NUM_STARS_USED: usize = T::NUM_STARS_USED + 1;
    const NEEDS_STAR_PRECISION: bool = T::NEEDS_STAR_PRECISION;

    type CPrintfType = StarredArgument<T::CPrintfType>;

    #[inline]
    fn as_c_val(self) -> StarredArgument<T::CPrintfType> {
        StarredArgument {
            star_arg: IntArg { n: self.0 },
            arg: self.1.as_c_val(),
        }
    }
}
