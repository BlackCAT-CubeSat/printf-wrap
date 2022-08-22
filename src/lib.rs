// Copyright (c) 2021-2022 The Pennsylvania State University and the project contributors.
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Types and functions for the safe use of `printf(3)`-style format strings.
//!
//! `printf(3)` ([POSIX], [Linux], and [FreeBSD] man pages) and its variants
//! present some challenges for memory-safe use from Rust:
//! the passed-in arguments
//! are interpreted as different types based on the content of the format
//! string, with each conversion specification (e.g., `%s`) consuming up to
//! three arguments (e.g, `%*.*d`), and the `%n` specification even writing
//! to memory!
//! For memory- and type-safe use, we must make sure a given format string
//! is only used in invocations with the correct argument number and type.
//!
//! This crate contains mechanisms you can use to ensure such agreement.
//! [`PrintfFmt`]`<(A, B, ...)>` wraps a format string, doing verification to ensure
//! it can be safely used with the list of arguments corresponding to
//! the tuple of types
//! `(A: `[`PrintfArgument`]`, B: `[`PrintfArgument`]`, ...)`.
//! This verification may be performed at
//! compile time, allowing for safe wrappers with zero runtime overhead.
//!
//! A brief example of how this crate might be used:
//!
//! ```no_run
//! use printf_wrap::{PrintfFmt, PrintfArgument};
//! use libc::{c_int, printf};
//!
//! /// Safe wrapper for calling printf with two value arguments.
//! pub fn printf_with_2_args<T, U>(fmt: PrintfFmt<(T, U)>, arg1: T, arg2: U) -> c_int
//! where
//!     T: PrintfArgument,
//!     U: PrintfArgument,
//! {
//!     unsafe { printf(fmt.as_ptr(), arg1.as_c_val(), arg2.as_c_val()) }
//! }
//!
//! fn main() {
//!     const MY_FMT: PrintfFmt<(u32, i32)> =
//!         PrintfFmt::new_or_panic("unsigned = %u, signed = %d\0");
//!     printf_with_2_args(MY_FMT, 42, -7);
//! }
//! ```
//!
//! The
#![cfg_attr(any(feature = "example", all(doc, feature = "doccfg")), doc = " [`example`]")]
#![cfg_attr(not(any(feature = "example", all(doc, feature = "doccfg"))), doc = " `example`")]
//! module has a more worked-out example of this crate's use, using
//! `printf(3)` and `snprintf(3)` as the functions to wrap.
//!
//! Only a subset of all possible `printf` format strings are accepted:
//!
//! * Numbered argument conversion specifications (e.g., `%2$d`) are not
//!   supported.
//! * `%lc`, `%ls`, `%C`, `%S`, and `%L[fFeEgGaA]` are not supported.
//! * `%n` is not supported.
//!
//! [POSIX]: https://pubs.opengroup.org/onlinepubs/9699919799/functions/printf.html
//! [Linux]: https://man7.org/linux/man-pages/man3/printf.3.html
//! [FreeBSD]: https://www.freebsd.org/cgi/man.cgi?printf%283%29

#![no_std]
#![cfg_attr(feature = "doccfg", feature(doc_cfg))]

// We only aim for compatibility with printf(3) as specified in POSIX:
#[cfg(unix)]
/// Marker structure used to ensure this crate only sucessfully compiles for
/// known-compatible systems.
#[derive(Clone, Copy, Debug)]
struct CompatibleSystem {}

// We use `libc` for types.
extern crate libc;

// We optionally provide support for a couple of relevant types in `std`.
#[cfg(any(feature = "std", doc))]
extern crate std;

use core::marker::PhantomData;
use libc::c_char;

use crate::private::PrintfArgumentPrivate;
use crate::validate::is_fmt_valid_for_args;

/// Traits used to implement private details of [sealed traits].
///
/// [sealed traits]: https://rust-lang.github.io/api-guidelines/future-proofing.html#c-sealed
pub(crate) mod private {
    /// Marker trait for [`PrintfArgument`](`super::PrintfArgument`).
    pub trait PrintfArgumentPrivate {}
}

mod larger_of;
mod printf_arg_impls;
mod validate;

/// A wrapper for a `'static` null-terminated string.
///
/// Sometimes used in favor of [`std`]'s
/// [`CStr`](std::ffi::CStr) or [`CString`](std::ffi::CString) types,
/// as [`NullString`]s can be made as compile-time constants.
#[derive(Clone, Copy, Debug)]
pub struct NullString {
    s: *const c_char,
}

impl NullString {
    /// Creates a [`NullString`] from `s`
    /// or panics if `s` is not null-terminated.
    ///
    /// # Panics
    ///
    /// Panics if the string `s` does not end in the null character.
    #[allow(unconditional_panic)]
    #[deny(const_err)]
    pub const fn new(s: &'static str) -> NullString {
        let bytes = s.as_bytes();
        if bytes.len() == 0 || bytes[bytes.len() - 1] != b'\0' {
            panic!("string passed to NullString::new is not null-terminated!");
        }

        NullString { s: bytes.as_ptr() as *const c_char }
    }

    /// Returns a pointer to the beginning of the wrapped string.
    #[inline]
    pub const fn as_ptr(self) -> *const c_char {
        self.s
    }

    /// Returns a `&`[`CStr`](std::ffi::CStr) pointing to the wrapped string.
    #[cfg(any(feature = "std", all(doc, feature = "doccfg")))]
    #[cfg_attr(feature = "doccfg", doc(cfg(feature = "std")))]
    #[inline]
    pub fn as_cstr(self) -> &'static std::ffi::CStr {
        unsafe { std::ffi::CStr::from_ptr(self.s) }
    }
}

#[cfg(any(feature = "std", all(doc, feature = "doccfg")))]
#[cfg_attr(feature = "doccfg", doc(cfg(feature = "std")))]
impl From<&'static std::ffi::CStr> for NullString {
    #[inline]
    fn from(cstr: &'static std::ffi::CStr) -> Self {
        NullString { s: cstr.as_ptr() }
    }
}

#[cfg(any(feature = "std", all(doc, feature = "doccfg")))]
#[cfg_attr(feature = "doccfg", doc(cfg(feature = "std")))]
impl From<NullString> for &'static std::ffi::CStr {
    #[inline]
    fn from(nstr: NullString) -> Self {
        nstr.as_cstr()
    }
}

/// Convenience macro for creating a `const` [`NullString`],
/// including appending a null character.
#[macro_export]
macro_rules! null_str {
    ($str:expr) => {{
        const STR: $crate::NullString = $crate::NullString::new(concat!($str, "\0"));
        STR
    }};
}

/// A Rust-side argument to a safe wrapper around a `printf(3)`-like function.
///
/// This is a [sealed trait]; consumers of this crate are not allowed
/// to create their own `impl`s in order to unconditionally preserve
/// safety.
///
/// [sealed trait]: https://rust-lang.github.io/api-guidelines/future-proofing.html#c-sealed
pub trait PrintfArgument: PrintfArgumentPrivate + Copy {
    /// The C type corresponding to `Self` that we should _really_ send
    /// as an argument to a `printf(3)`-like function.
    type CPrintfType;

    /// Converts `self` to a value suitable for sending to `printf(3)`.
    fn as_c_val(self) -> Self::CPrintfType;

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

    /// Whether the type is a null-terminated string.
    const IS_C_STRING: bool = false;

    /// Whether the type is a pointer.
    const IS_POINTER: bool = false;
}

/// Are types `T` and `U` ABI-compatible, in the sense that using
/// one in the place of the other wouldn't affect structure layout,
/// stack layout if used as arguments (assuming they're both integer-like),
/// etc.?
///
/// Note that this doesn't check for whether substituting `T` with `U` (or vice
/// versa) is sensible or even valid;
/// the use-case is for types where any bit-pattern is
/// sensible and the types don't have non-trivial drop behavior.
const fn is_compat<T: Sized, U: Sized>() -> bool {
    use core::mem::{align_of, size_of};

    size_of::<T>() == size_of::<U>() && align_of::<T>() == align_of::<U>()
}

/// Utility trait for determining which of two integer types is larger.
///
/// The type alias [`LargerOf`] is usually more convenient to use outside
/// of implementations of this trait.
pub trait LargerOfOp<Rhs> {
    /// If `Rhs` is a larger type than `Self`, this should be `Rhs`; otherwise
    /// it should be `Self`.
    type Output;
}

/// Type alias that better conveys [`LargerOfOp`]'s nature as a type-level
/// function.
pub type LargerOf<T, U> = <T as LargerOfOp<U>>::Output;

/// A list of Rust-side arguments to a `printf(3)`-style function.
pub trait PrintfArgs {
    /// The [`PrintfArgsList`] equivalent to `Self`.
    type AsList: PrintfArgsList;
}

/// A [`PrintfArgs`] in a form more amenable to recursive processing.
pub trait PrintfArgsList {
    /// Whether this type represents an empty list.
    const IS_EMPTY: bool;

    /// The first element of the list.
    type First: PrintfArgument;
    /// The elements of the list after the first.
    type Rest: PrintfArgsList;
}

impl PrintfArgsList for () {
    const IS_EMPTY: bool = true;

    /// This isn't _really_ the first element of an empty list,
    /// but to fulfil the type constraint, we need _something_ here.
    type First = u8;
    type Rest = ();
}

impl<CAR: PrintfArgument, CDR: PrintfArgsList> PrintfArgsList for (CAR, CDR) {
    const IS_EMPTY: bool = false;

    type First = CAR;
    type Rest = CDR;
}

impl<T: PrintfArgument> PrintfArgs for T {
    type AsList = (T, ());
}

impl PrintfArgs for () {
    type AsList = ();
}

macro_rules! nested_list_from_flat {
    ($t:ident $(, $u:ident )*) => { ($t, nested_list_from_flat!($( $u ),*)) };
    () => { () };
}

macro_rules! make_printf_arguments_tuple {
    ($( $t:ident ),+) => {
        impl<$( $t ),+> PrintfArgs for ($( $t, )+)
            where $( $t: PrintfArgument ),+ {
            type AsList = nested_list_from_flat!($( $t ),+);
        }
    };
}

make_printf_arguments_tuple!(A);
make_printf_arguments_tuple!(A, B);
make_printf_arguments_tuple!(A, B, C);
make_printf_arguments_tuple!(A, B, C, D);
make_printf_arguments_tuple!(A, B, C, D, E);
make_printf_arguments_tuple!(A, B, C, D, E, F);
make_printf_arguments_tuple!(A, B, C, D, E, F, G);
make_printf_arguments_tuple!(A, B, C, D, E, F, G, H);
make_printf_arguments_tuple!(A, B, C, D, E, F, G, H, I);
make_printf_arguments_tuple!(A, B, C, D, E, F, G, H, I, J);
make_printf_arguments_tuple!(A, B, C, D, E, F, G, H, I, J, K);
make_printf_arguments_tuple!(A, B, C, D, E, F, G, H, I, J, K, L);
make_printf_arguments_tuple!(A, B, C, D, E, F, G, H, I, J, K, L, M);
make_printf_arguments_tuple!(A, B, C, D, E, F, G, H, I, J, K, L, M, N);
make_printf_arguments_tuple!(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O);
make_printf_arguments_tuple!(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P);

/// A type-safe wrapper around a C-style string verified to be compatible
/// with use as a format string for `printf(3)`-style functions called with
/// `T` as the varargs.
#[derive(Debug)]
pub struct PrintfFmt<T: PrintfArgs> {
    fmt: *const c_char,
    _x: CompatibleSystem,
    _y: PhantomData<T>,
}

/// Utility conversion from [`u8`] to [`libc::c_char`].
const fn c(x: u8) -> c_char {
    x as c_char
}

/// The empty C string.
const EMPTY_C_STRING: *const c_char = &c(b'\0') as *const c_char;

impl<T: PrintfArgs> PrintfFmt<T> {
    /// If `fmt` represents a valid, supported format string for `printf(3)`
    /// when given Rust-side arguments `T`, returns a [`PrintfFmt`];
    /// panics otherwise.
    ///
    /// # Panics
    ///
    /// See above.
    #[allow(unconditional_panic)]
    #[inline]
    pub const fn new_or_panic(fmt: &'static str) -> Self {
        if !is_compat::<u8, c_char>() {
            panic!("u8 and c_char have different sizes/alignments, somehow");
        }

        let fmt_as_cstr: &'static [c_char] = unsafe {
            // Following is safe, as (1) we've verified u8 has the same
            // size and alignment as c_char and (2) references to T have the
            // same layout as pointers to T
            core::mem::transmute(fmt.as_bytes() as *const [u8] as *const [c_char])
        };

        let s = if is_fmt_valid_for_args::<T>(fmt_as_cstr, true) {
            fmt_as_cstr.as_ptr()
        } else {
            EMPTY_C_STRING
        };

        PrintfFmt { fmt: s, _x: CompatibleSystem {}, _y: PhantomData }
    }

    /// If `fmt` represents a valid, supported format string for `printf(3)`
    /// when given Rust-side arguments `T`, returns it as a [`PrintfFmt`].
    ///
    /// # Errors
    ///
    /// Returns `Err(())` if `fmt` is _not_ a valid, supported format string
    /// corresponding to varargs `T`.
    #[inline]
    pub const fn new(fmt: &'static str) -> Result<Self, ()> {
        if !is_compat::<u8, c_char>() {
            return Err(());
        }

        let fmt_as_cstr: &'static [c_char] = unsafe {
            // Following is safe, as (1) we've verified u8 has the same
            // size and alignment as c_char and (2) references to T have the
            // same layout as pointers to T
            core::mem::transmute(fmt.as_bytes() as *const [u8] as *const [c_char])
        };

        if is_fmt_valid_for_args::<T>(fmt_as_cstr, false) {
            Ok(PrintfFmt { fmt: fmt_as_cstr.as_ptr(), _x: CompatibleSystem {}, _y: PhantomData })
        } else {
            Err(())
        }
    }

    /// Returns a pointer to the beginning of the format string.
    #[inline]
    pub const fn as_ptr(self) -> *const c_char {
        self.fmt
    }
}

impl<T: PrintfArgs> Clone for PrintfFmt<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T: PrintfArgs> Copy for PrintfFmt<T> {}

/// Returns whether `fmt` is (1) a valid C-style string and (2) a format
/// string compatible with the tuple of arguments `T` when used in a
/// `printf(3)`-like function.
#[deny(unconditional_panic)]
#[inline]
pub const fn is_fmt_valid<T: PrintfArgs>(fmt: &[c_char]) -> bool {
    is_fmt_valid_for_args::<T>(fmt, false)
}

#[cfg(any(feature = "example", all(doc, feature = "doccfg")))]
#[cfg_attr(feature = "doccfg", doc(cfg(feature = "example")))]
pub mod example;

#[cfg(test)]
mod tests;
