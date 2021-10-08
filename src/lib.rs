// Copyright (c) 2021 The Pennsylvania State University. All rights reserved.

//! Types and whatnot for safe use of printf(3)-style format strings.

// https://pubs.opengroup.org/onlinepubs/9699919799/functions/printf.html
// https://man7.org/linux/man-pages/man3/printf.3.html
// https://www.freebsd.org/cgi/man.cgi?printf%283%29

#![no_std]

#![feature(const_fn_trait_bound)]

// We engage in a little naughtiness where we rely on two arguments to
// functions and the two elements of the following structs (when used as
// a single argument to a function) being laid out in same way always:
//
// StrSlice
// StarredArgument
//
// This is not guaranteed to be true in general, but is known to be true
// for the following architectures and ABIs (using OSes as a proxy for ABI):
#[cfg(all(
    any(target_arch = "x86", target_arch = "x86_64", target_arch = "arm"),
    any(target_os = "linux", target_os = "android", target_os = "freebsd",
        target_os = "dragonfly", target_os = "openbsd", target_os = "netbsd")
))]

// We only aim for compatibility with printf(3) as specified in POSIX:
#[cfg(unix)]

/// Marker structure used to ensure this crate only sucessfully compiles for
/// known-compatible (architecture, ABI) pairs.
#[derive(Clone,Copy)]
struct CompatibleSystem { }

// We use `libc` for types.
extern crate libc;

// We optionally provide support for a couple of relevant types in `std`.
#[cfg(feature = "std")]
extern crate std;

use core::marker::PhantomData;
use libc::c_char;

use crate::validate::is_fmt_valid_for_args;
use crate::private::PrintfArgumentPrivate;

pub use crate::printf_arg_impls::{StrSlice, StarredArgument};

/// Traits used to implement private details of [sealed traits].
///
/// [sealed traits]: https://rust-lang.github.io/api-guidelines/future-proofing.html
mod private {
    /// Marker trait for [`PrintfArgument`](`super::PrintfArgument`).
    pub trait PrintfArgumentPrivate {
    }
}

mod larger_of;
mod printf_arg_impls;
mod validate;

/// A wrapper for a `'static` null-terminated string.
///
/// Sometimes used in favor of `std`'s `CStr` or `CString` types,
/// as these can be made as compile-time constants.
#[derive(Clone, Copy)]
pub struct NullString {
    s: *const c_char
}

impl NullString {
    /// Creates a [`NullString`] from a `s`, a static [`&str`](str),
    /// or panics if `s` is not null-terminated.
    #[allow(unconditional_panic)]
    #[deny(const_err)]
    pub const fn new(s: &'static str) -> NullString {
        const PANIC: [c_char; 0] = [];
        const NOT_NULL_TERMINATED: usize = 42;

        let bytes = s.as_bytes();
        if bytes.len() == 0 || bytes[bytes.len() - 1] != b'\0' {
            // out-of-bounds reference as a workaround for not being able
            // to panic!() in a const fn
            let x: &c_char = &PANIC[NOT_NULL_TERMINATED];
            return NullString { s: x as *const c_char };
        }

        NullString { s: bytes.as_ptr() as *const c_char }
    }

    /// Returns a pointer to the beginning of the wrapped string.
    #[inline]
    pub const fn as_ptr(self) -> *const c_char {
        self.s
    }
}

/// Convenience macro for creating a [`NullString`]; it appends a null
/// character for you!
#[macro_export]
macro_rules! null_str {
    ($str:expr) => {
        {
            const STR: NullString = $crate::NullString::new(concat!($str, "\0"));
            STR
        }
    };
}

/// A Rust-side argument to a safe wrapper around a printf(3)-like function.
///
/// This is a [sealed trait]; consumers of this crate are not allowed
/// to create their own `impl`s in order to unconditionally preserve
/// safety.
///
/// [sealed trait]: https://rust-lang.github.io/api-guidelines/future-proofing.html
pub trait PrintfArgument: PrintfArgumentPrivate + Copy {
    /// The type corresponding to `Self` we should _really_ send as
    /// an argument to a printf(3)-like function.
    type CPrintfType;

    /// Converts `self` to a value suitable for sending to printf(3).
    fn as_c_val(self) -> Self::CPrintfType;

    /// The number of stars (`*` characters)
    /// in the corresponding printf(3) conversion
    /// specification to match what is put on the stack by
    /// [`CPrintfType`](Self::CPrintfType).
    const NUM_STARS_USED: usize = 0;

    /// Whether the precision of the printf(3) conversion specification
    /// corresponding to `self` must be star (`*`).
    const NEEDS_STAR_PRECISION: bool = false;

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

/// Marker trait for implementors of [`PrintfArgument`] that are not
/// tuples (which are used with conversion specifications involving stars)
/// _and_ whose [`CPrintfType`](PrintfArgument::CPrintfType) is not
/// compound.
pub trait PrimitivePrintfArgument: PrintfArgument { }

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
    use core::mem::{size_of, align_of};

    size_of::<T>() == size_of::<U>() && align_of::<T>() == align_of::<U>()
}

/// Utility trait for determining which of two integer types is larger.
pub trait LargerOfOp<Rhs> {
    /// If `Rhs` is a larger type than `Self`, this should be `Rhs`; otherwise
    /// it should be `Self`.
    type Output;
}

/// Type alias that better conveys [`LargerOfOp`]'s nature as a type-level
/// function.
pub type LargerOf<T, U> = <T as LargerOfOp<U>>::Output;

/// A list of Rust-side arguments to a printf(3)-style function.
pub trait PrintfArgs {
    /// The [`PrintfArgsList`] equivalent to `Self`.
    type AsList: PrintfArgsList;
}

/// A [`PrintfArgs`] in a form more amenable to recursive processing.
pub trait PrintfArgsList {
    const IS_EMPTY: bool;

    type First: PrintfArgument;
    type Rest: PrintfArgsList;
}

impl PrintfArgsList for () {
    const IS_EMPTY: bool = true;

    type First = u8; // not really, but to fulfil the type constraint, we need *something* here.
    type Rest = ();
}

impl<CAR: PrintfArgument, CDR: PrintfArgsList> PrintfArgsList for (CAR, CDR) {
    const IS_EMPTY: bool = false;

    type First = CAR;
    type Rest = CDR;
}

impl<T: PrimitivePrintfArgument> PrintfArgs for T {
    type AsList = (T, ());
}

impl PrintfArgs for &str {
    type AsList = (Self, ());
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

make_printf_arguments_tuple!( T );
make_printf_arguments_tuple!( T, U );
make_printf_arguments_tuple!( T, U, V );
make_printf_arguments_tuple!( T, U, V, W );
make_printf_arguments_tuple!( T, U, V, W, X );
make_printf_arguments_tuple!( T, U, V, W, X, Y );
make_printf_arguments_tuple!( T, U, V, W, X, Y, Z );
make_printf_arguments_tuple!( T, U, V, W, X, Y, Z, A );

/// A type-safe wrapper around a C-style string verified to be compatible
/// with use as a format string for printf(3)-style functions called with
/// `T` as the varargs.
#[derive(Clone, Copy)]
pub struct PrintfFmt<T: PrintfArgs> {
    fmt: *const c_char,
    _x: CompatibleSystem,
    _y: PhantomData<T>,
}

/// Utility conversion from [`u8`] to [`libc::c_char`].
const fn c(x: u8) -> c_char { x as c_char }

/// The empty C string.
const EMPTY_C_STRING: *const c_char = &c(b'\0') as *const c_char;

impl<T: PrintfArgs> PrintfFmt<T> {
    /// If `fmt` represents a valid, supported format string for printf(3)
    /// when given Rust-side arguments `T`, returns a [`PrintfFmt`];
    /// panics otherwise.
    #[allow(unconditional_panic)]
    pub const fn new(fmt: &'static str) -> Self {
        const PANIC: [c_char; 0] = [];
        const U8_IS_NOT_CHAR_SIZED: usize = 42;

        if !is_compat::<u8, c_char>() {
            // We do out-of-bounds indexing, as we can't currently use
            // panic! in const fns.
            let p = &PANIC[U8_IS_NOT_CHAR_SIZED] as *const c_char;

            return PrintfFmt {
                fmt: p,
                _x: CompatibleSystem { },
                _y: PhantomData,
            };
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

        PrintfFmt {
            fmt: s,
            _x: CompatibleSystem { },
            _y: PhantomData,
        }
    }

    /// Returns a pointer to the beginning of the format string.
    pub fn as_ptr(self) -> *const c_char {
        self.fmt
    }
}

/// Returns whether `fmt` is (1) a valid C-style string and (2) a format
/// string compatible with the tuple of arguments `T` when used in a
/// printf(3)-like function.
#[deny(unconditional_panic)]
pub const fn is_fmt_valid<T: PrintfArgs>(fmt: &[c_char]) -> bool {
    is_fmt_valid_for_args::<T>(fmt, false)
}

/// An example of how to use the types and traits of this crate to safely
/// wrap functions with printf(3)-style format strings and varargs.
pub mod example {
    use libc::{c_char, c_int};
    use crate::{PrintfFmt, PrintfArgument};

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
}
