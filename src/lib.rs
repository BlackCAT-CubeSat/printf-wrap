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
// This is not guaranteed to be true in general, but is true for the
// following architectures and ABIs (using OSes as a proxy for ABI):
#[cfg(all(
    any(target_arch = "x86", target_arch = "x86_64", target_arch = "arm"),
    any(target_os = "linux", target_os = "android", target_os = "freebsd",
        target_os = "dragonfly", target_os = "openbsd", target_os = "netbsd")
))]

// We only aim for compatibility with printf(3) as specified in POSIX:
#[cfg(unix)]

/// Marker structure used to ensure this crate only compiles on
/// known-compatible (architecture, ABI) pairs.
struct CompatibleSystem { }

// We use `libc` for types.
extern crate libc;

use core::ffi::c_void;
use libc::{c_char, c_int, c_uint, c_double};

use crate::private::PrintfArgumentPrivate;


/// Traits used to implement private details of [sealed traits].
///
/// [sealed traits]: https://rust-lang.github.io/api-guidelines/future-proofing.html
mod private {
    ///
    pub trait PrintfArgumentPrivate {
    }
}

macro_rules! impl_empty_trait {
    ($trait_name:ident ; $($implementor:ty),*) => {
        $(
            impl $trait_name for $implementor { }
        )*
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

    const NUM_STARS_USED: usize = 0;
    const NEEDS_STAR_PRECISION: bool = false;
}

/// Marker trait for implementors of [`PrintfArgument`] that are not
/// tuples (which are used with conversion specifications involving stars).
pub trait PrimitivePrintfArgument: PrintfArgument { }

impl_empty_trait!(PrintfArgumentPrivate; u8, u16);
impl_empty_trait!(PrimitivePrintfArgument; u8, u16);

impl PrintfArgument for u8 {
    type CPrintfType = c_uint;

    #[inline]
    fn as_c_val(self) -> c_uint { self as c_uint }
}

impl PrintfArgument for u16 {
    type CPrintfType = c_uint;

    #[inline]
    fn as_c_val(self) -> c_uint { self as c_uint }
}

#[repr(C)]
pub struct StrSlice {
    sz: usize,
    ptr: *const u8,
}

// Because &str's CPrintfType already takes up two 8-byte words on x86_64,
// we can't allow this to be used with a(n additional) star argument in
// a tuple (otherwise the structure will not always be laid out as a
// function argument in the same manner as the corresponding disaggregated
// values (treated as multiple arguments),
// so this isn't also `PrimitivePrintArgument`.
impl PrintfArgumentPrivate for &str { }

impl PrintfArgument for &str {
    const NUM_STARS_USED: usize = 1;
    const NEEDS_STAR_PRECISION: bool = true;

    type CPrintfType = StrSlice;

    #[inline]
    fn as_c_val(self) -> StrSlice {
        StrSlice {
            sz: self.len(),
            ptr: self.as_ptr(),
        }
    }
}

#[cfg(not(target_arch = "x86_64"))]
#[repr(C)]
pub struct IntArg {
  n: c_int,
}

#[cfg(target_arch = "x86_64")]
#[repr(C)]
pub union IntArg {
    n: c_int,
    _ll: u64,
}

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

pub trait PrintfArgs {
    type AsList: PrintfArgsList;
}

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


const fn c(x: u8) -> c_char { x as c_char }

// This array is used by functions below to panic at compile time:
// we can't use panic!() in `const fn`s,
// but out-of-bounds indices work as a surrogate.
const PANIC: [u8; 0] = [];

// "Indices" to use with PANIC
const NOT_NULL_TERMINATED: usize = 42;

macro_rules! compile_time_panic {
    ($cond:tt, $reason:tt) => {
        if $cond {
            return PANIC[$reason] != 0;
        }
    };
}

#[allow(unconditional_panic)]
pub const fn does_fmt_match_args<T: PrintfArgs>(fmt: &[c_char], panic_on_false: bool) -> bool {
    let pf = panic_on_false;

    if !is_null_terminated(fmt) {
        compile_time_panic!(pf, NOT_NULL_TERMINATED);
        return false;
    }
    does_fmt_match_args_list::<T::AsList>(fmt, 0, panic_on_false)
}

#[allow(unconditional_panic)]
const fn does_fmt_match_args_list<T: PrintfArgsList>(fmt: &[c_char], start_idx: usize, panic_on_false: bool) -> bool {
   let pf = panic_on_false;

   false
}

/// Is `s` (a candidate for being a C string) null-terminated, and does
/// it have a null character _only_ at the very end?
const fn is_null_terminated(s: &[c_char]) -> bool {
    let mut i: usize = 0;

    while i < s.len() {
        if s[i] == c(b'\0') {
            return i == (s.len() - 1);
        }
        i += 1;
    }

    // If we get here, there's no null character at all:
    false
}


mod take1 {
use core::ffi::c_void;
use libc::c_char;

/// A wrapper for a null-terminated string.
///
/// Sometimes used in favor of `std`'s `CStr` or `CString` types,
/// as these can be made as compile-time constants.
#[derive(Clone, Copy)]
pub struct NulString {
    s: *const c_char
}

impl NulString {
    /// Creates a [`NulString`] from a `s`, a static `&str`,
    /// or panics if `s` is not null-terminated.
    #[allow(unconditional_panic)]
    #[deny(const_err)]
    pub const fn new(s: &'static str) -> NulString {
        const PANIC: [c_char; 0] = [];
        const NOT_NULL_TERMINATED: usize = 42;

        let bytes = s.as_bytes();
        if bytes.len() == 0 || bytes[bytes.len() - 1] != b'\0' {
            // out-of-bounds reference as a workaround for not being able
            // to panic!() in a const fn
            let x: &c_char = &PANIC[NOT_NULL_TERMINATED];
            return NulString { s: x as *const c_char };
        }

        NulString { s: bytes.as_ptr() as *const c_char }
    }

    #[inline]
    pub const fn as_ptr(self) -> *const c_char {
        self.s
    }
}

//#[macro_export]
//macro_rules! c_str {
//    ($str:expr) => {
//        {
//            const CSTR: NulString = $crate::NulString::new(concat!($str, "\0"));
//            CSTR
//        }
//    };
//}

/// An empty null-terminated string; used in some default implementations
/// of methods in [`PrintfArgument`].
const EMPTY_C_STRING: [c_char; 1] = [b'\0' as c_char];

pub trait LargerOfOp<Rhs> {
    type Output;
}

/// Information about how a type may be used with C's printf(3)
/// and similar functions.
pub trait PrintfArgument: Sized + Copy {
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

    /// Provides `self` as a [`libc::c_double`].
    /// Only expected to be meaningful if `Self::IS_FLOAT == true`.
    #[inline]
    fn as_double(self) -> libc::c_double {
        0.0 as libc::c_double
    }

    /// Whether the type is a null-terminated string.
    const IS_C_STRING: bool = false;

    /// Provides `self` as a [`*const c_char`] to a null-terminated (C-style)
    /// string.
    /// Only expected to be meaningful if `Self::IS_C_STRING == true`.
    #[inline]
    fn as_c_string(self) -> *const c_char {
        EMPTY_C_STRING.as_ptr()
    }

    /// Whether the type is a pointer.
    const IS_POINTER: bool = false;

    /// Provides `self` as a [`*const c_void`].
    /// Only expected to be meaningful if `Self::IS_POINTER == true`.
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
    ( $( $t:ty, $signed:expr );* ) => {
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

    #[inline]
    fn as_double(self) -> libc::c_double {
        self as libc::c_double
    }
}

impl PrintfArgument for f64 {
    const IS_FLOAT: bool = true;

    #[inline]
    fn as_double(self) -> libc::c_double {
        self as libc::c_double
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

impl PrintfArgument for NulString {
    const IS_C_STRING: bool = true;

    #[inline]
    fn as_c_string(self) -> *const c_char {
        self.as_ptr()
    }

    const IS_POINTER: bool = true;

    #[inline]
    fn as_pointer(self) -> *const c_void {
        self.as_ptr() as *const c_void
    }
}

pub trait PrintfArgs {
    type AsList: PrintfArgsList;
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

make_printf_arguments_tuple!( T );
make_printf_arguments_tuple!( T, U );
make_printf_arguments_tuple!( T, U, V );
make_printf_arguments_tuple!( T, U, V, W );
make_printf_arguments_tuple!( T, U, V, W, X );
make_printf_arguments_tuple!( T, U, V, W, X, Y );
make_printf_arguments_tuple!( T, U, V, W, X, Y, Z );
make_printf_arguments_tuple!( T, U, V, W, X, Y, Z, A );

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

mod private {
}

pub const fn does_fmt_match_args<T: PrintfArgs>(fmt: &[c_char]) -> bool {
    if !is_null_terminated(fmt) { return false; }
    does_fmt_match_args_list::<T::AsList>(fmt, 0)
}

const fn does_fmt_match_args_list<T: PrintfArgsList>(fmt: &[c_char], start_idx: usize) -> bool {
    use LengthModifier as LM;
    use ConvSpecifier as CS;

    match (next_conversion_specification(fmt, start_idx), T::IS_EMPTY) {
        (None, true) => true,
        (Some(conv_start), false) => {
            if let Ok((spec, after_conv)) = parse_conversion_specification(fmt, conv_start) {
                // See if we find grounds for rejection in the current
                // conversion specification...

                // (we currently don't support "*" in specifications)
                if spec.width_is_arg || spec.precision_is_arg { return false; }

                match spec.specifier {
                    CS::Integer => {
                        let is_compatible_type = match spec.length_modifier {
                            None               => T::First::IS_INT,
                            Some(LM::CharLen)  => T::First::IS_CHAR,
                            Some(LM::Short)    => T::First::IS_SHORT,
                            Some(LM::Long)     => T::First::IS_LONG,
                            Some(LM::LongLong) => T::First::IS_LONG_LONG,
                            Some(LM::Max)      => T::First::IS_MAX,
                            Some(LM::Size)     => T::First::IS_SIZE,
                            Some(LM::Ptrdiff)  => T::First::IS_PTRDIFF,
                            Some(LM::LongDouble) => false,
                        };

                        if !is_compatible_type { return false; }
                    },
                    CS::Double => {
                        if let Some(_) = spec.length_modifier { return false; }
                        if !T::First::IS_FLOAT { return false; }
                    },
                    CS::Char => {
                        if let Some(_) = spec.length_modifier { return false; }
                        if !T::First::IS_CHAR { return false; }
                    },
                    CS::String => {
                        if let Some(_) = spec.length_modifier { return false; }
                        if !T::First::IS_C_STRING { return false; }
                    },
                    CS::Pointer => {
                        if let Some(_) = spec.length_modifier { return false; }
                        if !T::First::IS_POINTER { return false; }
                    },
                };

                // ...and if not, recurse on the remainder of the format string
                // and argument list.
                does_fmt_match_args_list::<T::Rest>(fmt, after_conv)
            } else { false }
        },
        _ => false,
    }
}

/// The type content of a printf(3) conversion specification (excepting "`%%`"):
/// the parts that define the number and types of arguments that are consumed.
struct ConversionSpecification {
    /// Whether the field width is a function argument (`*`).
    width_is_arg: bool,
    /// Whether the precision is a function argument (`*`).
    precision_is_arg: bool,
    /// The length modifier, if present.
    length_modifier: Option<LengthModifier>,
    /// The conversion specifier.
    specifier: ConvSpecifier,
}

/// A length modifier in a printf(3) conversion specification.
enum LengthModifier {
    /// `hh`
    CharLen,
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

/// The conversion specifier in a conversion specification, or, rather,
/// an equivalence class with respect to acceptable argument types.
enum ConvSpecifier {
    /// `d`, `i`, `o`, `u`, `x`, or `X`
    Integer,
    /// `f`, `F`, `e`, `E`, `g`, `G`, `a`, or `A`
    Double,
    /// `c`
    Char,
    /// `s`
    String,
    /// `p`
    Pointer,
}

const fn c(x: u8) -> c_char { x as c_char }

/// If `fmt` has an acceptable printf(3) conversion specification starting
/// at index `start_idx`,
/// returns a pair consisting of a [`ConversionSpecification`] describing the
/// specification and a `usize` containing the index of the
/// first character after the specification; otherwise returns `Err`.
const fn parse_conversion_specification(fmt: &[c_char], start_idx: usize)
    -> Result<(ConversionSpecification, usize), ()> {
    use LengthModifier::*;
    use ConvSpecifier::*;

    let len = fmt.len();

    if len < 2 || start_idx > len - 2 { return Err(()); }

    if fmt[start_idx] != c(b'%') { return Err(()); }

    let mut i = start_idx + 1;

    // skip over flag characters ('-+#0 )
    while i < len {
        match fmt[i] as u8 {
            b'\'' | b'-' | b'+' | b'#' | b'0' | b' ' => (),
            _ => { break; }
        };
        i += 1;
    }

    // There must be more to the conversion specification at this point:
    if i >= len { return Err(()); }

    // See whether the field width (if any) is '*':
    let width_is_arg = match fmt[i] as u8 {
        b'*' => { i += 1; true },
        _ => {
            // Skip over any digits; if they exist, they're the field width.
            while i < len && (fmt[i] as u8).is_ascii_digit() { i += 1; }
            false
        }
    };

    // Must still be more:
    if i >= len { return Err(()); }

    // If the next character is '.', we have a precision:
    let precision_is_arg = if fmt[i] != c(b'.') {
        false
    } else {
        i += 1;
        if i >= len { return Err(()); }
        if fmt[i] == c(b'*') {
            i += 1;
            true
        } else {
            // Skip over any decimal digits -- they're part of the precision
            while i < len && (fmt[i] as u8).is_ascii_digit() { i += 1; }
            false
        }
    };

    // Must still be yet more:
    if i >= len { return Err(()); }

    // OK, look for a length modifier, if any:
    let length_modifier: Option<LengthModifier> = match fmt[i] as u8 {
        b'h' => {
            i += 1;
            if i < len && fmt[i] == c(b'h') {
                i += 1;
                Some(CharLen)
            } else {
                Some(Short)
            }
        },
        b'l' => {
            i += 1;
            if i < len && fmt[i] == c(b'l') {
                i += 1;
                Some(LongLong)
            } else {
                Some(Long)
            }
        },
        b'j' => { i += 1; Some(Max) },
        b'z' => { i += 1; Some(Size) },
        b't' => { i += 1; Some(Ptrdiff) },
        b'L' => { i += 1; Some(LongDouble) },
        _ => None,
    };

    // Must still be at least one more character:
    if i >= len { return Err(()); }

    // We've passed over any previous parts of the specification, so the
    // next character *must* be the conversion specifier:
    let spec: ConvSpecifier = match fmt[i] as u8 {
        b'd' | b'i' | b'o' | b'u' | b'x' | b'X' => { Integer },
        b'f' | b'F' | b'e' | b'E' | b'g' | b'G' | b'a' | b'A' => { Double },
        b'c' => { Char },
        b's' => { String },
        b'p' => { Pointer },
        _ => { return Err(()); },
    };

    let conv = ConversionSpecification {
        width_is_arg: width_is_arg,
        precision_is_arg: precision_is_arg,
        length_modifier: length_modifier,
        specifier: spec,
    };

    Ok((conv, i+1))
}

/// Starting at index `start_idx`, returns the index of the initial '`%`'
/// of the next non-`%%` conversion specification, if one is present;
/// else returns `None`.
const fn next_conversion_specification(fmt: &[c_char], start_idx: usize) -> Option<usize> {
    let len = fmt.len();
    let mut i: usize = start_idx;

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
    // conversion specification:
    None
}

/// Is `s` (a candidate for being a C string) null-terminated, and does
/// it have a null character _only_ at the very end?
const fn is_null_terminated(s: &[c_char]) -> bool {
    let mut i: usize = 0;

    while i < s.len() {
        if s[i] == c(b'\0') {
            return i == (s.len() - 1);
        }
        i += 1;
    }

    // If we get here, there's no null character at all:
    false
}


#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
}
