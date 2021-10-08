// Copyright (c) 2021 The Pennsylvania State University. All rights reserved.

//! Utilities for validation of the content of candidate format strings.

use libc::c_char;

use crate::{PrintfArgument, PrintfArgs, PrintfArgsList, c};

/// This array is used by functions below to panic at compile time:
/// we can't use panic!() in `const fn`s,
/// but out-of-bounds indices work as a surrogate.
const PANIC: [u8; 0] = [];

// "Indices" to use with PANIC
const NOT_NULL_TERMINATED: usize = 10042;
const WRONG_NUMBER_OF_STARS_IN_SPECIFICATION: usize = 10044;
const PRECISION_MUST_BE_STAR: usize = 10045;
const INTEGER_WIDTH_MISMATCH_IN_SPECIFICATION: usize = 10046;
const UNSUPPORTED_LENGTH_MODIFIER: usize = 10047;
const PRINTF_SPECIFIER_MISMATCH: usize = 10048;
const UNRECOGNIZED_CONVERSION_SPECIFICATION: usize = 10049;
const WRONG_NUMBER_OF_CONVERSIONS: usize = 10050;

/// If `$cond` is true, panic using `$reason` (used as an invalid array index).
///
/// This macro can be used at compile time, whereas [`panic!`] currently can't.
macro_rules! if_then_panic {
    ($cond:tt, $reason:tt) => {
        if $cond {
            return PANIC[$reason] != 0;
        }
    };
}

/// Returns whether `fmt` is (1) a valid C-style string and (2) a format
/// string compatible with the tuple of arguments `T` when used in a
/// printf(3)-like function.
///
/// If `panic_on_false` is true, panics instead of returning `false`.
#[allow(unconditional_panic)]
#[inline]
pub(crate) const fn is_fmt_valid_for_args<T: PrintfArgs>(fmt: &[c_char], panic_on_false: bool) -> bool {
    let pf = panic_on_false;

    if !is_null_terminated(fmt) {
        if_then_panic!(pf, NOT_NULL_TERMINATED);
        return false;
    }
    does_fmt_match_args_list::<T::AsList>(fmt, 0, panic_on_false)
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

/// Is `fmt`, treated as a printf(3) format string, compatible with the
/// arguments list `T`?
///
/// If it is not and `panic_on_false` is true, panics instead of returning
/// `false`.
#[allow(unconditional_panic)]
const fn does_fmt_match_args_list<T: PrintfArgsList>(fmt: &[c_char], start_idx: usize, panic_on_false: bool) -> bool {
    use LengthModifier as LM;
    use ConvSpecifier as CS;

    let pf = panic_on_false;

    match (next_conversion_specification(fmt, start_idx), T::IS_EMPTY) {
        (None, true) => true,
        (Some(conv_start), false) => {
            if let Ok((spec, after_conv)) = parse_conversion_specification(fmt, conv_start) {
                // See if we find grounds for rejection in the current
                // conversion specification...

                // Check starred width, precision:
                let num_stars = (spec.width_is_arg as usize) + (spec.precision_is_arg as usize);

                if num_stars != T::First::NUM_STARS_USED {
                    if_then_panic!(pf, WRONG_NUMBER_OF_STARS_IN_SPECIFICATION);
                    return false;
                }

                if T::First::NEEDS_STAR_PRECISION && !spec.precision_is_arg {
                    if_then_panic!(pf, PRECISION_MUST_BE_STAR);
                    return false;
                }

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

                        if !is_compatible_type {
                            if_then_panic!(pf, INTEGER_WIDTH_MISMATCH_IN_SPECIFICATION);
                            return false;
                        }
                    },
                    CS::Double => {
                        if let Some(_) = spec.length_modifier {
                            if_then_panic!(pf, UNSUPPORTED_LENGTH_MODIFIER);
                            return false;
                        }
                        if !T::First::IS_FLOAT {
                            if_then_panic!(pf, PRINTF_SPECIFIER_MISMATCH);
                            return false;
                        }
                    },
                    CS::Char => {
                        if let Some(_) = spec.length_modifier {
                            if_then_panic!(pf, UNSUPPORTED_LENGTH_MODIFIER);
                            return false;
                        }
                        if !T::First::IS_CHAR {
                            if_then_panic!(pf, PRINTF_SPECIFIER_MISMATCH);
                            return false;
                        }
                    },
                    CS::String => {
                        if let Some(_) = spec.length_modifier {
                            if_then_panic!(pf, UNSUPPORTED_LENGTH_MODIFIER);
                            return false;
                        }
                        if !T::First::IS_C_STRING {
                            if_then_panic!(pf, PRINTF_SPECIFIER_MISMATCH);
                            return false;
                        }
                    },
                    CS::Pointer => {
                        if let Some(_) = spec.length_modifier {
                            if_then_panic!(pf, UNSUPPORTED_LENGTH_MODIFIER);
                            return false;
                        }
                        if !T::First::IS_POINTER {
                            if_then_panic!(pf, PRINTF_SPECIFIER_MISMATCH);
                            return false;
                        }
                    },
                };

                // ...and if not, recurse on the remainder of the format string
                // and argument list.
                does_fmt_match_args_list::<T::Rest>(fmt, after_conv, panic_on_false)
            } else {
                if_then_panic!(pf, UNRECOGNIZED_CONVERSION_SPECIFICATION);
                false
            }
        },
        _ => {
            if_then_panic!(pf, WRONG_NUMBER_OF_CONVERSIONS);
            false
        },
    }
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
