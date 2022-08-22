// Copyright (c) 2021-2022 The Pennsylvania State University and the project contributors.
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Utilities for the validation of the content of candidate format strings.

use core::ffi::c_char;

use crate::{c, PrintfArgs, PrintfArgsList, PrintfArgument};

/// Returns whether `fmt` is (1) a valid C-style string and (2) a format
/// string compatible with the tuple of arguments `T` when used in a
/// `printf(3)`-like function.
///
/// # Panics
///
/// If `panic_on_false` is true, panics instead of returning `false`.
#[allow(unconditional_panic)]
#[inline]
pub(crate) const fn is_fmt_valid_for_args<T: PrintfArgs>(
    fmt: &[c_char],
    panic_on_false: bool,
) -> bool {
    if !is_null_terminated(fmt) {
        if panic_on_false {
            panic!("Candidate format string is not null-terminated!");
        }
        return false;
    }
    does_fmt_match_args_list::<T::AsList>(fmt, 0, panic_on_false)
}

/// The type content of a `printf(3)` conversion specification (excepting "`%%`"):
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

/// A length modifier in a `printf(3)` conversion specification.
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

/// Is `fmt`, treated as a `printf(3)` format string, compatible with the
/// arguments list `T`?
///
/// # Panics
///
/// If `fmt` is not so compatible and `panic_on_false` is true,
/// this function panics instead of returning `false`.
#[allow(unconditional_panic)]
const fn does_fmt_match_args_list<T: PrintfArgsList>(
    fmt: &[c_char],
    start_idx: usize,
    panic_on_false: bool,
) -> bool {
    match (next_conversion_specification(fmt, start_idx), T::IS_EMPTY) {
        (None, true) => true,
        (Some(conv_start), false) => {
            if let Ok((spec, after_conv)) = parse_conversion_specification(fmt, conv_start) {
                // Check conversion specification:
                does_convspec_match_arg::<T>(spec, fmt, after_conv, panic_on_false)
            } else {
                if panic_on_false {
                    panic!("Unrecognized conversion specification!");
                }
                false
            }
        }
        _ => {
            if panic_on_false {
                panic!("Wrong number of conversions!");
            }
            false
        }
    }
}

/// Recursive part of [`does_fmt_match_args_list`].
///
/// Specifically, this function
/// tests whether the first element of the [`PrintfArgsList`] `T` is an
/// acceptable first argument for the conversion specification `spec`,
/// then recurses over (1) the rest of `T` and (2) either the rest of
/// the conversion specification (for specifications with `*`) or the
/// rest of the format string `fmt` (starting at `next_idx`).
///
/// # Panics
///
/// Panics instead of returning `false` if `panic_on_false` is true.
#[allow(unconditional_panic)]
const fn does_convspec_match_arg<T: PrintfArgsList>(
    spec: ConversionSpecification,
    fmt: &[c_char],
    next_idx: usize,
    panic_on_false: bool,
) -> bool {
    use ConvSpecifier as CS;
    use LengthModifier as LM;

    // Make sure we haven't prematurely gotten to the end of the arguments
    // list...
    if T::IS_EMPTY {
        if panic_on_false {
            panic!("Wrong number of arguments for conversion!");
        }
        return false;
    }

    // Let's see if we find grounds for rejection in the current
    // conversion specification.

    // Check for starred width, precision:
    if spec.width_is_arg {
        if !T::First::IS_INT || !T::First::IS_SIGNED {
            if panic_on_false {
                panic!("Bad argument for starred width!");
            }
            return false;
        }

        // Recurse on the *rest* of the (conversion specification, args list):
        return does_convspec_match_arg::<T::Rest>(
            ConversionSpecification { width_is_arg: false, ..spec },
            fmt,
            next_idx,
            panic_on_false,
        );
    }
    if spec.precision_is_arg {
        if !T::First::IS_INT || !T::First::IS_SIGNED {
            if panic_on_false {
                panic!("Bad argument for starred precision!");
            }
            return false;
        }

        // Recurse on the *rest* of the (conversion specification, args list):
        return does_convspec_match_arg::<T::Rest>(
            ConversionSpecification { precision_is_arg: false, ..spec },
            fmt,
            next_idx,
            panic_on_false,
        );
    }

    // If we get here, we've gotten past any stars
    // in the conversion specification:

    match spec.specifier {
        CS::Integer => {
            let is_compatible_type = match spec.length_modifier {
                None => T::First::IS_INT,
                Some(LM::CharLen) => T::First::IS_CHAR,
                Some(LM::Short) => T::First::IS_SHORT,
                Some(LM::Long) => T::First::IS_LONG,
                Some(LM::LongLong) => T::First::IS_LONG_LONG,
                Some(LM::Max) => T::First::IS_MAX,
                Some(LM::Size) => T::First::IS_SIZE,
                Some(LM::Ptrdiff) => T::First::IS_PTRDIFF,
                Some(LM::LongDouble) => false,
            };

            if !is_compatible_type {
                if panic_on_false {
                    panic!("Integer width mismatch in specification!");
                }
                return false;
            }
        }
        s @ (CS::Double | CS::Char | CS::String | CS::Pointer) => {
            let is_compatible_type = match s {
                CS::Double => T::First::IS_FLOAT,
                CS::Char => T::First::IS_CHAR,
                CS::String => T::First::IS_C_STRING,
                CS::Pointer => T::First::IS_POINTER,
                _ => {
                    return false;
                }
            };
            if let Some(_) = spec.length_modifier {
                if panic_on_false {
                    panic!("Unsupported length modifier!");
                }
                return false;
            }
            if !is_compatible_type {
                if panic_on_false {
                    panic!("printf(3) specifier mismatch!");
                }
                return false;
            }
        }
    };

    // Nothing wrong in the current specification;
    // recurse on the remainder of the format string and argument list.
    does_fmt_match_args_list::<T::Rest>(fmt, next_idx, panic_on_false)
}

/// Starting at index `start_idx`, returns the index of the initial '`%`'
/// of the next non-`%%` conversion specification, if one is present;
/// else returns `None`.
const fn next_conversion_specification(fmt: &[c_char], start_idx: usize) -> Option<usize> {
    let len = fmt.len();
    let mut i: usize = start_idx;

    if len == 0 {
        return None;
    }

    while i < len {
        if fmt[i] == c(b'%') {
            // skip over '%%':
            if i < len - 1 && fmt[i + 1] == c(b'%') {
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

/// If `fmt` has an acceptable `printf(3)` conversion specification starting
/// at index `start_idx`,
/// returns a pair consisting of a [`ConversionSpecification`] describing the
/// specification and a `usize` containing the index of the
/// first character after the specification.
///
/// # Errors
///
/// Returns `Err(())` if `fmt` does not have an acceptable conversion specification
/// starting at `start_idx`.
const fn parse_conversion_specification(
    fmt: &[c_char],
    start_idx: usize,
) -> Result<(ConversionSpecification, usize), ()> {
    use ConvSpecifier::*;
    use LengthModifier::*;

    let len = fmt.len();

    if len < 2 || start_idx > len - 2 {
        return Err(());
    }

    if fmt[start_idx] != c(b'%') {
        return Err(());
    }

    let mut i = start_idx + 1;

    // skip over flag characters ('-+#0 )
    while i < len {
        match fmt[i] as u8 {
            b'\'' | b'-' | b'+' | b'#' | b'0' | b' ' => (),
            _ => {
                break;
            }
        };
        i += 1;
    }

    // There must be more to the conversion specification at this point:
    if i >= len {
        return Err(());
    }

    // See whether the field width (if any) is '*':
    let width_is_arg = match fmt[i] as u8 {
        b'*' => {
            i += 1;
            true
        }
        _ => {
            // Skip over any digits; if they exist, they're the field width.
            while i < len && (fmt[i] as u8).is_ascii_digit() {
                i += 1;
            }
            false
        }
    };

    // Must still be more:
    if i >= len {
        return Err(());
    }

    // If the next character is '.', we have a precision:
    let precision_is_arg = if fmt[i] != c(b'.') {
        false
    } else {
        i += 1;
        if i >= len {
            return Err(());
        }
        if fmt[i] == c(b'*') {
            i += 1;
            true
        } else {
            // Skip over any decimal digits -- they're part of the precision
            while i < len && (fmt[i] as u8).is_ascii_digit() {
                i += 1;
            }
            false
        }
    };

    // Must still be yet more:
    if i >= len {
        return Err(());
    }

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
        }
        b'l' => {
            i += 1;
            if i < len && fmt[i] == c(b'l') {
                i += 1;
                Some(LongLong)
            } else {
                Some(Long)
            }
        }
        b'j' => {
            i += 1;
            Some(Max)
        }
        b'z' => {
            i += 1;
            Some(Size)
        }
        b't' => {
            i += 1;
            Some(Ptrdiff)
        }
        b'L' => {
            i += 1;
            Some(LongDouble)
        }
        _ => None,
    };

    // Must still be at least one more character:
    if i >= len {
        return Err(());
    }

    // We've passed over any previous parts of the specification, so the
    // next character *must* be the conversion specifier:
    let spec: ConvSpecifier = match fmt[i] as u8 {
        b'd' | b'i' | b'o' | b'u' | b'x' | b'X' => Integer,
        b'f' | b'F' | b'e' | b'E' | b'g' | b'G' | b'a' | b'A' => Double,
        b'c' => Char,
        b's' => String,
        b'p' => Pointer,
        _ => {
            return Err(());
        }
    };

    let conv = ConversionSpecification {
        width_is_arg: width_is_arg,
        precision_is_arg: precision_is_arg,
        length_modifier: length_modifier,
        specifier: spec,
    };

    Ok((conv, i + 1))
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
