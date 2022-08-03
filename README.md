# printf-wrap

[![Crates.io](https://img.shields.io/crates/v/printf-wrap)](https://crates.io/crates/printf-wrap)
[![docs.rs](https://img.shields.io/docsrs/printf-wrap)](https://docs.rs/printf-wrap)

`printf-wrap` is a Rust crate with types to help developers write safe wrappers for
C functions using [`printf(3)`]-style format strings and varargs.
In particular, `PrintfFmt<(T_1, T_2, ..., T_N)>` is a wrapper around a null-terminated string
that is guaranteed to be a valid format string for use with `N` arguments of types
`T_1`,&nbsp;`T_2`,&nbsp;&hellip;,&nbsp;`T_N`
when the arguments are mapped through the `PrintfArgument::as_c_val()` method.

The following example shows a safe wrapper for calling `printf` with two arguments,
along with a use of it.

```rust
use printf_wrap::{PrintfFmt, PrintfArgument};
use libc::{c_int, printf};

/// Safe wrapper for calling printf with two value arguments.
pub fn printf_with_2_args<T, U>(fmt: PrintfFmt<(T, U)>, arg1: T, arg2: U) -> c_int
where
    T: PrintfArgument,
    U: PrintfArgument,
{
    unsafe { printf(fmt.as_ptr(), arg1.as_c_val(), arg2.as_c_val()) }
}

const MY_FORMAT_STRING: PrintfFmt<(u32, i32)> =
    PrintfFmt::new_or_panic("unsigned = %u, signed = %d\0");

fn main() {
    printf_with_2_args(MY_FORMAT_STRING, 42, -7);
}
```

In the example, `MY_FORMAT_STRING` is determined to be a valid format string
for arguments of `(u32, i32)` _at compile time_, with zero runtime overhead.
With a little macro magic, generating wrappers for different numbers of post-format
arguments is easy, with `printf-wrap` handling the validation and conversion of
values to C-compatible equivalents.

## Features

**std** &ndash; enables support for the [`CStr`] and [`CString`] types from [`std`].
Enabled by default; if you want to use this crate in `#[no_std]` environments,
[`default-features = false`] in the dependency declaration is your friend.

**example** &ndash; enables a demonstration of the use of `printf-wrap`
with some wrappers around functions from the C standard library.

## License

This crate is licensed under either of the [MIT license](LICENSE-MIT)
or the [Apache License version 2.0](LICENSE-Apache-2.0) at your option.

[`printf(3)`]: https://man7.org/linux/man-pages/man3/printf.3.html
[`std`]: https://doc.rust-lang.org/std/index.html
[`CStr`]: https://doc.rust-lang.org/std/ffi/type.CStr.html
[`CString`]: https://doc.rust-lang.org/std/ffi/type.CString.html
[`default-features = false`]: https://doc.rust-lang.org/cargo/reference/features.html#dependency-features
