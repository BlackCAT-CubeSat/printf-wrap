# Change Log

## 0.2.0 &ndash; 2022-09-28

### Changes

* Bumped minimum Rust version to 1.64.0
* Switched from using `std::ffi::CStr` to using `core::ffi::CStr` (Rust 1.64.0+)
* Changed from explicitly implementing `PrintfArgument` for `{std,alloc}::ffi::CString` to blanket-implementing `PrintfArgument` for `T: AsRef<CStr>`
* (Mostly) switched from using the `libc` crate's C integer types to using the equivalent types in `core::ffi` (Rust 1.64.0+)
* Made `libc` crate dependency optional (enabled with the `libc` feature)
* Marked `NullString` and `PrintfFmt<T>` as `Send` and `Sync`
* Changed argument type of `null_str!` from `literal` to `expr`

### Additions

* Added `libc` feature to enable use of integer types available in `libc` but not `core::ffi`

### Removals

* Removed the `std` feature as the types previously used in `std` are now available in `core` contexts

## 0.1.0 &ndash; 2022-08-03

* Initial release.
