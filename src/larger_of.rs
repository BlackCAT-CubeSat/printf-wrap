//! Implementations of [`LargerOfOp`].

use crate::LargerOfOp;

/// Implementations of [`LargerOfOp`]`<$smaller>*`, `LargerOfOp<$same>*`,
/// and `LargerOfOp<$larger>*` for `$implementor*`.
///
/// The macro assumes that:
///
/// * Types in `$smaller` are smaller than each of the `$implementor`s.
/// * Types in `$same` are the same size as each of the `$implementor`s.
/// * Types in `$larger` are larger than each of the `$implementor`s.
macro_rules! loo_impl {

    // '@ 0' and '@ 1' generate all impls for a single $implementor.
    ( @ 0 $implementor:ty : ( $($smaller:ty)* ) ( $($same:ty)* ) ( $($larger:ty)* ) ) => {
        $(
            impl LargerOfOp<$smaller> for $implementor {
                type Output = $implementor;
            }
        )*

        $(
            impl LargerOfOp<$same> for $implementor {
                type Output = $implementor;
            }
        )*

        $(
            impl LargerOfOp<$larger> for $implementor {
                type Output = $larger;
            }
        )*
    };
    ( @ 1 $attr:meta $implementor:ty : ( $($smaller:ty)* ) ( $($same:ty)* ) ( $($larger:ty)* ) ) => {
        $(
            #[$attr]
            impl LargerOfOp<$smaller> for $implementor {
                type Output = $implementor;
            }
        )*

        $(
            #[$attr]
            impl LargerOfOp<$same> for $implementor {
                type Output = $implementor;
            }
        )*

        $(
            #[$attr]
            impl LargerOfOp<$larger> for $implementor {
                type Output = $larger;
            }
        )*
    };

    // '@ 2' and '@ 3' iterate over each $implementor.
    // This intermediate step is needed as macros don't directly
    // support nested iteration well.
    ( @ 2 $($implementor:ty)* : $smaller:tt $same:tt $larger:tt ) => {
        $( loo_impl! { @ 0 $implementor : $smaller $same $larger } )*
    };
    ( @ 3 $attr:meta $($implementor:ty)* : $smaller:tt $same:tt $larger:tt ) => {
        $( loo_impl! { @ 1 $attr $implementor : $smaller $same $larger } )*
    };

    // The actual branches users of the macro will use:
    ( $($implementor:ty)* : $($smaller:ty)* : $($same:ty)* : $($larger:ty)* ) => {
        loo_impl! { @ 2 $($implementor)* : ( $($smaller)* ) ( $($same)* ) ( $($larger)* ) }
    };
    ( @ $attr:meta $($implementor:ty)* : $($smaller:ty)* : $($same:ty)* : $($larger:ty)* ) => {
        loo_impl! { @ 3 $attr $($implementor)* : ( $($smaller)* ) ( $($same)* ) ( $($larger)* ) }
    };
}

loo_impl! { u8 i8     : : u8 i8 : u16 i16 u32 i32 u64 i64 u128 i128 }
loo_impl! { u16 i16   : u8 i8 : u16 i16 : u32 i32 u64 i64 u128 i128 }
loo_impl! { u32 i32   : u8 i8 u16 i16 : u32 i32 : u64 i64 u128 i128 }
loo_impl! { u64 i64   : u8 i8 u16 i16 u32 i32 : u64 i64 : u128 i128 }
loo_impl! { u128 i128 : u8 i8 u16 i16 u32 i32 u64 i64 : u128 i128 : }

loo_impl! { usize isize : : usize isize : }

loo_impl! {
    @ cfg(target_pointer_width = "16")
    usize isize : u8 i8 : u16 i16 : u32 i32 u64 i64 u128 i128
}
loo_impl! {
    @ cfg(target_pointer_width = "16")
    u8 i8 : : : usize isize
}
loo_impl! {
    @ cfg(target_pointer_width = "16")
    u16 i16 : : usize isize :
}
loo_impl! {
    @ cfg(target_pointer_width = "16")
    u32 i32 u64 i64 u128 i128 : usize isize : :
}

loo_impl! {
    @ cfg(target_pointer_width = "32")
    usize isize : u8 i8 u16 i16 : u32 i32 : u64 i64 u128 i128
}
loo_impl! {
    @ cfg(target_pointer_width = "32")
    u8 i8 u16 i16 : : : usize isize
}
loo_impl! {
    @ cfg(target_pointer_width = "32")
     u32 i32 : : usize isize :
}
loo_impl! {
    @ cfg(target_pointer_width = "32")
    u64 i64 u128 i128 : usize isize : :
}

loo_impl! {
    @ cfg(target_pointer_width = "64")
    usize isize : u8 i8 u16 i16 u32 i32 : u64 i64 : u128 i128
}
loo_impl! {
    @ cfg(target_pointer_width = "64")
    u8 i8 u16 i16 u32 i32 : : : usize isize
}
loo_impl! {
    @ cfg(target_pointer_width = "64")
    u64 i64 : : usize isize :
}
loo_impl! {
    @ cfg(target_pointer_width = "64")
    u128 i128 : usize isize : :
}
