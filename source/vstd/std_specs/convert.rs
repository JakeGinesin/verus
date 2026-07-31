#![allow(unused_imports)]
use super::super::prelude::*;

use core::convert::{From, Into, TryFrom, TryInto};

verus! {

#[verifier::external_trait_specification]
#[verifier::external_trait_extension(FromSpec via FromSpecImpl)]
pub trait ExFrom<T>: Sized {
    type ExternalTraitSpecificationFor: core::convert::From<T>;

    spec fn obeys_from_spec() -> bool;

    spec fn from_spec(v: T) -> Self;

    fn from(v: T) -> (ret: Self)
        ensures
            Self::obeys_from_spec() ==> ret == Self::from_spec(v),
    ;
}

#[verifier::external_trait_specification]
#[verifier::external_trait_extension(IntoSpec via IntoSpecImpl)]
pub trait ExInto<T>: Sized {
    type ExternalTraitSpecificationFor: core::convert::Into<T>;

    spec fn obeys_into_spec() -> bool;

    spec fn into_spec(self) -> T;

    fn into(self) -> (ret: T)
        ensures
            Self::obeys_into_spec() ==> ret == Self::into_spec(self),
    ;
}

impl<T, U: From<T>> IntoSpecImpl<U> for T {
    open spec fn obeys_into_spec() -> bool {
        <U as FromSpec<Self>>::obeys_from_spec()
    }

    open spec fn into_spec(self) -> U {
        U::from_spec(self)
    }
}

pub assume_specification<T, U: From<T>>[ <T as Into<U>>::into ](a: T) -> (ret: U)
    ensures
        call_ensures(U::from, (a,), ret),
;

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExTryFromIntError(core::num::TryFromIntError);

#[verifier::external_trait_specification]
#[verifier::external_trait_extension(TryFromSpec via TryFromSpecImpl)]
pub trait ExTryFrom<T>: Sized {
    type ExternalTraitSpecificationFor: TryFrom<T>;

    type Error;

    spec fn obeys_try_from_spec() -> bool;

    spec fn try_from_spec(v: T) -> Result<Self, Self::Error>;

    fn try_from(v: T) -> (ret: Result<Self, Self::Error>)
        ensures
            Self::obeys_try_from_spec() ==> ret == Self::try_from_spec(v),
    ;
}

#[verifier::external_trait_specification]
#[verifier::external_trait_extension(TryIntoSpec via TryIntoSpecImpl)]
pub trait ExTryInto<T>: Sized {
    type ExternalTraitSpecificationFor: TryInto<T>;

    type Error;

    spec fn obeys_try_into_spec() -> bool;

    spec fn try_into_spec(self) -> Result<T, Self::Error>;

    fn try_into(self) -> (ret: Result<T, Self::Error>)
        ensures
            Self::obeys_try_into_spec() ==> ret == Self::try_into_spec(self),
    ;
}

impl<T, U: TryFrom<T>> TryIntoSpecImpl<U> for T {
    open spec fn obeys_try_into_spec() -> bool {
        <U as TryFromSpec<Self>>::obeys_try_from_spec()
    }

    open spec fn try_into_spec(self) -> Result<U, U::Error> {
        <U as TryFromSpec<Self>>::try_from_spec(self)
    }
}

pub assume_specification<T, U: TryFrom<T>>[ <T as TryInto<U>>::try_into ](a: T) -> (ret: Result<
    U,
    U::Error,
>)
    ensures
        call_ensures(U::try_from, (a,), ret),
;

pub assume_specification<T, U: Into<T>>[ <T as TryFrom<U>>::try_from ](a: U) -> (ret: Result<
    T,
    <T as TryFrom<U>>::Error,
>)
    ensures
        ret.is_ok(),
        call_ensures(U::into, (a,), ret.unwrap()),
;

} // verus!
macro_rules! impl_from_spec {
    ($from: ty => [$($to: ty)*]) => {
        verus!{
        $(
        pub assume_specification[ <$to as core::convert::From<$from>>::from ](a: $from) -> (ret: $to);

        impl FromSpecImpl<$from> for $to {
            open spec fn obeys_from_spec() -> bool {
                true
            }

            open spec fn from_spec(v: $from) -> $to {
                v as $to
            }
        }
        )*
        }
    };
}

impl_from_spec! {u8 => [u16 u32 u64 usize u128]}
impl_from_spec! {u16 => [u32 u64 usize u128]}
impl_from_spec! {u32 => [u64 u128]}
impl_from_spec! {u64 => [u128]}
impl_from_spec! {i8 => [i16 i32 i64 isize i128]}
impl_from_spec! {i16 => [i32 i64 isize i128]}
impl_from_spec! {i32 => [i64 i128]}
impl_from_spec! {i64 => [i128]}

macro_rules! impl_int_try_from_spec {
    ($from:ty => [$($to:ty)*]) => {
        verus!{
        $(
        pub assume_specification[ <$to as TryFrom<$from>>::try_from ](a: $from) -> (ret: Result<$to, <$to as TryFrom<$from>>::Error>);

        impl TryFromSpecImpl<$from> for $to {
            open spec fn obeys_try_from_spec() -> bool {
                true
            }

            open spec fn try_from_spec(v: $from) -> Result<Self, Self::Error> {
                if Self::MIN <= v <= Self::MAX {
                    Ok(v as $to)
                } else {
                    Err(arbitrary())
                }
            }
        }
        )*
        }
    };
}

impl_int_try_from_spec! { u16 => [u8 i8] }
impl_int_try_from_spec! { u32 => [u8 u16 i8 i16 usize isize] }
impl_int_try_from_spec! { u64 => [u8 u16 u32 i8 i16 i32 usize isize] }
impl_int_try_from_spec! { u128 => [u8 u16 u32 u64 i8 i16 i32 i64 usize isize] }
impl_int_try_from_spec! { usize => [u8 u16 u32 u64 u128 i8 i16 i32 i64] }
impl_int_try_from_spec! { i8 => [u8 u16 u32 u64 u128 usize] }
impl_int_try_from_spec! { i16 => [u8 u16 u32 u64 u128 i8 usize] }
impl_int_try_from_spec! { i32 => [u8 u16 u32 u64 u128 i8 i16 usize isize] }
impl_int_try_from_spec! { i64 => [u8 u16 u32 u64 u128 i8 i16 i32 usize isize] }
impl_int_try_from_spec! { i128 => [u8 u16 u32 u64 u128 i8 i16 i32 i64 usize isize] }
impl_int_try_from_spec! { isize => [u8 u16 u32 u64 u128 i8 i16 i32 i64 i128 usize] }

// ---------------------------------------------------------------------------
// PBT harnesses for the trusted `TryFrom` integer specs.
//
// The `impl_int_try_from_spec!` macro above installs *assumed* specs for
// `<$to>::try_from(<$from>)`: in-range values convert via `as`, out-of-range
// values yield `Err`. Those are trusted axioms — if they don't match the real
// std impl, that's unsoundness. Each wrapper below re-states the intended
// range/truncation contract as an `ensures` and calls the real std
// conversion; a `#[pbt(backend = "bolero")]` harness then fuzzes the input
// (edge-biased, so `MIN`/`MAX`/`0`/boundary values are hit) and fails if the
// real conversion violates the assumed spec.
//
// `#[verifier::external_body]` so the ensures is a trusted (pbt-checked) spec
// rather than something Verus proves from the body.
macro_rules! pbt_try_from_test {
    ($name:ident, $from:ty => $to:ty) => {
        verus! {
            #[cfg(not(verus_verify_core))]
            #[verifier::external_body]
            #[pbt(backend = "bolero")]
            pub fn $name(a: $from) -> (ret: Option<$to>)
                // Full range-decision spec (enabled by engine feature A1,
                // which lifts these cross-width `as int` comparisons and the
                // `Option` projection into the SpecInt domain):
                //   * in range  ⟺ Some, with the exact value preserved;
                //   * out of range ⟺ None.
                // Catches wrong-value truncation, false-accepts, AND
                // false-rejects.
                ensures
                    (((<$to>::MIN as int) <= (a as int)) && ((a as int) <= (<$to>::MAX as int)))
                        ==> (ret is Some && (ret->Some_0 as int) == (a as int)),
                    !(((<$to>::MIN as int) <= (a as int)) && ((a as int) <= (<$to>::MAX as int)))
                        ==> (ret is None),
            {
                // `.ok()` maps Ok(v) -> Some(v), Err(_) -> None, sidestepping
                // the opaque TryFromIntError while preserving the ok/value
                // observable the spec constrains.
                <$to>::try_from(a).ok()
            }
        }
    };
}

// Narrowing (same signedness).
pbt_try_from_test!(pbt_tf_u16_u8, u16 => u8);
pbt_try_from_test!(pbt_tf_u32_u8, u32 => u8);
pbt_try_from_test!(pbt_tf_u32_u16, u32 => u16);
pbt_try_from_test!(pbt_tf_u64_u32, u64 => u32);
pbt_try_from_test!(pbt_tf_u128_u64, u128 => u64);
pbt_try_from_test!(pbt_tf_i16_i8, i16 => i8);
pbt_try_from_test!(pbt_tf_i32_i8, i32 => i8);
pbt_try_from_test!(pbt_tf_i64_i32, i64 => i32);
pbt_try_from_test!(pbt_tf_i128_i64, i128 => i64);

// Sign-crossing: signed -> unsigned (negatives must be rejected).
pbt_try_from_test!(pbt_tf_i8_u8, i8 => u8);
pbt_try_from_test!(pbt_tf_i32_u8, i32 => u8);
pbt_try_from_test!(pbt_tf_i32_u32, i32 => u32);
pbt_try_from_test!(pbt_tf_i64_u64, i64 => u64);

// Sign-crossing: unsigned -> signed (large positives must be rejected).
pbt_try_from_test!(pbt_tf_u8_i8, u8 => i8);
pbt_try_from_test!(pbt_tf_u32_i32, u32 => i32);
pbt_try_from_test!(pbt_tf_u64_i64, u64 => i64);

// Platform-dependent widths.
pbt_try_from_test!(pbt_tf_usize_u32, usize => u32);
pbt_try_from_test!(pbt_tf_isize_i32, isize => i32);
pbt_try_from_test!(pbt_tf_u64_usize, u64 => usize);
pbt_try_from_test!(pbt_tf_i64_isize, i64 => isize);


// PBT harnesses for the trusted widening `From` integer specs
// (`impl_from_spec!` above installs `from_spec(v) = v as $to`). Widening is
// value-preserving, so `From::from(a)` narrowed back to `$from` must equal
// `a`; a violation would reveal an unsound widening spec.
macro_rules! pbt_from_test {
    ($name:ident, $from:ty => $to:ty) => {
        verus! {
            #[cfg(not(verus_verify_core))]
            #[verifier::external_body]
            #[pbt(backend = "bolero")]
            pub fn $name(a: $from) -> (ret: $to)
                ensures
                    (ret as $from) == a,
            {
                <$to as core::convert::From<$from>>::from(a)
            }
        }
    };
}

pbt_from_test!(pbt_from_u8_u16, u8 => u16);
pbt_from_test!(pbt_from_u8_u32, u8 => u32);
pbt_from_test!(pbt_from_u8_u64, u8 => u64);
pbt_from_test!(pbt_from_u8_u128, u8 => u128);
pbt_from_test!(pbt_from_u16_u32, u16 => u32);
pbt_from_test!(pbt_from_u16_u64, u16 => u64);
pbt_from_test!(pbt_from_u32_u64, u32 => u64);
pbt_from_test!(pbt_from_u32_u128, u32 => u128);
pbt_from_test!(pbt_from_u64_u128, u64 => u128);
pbt_from_test!(pbt_from_i8_i16, i8 => i16);
pbt_from_test!(pbt_from_i8_i32, i8 => i32);
pbt_from_test!(pbt_from_i8_i64, i8 => i64);
pbt_from_test!(pbt_from_i16_i32, i16 => i32);
pbt_from_test!(pbt_from_i16_i64, i16 => i64);
pbt_from_test!(pbt_from_i32_i64, i32 => i64);
pbt_from_test!(pbt_from_i32_i128, i32 => i128);
pbt_from_test!(pbt_from_i64_i128, i64 => i128);
