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

// vcheck harnesses for the trusted `TryFrom` integer specs
macro_rules! vcheck_try_from_test {
    ($name:ident, $from:ty => $to:ty) => {
        verus! {
            #[cfg(not(any(verus_verify_core, verus_keep_ghost)))]
            #[verifier::external_body]
            #[vcheck]
            pub fn $name(a: $from) -> (ret: Option<$to>)
                // Full range-decision spec
                ensures
                    (((<$to>::MIN as int) <= (a as int)) && ((a as int) <= (<$to>::MAX as int)))
                        ==> (ret is Some && (ret->Some_0 as int) == (a as int)),
                    !(((<$to>::MIN as int) <= (a as int)) && ((a as int) <= (<$to>::MAX as int)))
                        ==> (ret is None),
            {
                // `.ok()` maps Ok(v) -> Some(v), Err(_) -> None
                <$to>::try_from(a).ok()
            }
        }
    };
}

// Narrowing (same signedness)
vcheck_try_from_test!(vcheck_tf_u16_u8, u16 => u8);
vcheck_try_from_test!(vcheck_tf_u32_u8, u32 => u8);
vcheck_try_from_test!(vcheck_tf_u32_u16, u32 => u16);
vcheck_try_from_test!(vcheck_tf_u64_u32, u64 => u32);
vcheck_try_from_test!(vcheck_tf_u128_u64, u128 => u64);
vcheck_try_from_test!(vcheck_tf_i16_i8, i16 => i8);
vcheck_try_from_test!(vcheck_tf_i32_i8, i32 => i8);
vcheck_try_from_test!(vcheck_tf_i64_i32, i64 => i32);
vcheck_try_from_test!(vcheck_tf_i128_i64, i128 => i64);

// Sign-crossing: signed -> unsigned (negatives must be rejected)
vcheck_try_from_test!(vcheck_tf_i8_u8, i8 => u8);
vcheck_try_from_test!(vcheck_tf_i32_u8, i32 => u8);
vcheck_try_from_test!(vcheck_tf_i32_u32, i32 => u32);
vcheck_try_from_test!(vcheck_tf_i64_u64, i64 => u64);

// Sign-crossing: unsigned -> signed (large positives must be rejected)
vcheck_try_from_test!(vcheck_tf_u8_i8, u8 => i8);
vcheck_try_from_test!(vcheck_tf_u32_i32, u32 => i32);
vcheck_try_from_test!(vcheck_tf_u64_i64, u64 => i64);

// Platform-dependent widths
vcheck_try_from_test!(vcheck_tf_usize_u32, usize => u32);
vcheck_try_from_test!(vcheck_tf_isize_i32, isize => i32);
vcheck_try_from_test!(vcheck_tf_u64_usize, u64 => usize);
vcheck_try_from_test!(vcheck_tf_i64_isize, i64 => isize);


// vcheck harnesses for the trusted widening `From` integer specs
macro_rules! vcheck_from_test {
    ($name:ident, $from:ty => $to:ty) => {
        verus! {
            #[cfg(not(any(verus_verify_core, verus_keep_ghost)))]
            #[verifier::external_body]
            #[vcheck]
            pub fn $name(a: $from) -> (ret: $to)
                ensures
                    (ret as $from) == a,
            {
                <$to as core::convert::From<$from>>::from(a)
            }
        }
    };
}

vcheck_from_test!(vcheck_from_u8_u16, u8 => u16);
vcheck_from_test!(vcheck_from_u8_u32, u8 => u32);
vcheck_from_test!(vcheck_from_u8_u64, u8 => u64);
vcheck_from_test!(vcheck_from_u8_u128, u8 => u128);
vcheck_from_test!(vcheck_from_u16_u32, u16 => u32);
vcheck_from_test!(vcheck_from_u16_u64, u16 => u64);
vcheck_from_test!(vcheck_from_u32_u64, u32 => u64);
vcheck_from_test!(vcheck_from_u32_u128, u32 => u128);
vcheck_from_test!(vcheck_from_u64_u128, u64 => u128);
vcheck_from_test!(vcheck_from_i8_i16, i8 => i16);
vcheck_from_test!(vcheck_from_i8_i32, i8 => i32);
vcheck_from_test!(vcheck_from_i8_i64, i8 => i64);
vcheck_from_test!(vcheck_from_i16_i32, i16 => i32);
vcheck_from_test!(vcheck_from_i16_i64, i16 => i64);
vcheck_from_test!(vcheck_from_i32_i64, i32 => i64);
vcheck_from_test!(vcheck_from_i32_i128, i32 => i128);
vcheck_from_test!(vcheck_from_i64_i128, i64 => i128);

verus! {

/// blanket `Into` / `TryInto` / `TryFrom` agree with the underlying `From` / `TryFrom`
#[cfg(not(any(verus_verify_core, verus_keep_ghost)))]
#[verifier::external_body]
#[vcheck]
pub fn vcheck_convert_blankets(a: u8, b: u32) -> (ret: bool)
    ensures
        ret,
{
    let i: u32 = a.into();
    let t: Result<u8, core::num::TryFromIntError> = b.try_into();
    let f: Result<u64, core::convert::Infallible> = <u64 as TryFrom<u32>>::try_from(b);
    i == <u32 as From<u8>>::from(a) && t == <u8 as TryFrom<u32>>::try_from(b) && f == Ok(b as u64)
}

} // verus!
