use super::super::prelude::*;

use alloc::boxed::Box;
use alloc::rc::Rc;
use alloc::sync::Arc;
use alloc::vec::Vec;
use core::alloc::Allocator;

verus! {

// TODO
// (no direct #[pbt]: `Box<[T]>` params have no sampling strategy — the
// pbt_into_vec wrapper samples a Vec and round-trips through
// into_boxed_slice.)
pub assume_specification<T, A: Allocator>[ <[T]>::into_vec ](b: Box<[T], A>) -> (v: Vec<T, A>)
    ensures
        v@ == b@,
;

#[pbt(T = u32)]
pub assume_specification<T>[ Box::<T>::new ](t: T) -> (v: Box<T>)
    ensures
        *v == t,
;

pub assume_specification<T: core::default::Default>[ <Box<
    T,
> as core::default::Default>::default ]() -> (res: Box<T>)
    ensures
        T::default.ensures((), *res),
;

#[pbt(T = u32)]
pub assume_specification<T>[ Rc::<T>::new ](t: T) -> (v: Rc<T>)
    ensures
        *v == t,
;

pub assume_specification<T: core::default::Default>[ <Rc<
    T,
> as core::default::Default>::default ]() -> (res: Rc<T>)
    ensures
        T::default.ensures((), *res),
;

#[pbt(T = u32)]
pub assume_specification<T>[ Arc::<T>::new ](t: T) -> (v: Arc<T>)
    ensures
        *v == t,
;

pub assume_specification<T: core::default::Default>[ <Arc<
    T,
> as core::default::Default>::default ]() -> (res: Arc<T>)
    ensures
        T::default.ensures((), *res),
;

// (no direct #[pbt]: `&Box<T, A>` params have no sampling strategy — the
// pbt_box_clone wrapper constructs the box from a sampled value.)
pub assume_specification<T: Clone, A: Allocator + Clone>[ <Box<T, A> as Clone>::clone ](
    b: &Box<T, A>,
) -> (res: Box<T, A>)
    ensures
        cloned::<T>(**b, *res),
;

// (no direct #[pbt]: `Rc<T>` params have no sampling strategy — the
// pbt_rc_try_unwrap wrapper constructs the rc from a sampled value and
// covers both the shared and sole-owner branches.)
pub assume_specification<T, A: Allocator>[ Rc::<T, A>::try_unwrap ](v: Rc<T, A>) -> (result: Result<
    T,
    Rc<T, A>,
>)
    ensures
        match result {
            Ok(t) => t == *v,
            Err(e) => e == v,
        },
;

// (no direct #[pbt]: `Rc<T>` params have no sampling strategy — see
// pbt_rc_into_inner.)
pub assume_specification<T, A: Allocator>[ Rc::<T, A>::into_inner ](v: Rc<T, A>) -> (result: Option<
    T,
>)
    ensures
        result matches Some(t) ==> t == *v,
;

// ---------------------------------------------------------------------------
// Composite PBT wrappers for the sites whose params have no sampling
// strategy (Box<[T]>, &Box, Rc — the constructors take direct #[pbt]
// labels above instead). The Default specs stay unannotated (generic
// `T::default.ensures` needs call_ensures lowering).
// ---------------------------------------------------------------------------

/// `Box::clone` (via `cloned::<T>`, identity for `u32`): clone derefs equal.
#[cfg(not(verus_verify_core))]
#[verifier::external_body]
#[pbt]
pub fn pbt_box_clone(t: u32) -> (ret: bool)
    ensures
        ret,
{
    let b = Box::new(t);
    *b.clone() == *b
}

/// `<[T]>::into_vec`: the vec's contents equal the boxed slice's.
#[cfg(not(verus_verify_core))]
#[verifier::external_body]
#[pbt]
pub fn pbt_into_vec(v: Vec<u32>) -> (ret: bool)
    ensures
        ret,
{
    let expected = v.clone();
    let b: Box<[u32]> = v.into_boxed_slice();
    b.into_vec() == expected
}

/// `Rc::try_unwrap`: sole ownership yields Ok(value); a second strong ref
/// yields Err with the original rc's value.
#[cfg(not(verus_verify_core))]
#[verifier::external_body]
#[pbt]
pub fn pbt_rc_try_unwrap(t: u32, shared: bool) -> (ret: bool)
    ensures
        ret,
{
    let v = Rc::new(t);
    if shared {
        let _hold = Rc::clone(&v);
        match Rc::try_unwrap(v) {
            Ok(_) => false,
            Err(e) => *e == t,
        }
    } else {
        Rc::try_unwrap(v) == Ok(t)
    }
}

/// `Rc::into_inner`: Some(t) under sole ownership (the ensures' one-way
/// implication is checked on the Some side; None carries no claim).
#[cfg(not(verus_verify_core))]
#[verifier::external_body]
#[pbt]
pub fn pbt_rc_into_inner(t: u32, shared: bool) -> (ret: bool)
    ensures
        ret,
{
    let v = Rc::new(t);
    if shared {
        let _hold = Rc::clone(&v);
        // ensures only constrains the Some case
        match Rc::into_inner(v) {
            Some(inner) => inner == t,
            None => true,
        }
    } else {
        Rc::into_inner(v) == Some(t)
    }
}

} // verus!
