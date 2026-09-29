use super::super::prelude::*;

use alloc::boxed::Box;
use alloc::rc::Rc;
use alloc::sync::Arc;
use alloc::vec::Vec;
use core::alloc::Allocator;

verus! {

// TODO
// (no direct vcheck: `Box<[T]>` params have no sampling strategy)
pub assume_specification<T, A: Allocator>[ <[T]>::into_vec ](b: Box<[T], A>) -> (v: Vec<T, A>)
    ensures
        v@ == b@,
;

#[vcheck(T = u32)]
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

#[vcheck(T = u32)]
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

#[vcheck(T = u32)]
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

// (no direct vcheck: `&Box<T, A>` params have no sampling strategy)
pub assume_specification<T: Clone, A: Allocator + Clone>[ <Box<T, A> as Clone>::clone ](
    b: &Box<T, A>,
) -> (res: Box<T, A>)
    ensures
        cloned::<T>(**b, *res),
;

// (no direct vcheck: `Rc<T>` params have no sampling strategy)
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

// (no direct vcheck: `Rc<T>` params have no sampling strategy)
pub assume_specification<T, A: Allocator>[ Rc::<T, A>::into_inner ](v: Rc<T, A>) -> (result: Option<
    T,
>)
    ensures
        result matches Some(t) ==> t == *v,
;

// Composite vcheck wrappers for the sites whose params have no sampling strategy

/// `Box::clone` (via `cloned::<T>`, identity for `u32`): clone derefs equal
#[cfg(not(any(verus_verify_core, verus_keep_ghost)))]
#[verifier::external_body]
#[vcheck]
pub fn vcheck_box_clone(t: u32) -> (ret: bool)
    ensures
        ret,
{
    let b = Box::new(t);
    *b.clone() == *b
}

/// `<[T]>::into_vec`: the vec's contents equal the boxed slice's
#[cfg(not(any(verus_verify_core, verus_keep_ghost)))]
#[verifier::external_body]
#[vcheck]
pub fn vcheck_into_vec(v: Vec<u32>) -> (ret: bool)
    ensures
        ret,
{
    let expected = v.clone();
    let b: Box<[u32]> = v.into_boxed_slice();
    b.into_vec() == expected
}

/// `Rc::try_unwrap`: sole ownership yields Ok(value)
#[cfg(not(any(verus_verify_core, verus_keep_ghost)))]
#[verifier::external_body]
#[vcheck]
pub fn vcheck_rc_try_unwrap(t: u32, shared: bool) -> (ret: bool)
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

/// `Rc::into_inner`: Some(t) under sole ownership
#[cfg(not(any(verus_verify_core, verus_keep_ghost)))]
#[verifier::external_body]
#[vcheck]
pub fn vcheck_rc_into_inner(t: u32, shared: bool) -> (ret: bool)
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

verus! {

/// Box / Rc / Arc `default` hold `u32::default()`
#[cfg(not(any(verus_verify_core, verus_keep_ghost)))]
#[verifier::external_body]
#[vcheck]
pub fn vcheck_smart_ptr_defaults(k: u8) -> (ret: bool)
    ensures
        ret,
{
    let b: Box<u32> = Default::default();
    let r: Rc<u32> = Default::default();
    let a: Arc<u32> = Default::default();
    *b == 0 && *r == 0 && *a == 0 && k == k
}

} // verus!
