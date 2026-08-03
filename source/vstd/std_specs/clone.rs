use super::super::prelude::*;
use core::clone::Clone;

verus! {

#[verifier::external_trait_specification]
pub trait ExClone: Sized {
    type ExternalTraitSpecificationFor: core::clone::Clone;

    fn clone(&self) -> Self;
}

#[verifier::external_trait_specification]
pub trait ExCopy: Clone {
    type ExternalTraitSpecificationFor: core::marker::Copy;
}

/*
#[verifier::external_fn_specification]
pub fn ex_clone_clone_from<T: Clone>(a: &mut T, b: &T)
{
    a.clone_from(b)
}
*/

#[pbt]
pub assume_specification[ <bool as Clone>::clone ](b: &bool) -> (res: bool)
    returns
        b,
;

#[pbt]
pub assume_specification[ <char as Clone>::clone ](c: &char) -> (res: char)
    returns
        c,
;

#[allow(suspicious_double_ref_op)]
pub assume_specification<'b, T: core::marker::PointeeSized, 'a>[ <&'b T as Clone>::clone ](
    b: &'a &'b T,
) -> (res: &'b T)
    ensures
        res == b,
;

/// Shared-ref clone returns the same referent (direct #[pbt] blocked by the
/// nested `&&T` param, which has no sampling strategy).
#[cfg(not(verus_verify_core))]
#[verifier::external_body]
#[allow(suspicious_double_ref_op)]
#[pbt]
pub fn pbt_ref_clone(v: u32) -> (ret: bool)
    ensures
        ret,
{
    let r = &v;
    let cloned: &u32 = Clone::clone(&r);
    core::ptr::eq(cloned, r) && *cloned == v
}

// (no #[pbt]: the quantified ensures uses an untyped binder (`forall|i|`),
// which the engine's quantifier lowering requires to be typed)
pub assume_specification<T: Clone, const N: usize>[ <[T; N] as Clone>::clone ](a: &[T; N]) -> (res:
    [T; N])
    ensures
        forall|i| #![all_triggers] 0 <= i < N ==> cloned::<T>(a@[i], res@[i]),
        a@ =~= res@ ==> a@ == res@,
;

/*
#[verifier::external_fn_specification]
pub fn ex_bool_clone_from(dest: &mut bool, source: &bool)
    ensures *dest == source,
{
    dest.clone_from(source)
}
*/

// Cloning a Tracked copies the underlying ghost T
pub assume_specification<T: Copy>[ <Tracked<T> as Clone>::clone ](b: &Tracked<T>) -> (res: Tracked<
    T,
>)
    ensures
        res == b,
;

pub assume_specification<T>[ <Ghost<T> as Clone>::clone ](b: &Ghost<T>) -> (res: Ghost<T>)
    ensures
        res == b,
;

} // verus!
