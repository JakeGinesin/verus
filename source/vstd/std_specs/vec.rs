use super::super::prelude::*;
// the iter/core spec-trait machinery stays gated on `verus_keep_ghost`
#[cfg(verus_keep_ghost)]
use super::iter::{FromIteratorSpecImpl, IteratorSpec};
use verus_builtin::*;

#[cfg(verus_keep_ghost)]
use super::super::slice::SliceIndexSpec;
#[cfg(verus_keep_ghost)]
use super::core::IndexSpec;
use alloc::collections::TryReserveError;
use alloc::vec::{IntoIter, Vec};
use core::alloc::Allocator;
use core::clone::Clone;
use core::marker::PhantomData;
use core::ops::Index;
use core::option::Option;
use core::option::Option::None;
use core::slice::SliceIndex;

use verus as verus_skip_verusfmt;
verus_skip_verusfmt! {

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::accept_recursive_types(T)]
#[verifier::reject_recursive_types(A)]
pub struct ExVec<T, A: Allocator>(Vec<T, A>);

pub trait VecAdditionalSpecFns<T>: View<V = Seq<T>> {
    spec fn spec_index(&self, i: int) -> T
        recommends
            0 <= i < self.view().len(),
    ;
}

impl<T, A: Allocator> VecAdditionalSpecFns<T> for Vec<T, A> {
    #[verifier::inline]
    open spec fn spec_index(&self, i: int) -> T {
        self.view().index(i)
    }
}

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExTryReserveError(alloc::collections::TryReserveError);

// We still have a special case for Vec::index on usize.
// The general Vec::index case now goes through the Index trait,
// but this special case is still here because it's more direct and efficient in its SMT encoding,
// and Vec::index on usize is very common.
//
// So this is a bit of a hack, but we just manually redirect
// `vec[i]` to this function here from rust_to_vir_expr.
#[verifier::external_body]
#[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::vstd::std_specs::vec::vec_index")]
#[vcheck(T = u32, A = alloc::alloc::Global)]
pub fn vec_index<T, A: Allocator>(vec: &Vec<T, A>, i: usize) -> (element: &T)
    requires
        i < vec.view().len(),
    ensures
        *element == vec.view().index(i as int),
    no_unwind
{
    &vec[i]
}

/// This is a specification for the indexing operator `vec[i]` when it expands to the `IndexMut` trait
#[doc(hidden)]
#[verifier::external_body]
#[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::vstd::std_specs::vec::vec_index_mut")]
pub fn vec_index_mut<T, A: Allocator>(vec: &mut Vec<T, A>, i: usize) -> (element: &mut T)
    requires
        i < vec.view().len(),
    ensures
        *element == old(vec)@.index(i as int),
        final(vec)@ == old(vec)@.update(i as int, *final(element)),

        *final(element) == final(vec).view().index(i as int),
    no_unwind
{
    &mut vec[i]
}

////// Len (with autospec)
pub uninterp spec fn spec_vec_len<T, A: Allocator>(v: &Vec<T, A>) -> usize;

// This axiom is slightly better than defining spec_vec_len to just be `v@.len() as usize`
// (the axiom also shows that v@.len() is in-bounds for usize)
pub broadcast proof fn axiom_spec_len<T, A: Allocator>(v: &Vec<T, A>)
    ensures
        #[trigger] spec_vec_len(v) == v@.len(),
{
    admit();
}

// (no vcheck on the assume_specification: `spec_vec_len` is uninterp)
#[verifier::when_used_as_spec(spec_vec_len)]
pub assume_specification<T, A: Allocator>[ Vec::<T, A>::len ](vec: &Vec<T, A>) -> (len: usize)
    ensures
        len == spec_vec_len(vec),
    no_unwind
;

#[cfg(not(any(verus_verify_core, verus_keep_ghost)))]
#[verifier::external_body]
#[vcheck]
pub fn vcheck_vec_len(vec: Vec<u32>) -> (len: usize)
    ensures
        len == vec@.len(),
{
    Vec::<u32>::len(&vec)
}

// Bounded-size wrappers for the allocation-hazard family: the sampled size is `u16`
#[cfg(not(any(verus_verify_core, verus_keep_ghost)))]
#[verifier::external_body]
#[vcheck]
pub fn vcheck_vec_with_capacity_bounded(capacity: u16) -> (v: Vec<u32>)
    ensures
        v@ == Seq::<u32>::empty(),
{
    Vec::<u32>::with_capacity(capacity as usize)
}

#[cfg(not(any(verus_verify_core, verus_keep_ghost)))]
#[verifier::external_body]
#[vcheck]
pub fn vcheck_vec_reserve_bounded(vec: &mut Vec<u32>, additional: u16)
    ensures
        final(vec)@ == old(vec)@,
{
    Vec::<u32>::reserve(vec, additional as usize)
}

#[cfg(not(any(verus_verify_core, verus_keep_ghost)))]
#[verifier::external_body]
#[vcheck]
pub fn vcheck_vec_from_elem_bounded(elem: u32, n: u16) -> (ret: bool)
    ensures ret,
{
    let v = alloc::vec::from_elem(elem, n as usize);
    v.len() == n as usize && v.iter().all(|x| *x == elem)
}

/// `Vec::resize` over the bounded (u16) size domain: truncates or extends with the fill value
#[cfg(not(any(verus_verify_core, verus_keep_ghost)))]
#[verifier::external_body]
#[vcheck]
pub fn vcheck_vec_resize_bounded(vec: Vec<u32>, n: u16, value: u32) -> (ret: bool)
    ensures ret,
{
    let mut v = vec.clone();
    v.resize(n as usize, value);
    let n = n as usize;
    v.len() == n
        && v[..n.min(vec.len())] == vec[..n.min(vec.len())]
        && v[n.min(vec.len())..].iter().all(|x| *x == value)
}

/// `Vec::new_in` at `A = Global` is empty
#[cfg(not(any(verus_verify_core, verus_keep_ghost)))]
#[verifier::external_body]
#[vcheck]
pub fn vcheck_vec_new_in_global() -> (ret: bool)
    ensures ret,
{
    let v: Vec<u32> = Vec::new_in(alloc::alloc::Global);
    v.is_empty()
}

/// Bare `<Vec as PartialEq>::eq` spec (contract lives in the spec-impl trait)
#[cfg(not(any(verus_verify_core, verus_keep_ghost)))]
#[verifier::external_body]
#[vcheck]
pub fn vcheck_vec_eq(x: Vec<u32>, y: Vec<u32>) -> (ret: bool)
    ensures ret,
{
    (x == y) == (x.len() == y.len() && x.iter().zip(y.iter()).all(|(a, b)| a == b))
        && x == x
}



////// Other functions
#[vcheck(T = u32)]
pub assume_specification<T>[ Vec::<T>::new ]() -> (v: Vec<T>)
    ensures
        v@ == Seq::<T>::empty(),
;

#[vcheck(T = u32)]
pub assume_specification<T>[ <Vec<T> as core::default::Default>::default ]() -> (v: Vec<T>)
    ensures
        v@ == Seq::<T>::empty(),
;

pub assume_specification<T, A: Allocator>[ Vec::<T, A>::new_in ](alloc: A) -> (v: Vec<T, A>)
    ensures
        v@ == Seq::<T>::empty(),
;

// (no vcheck directly on with_capacity / reserve / try_reserve / from_elem)
pub assume_specification<T>[ Vec::<T>::with_capacity ](capacity: usize) -> (v: Vec<T>)
    ensures
        v@ == Seq::<T>::empty(),
;

pub assume_specification<T, A: Allocator>[ Vec::<T, A>::with_capacity_in ](capacity: usize, alloc: A) -> (v: Vec<T, A>)
    ensures
        v@ == Seq::<T>::empty(),
;

pub assume_specification<T, A: Allocator>[ Vec::<T, A>::reserve ](
    vec: &mut Vec<T, A>,
    additional: usize,
)
    ensures
        final(vec)@ == old(vec)@,
;

#[vcheck(T = u32, A = alloc::alloc::Global)] // vc#1359
pub assume_specification<T, A: Allocator>[ Vec::<T, A>::try_reserve ](
    vec: &mut Vec<T, A>,
    additional: usize,
) -> (result: Result<(), TryReserveError>)
    ensures
        final(vec)@ == old(vec)@,
;

#[vcheck(T = u32, A = alloc::alloc::Global)]
pub assume_specification<T, A: Allocator>[ Vec::<T, A>::push ](vec: &mut Vec<T, A>, value: T)
    ensures
        final(vec)@ == old(vec)@.push(value),
;

#[vcheck(T = u32, A = alloc::alloc::Global)]
pub assume_specification<T, A: Allocator>[ Vec::<T, A>::pop ](vec: &mut Vec<T, A>) -> (value:
    Option<T>)
    ensures
        old(vec)@.len() > 0 ==> value == Some(old(vec)@[old(vec)@.len() - 1])
            && final(vec)@ == old(vec)@.take(old(vec)@.len() - 1),
        old(vec)@.len() == 0 ==> value == None::<T> && final(vec)@ == old(vec)@,
;

#[vcheck(T = u32, A = alloc::alloc::Global)]
pub assume_specification<T, A: Allocator>[ Vec::<T, A>::append ](
    vec: &mut Vec<T, A>,
    other: &mut Vec<T, A>,
)
    ensures
        final(vec)@ == old(vec)@ + old(other)@,
        final(other)@ == Seq::<T>::empty(),
;

// (no vcheck: the quantified ensures mixes `final(vec)@[i]` with an if/else over `old(vec)`)
pub assume_specification<T: core::clone::Clone, A: Allocator>[ Vec::<T, A>::extend_from_slice ](
    vec: &mut Vec<T, A>,
    other: &[T],
)
    ensures
        final(vec)@.len() == old(vec)@.len() + other@.len(),
        forall|i: int|
            #![trigger final(vec)@[i]]
            0 <= i < final(vec)@.len() ==> if i < old(vec)@.len() {
                final(vec)@[i] == old(vec)@[i]
            } else {
                cloned::<T>(other@[i - old(vec)@.len()], final(vec)@[i])
            },
;

#[cfg(verus_keep_ghost)]
impl<T: Sized, I: SliceIndex<[T]>, A: Allocator> super::core::IndexSpecImpl<I> for Vec<T, A> {
    open spec fn index_req(&self, index: &I) -> bool {
        forall|s: &[T]| #[trigger] s@ == self@ ==> index.in_bounds(s)
    }
}

pub assume_specification<T, I: SliceIndex<[T]>, A: Allocator>[Vec::<T, A>::index](
    vec: &Vec<T, A>,
    i: I,
) -> (r: &<Vec<T, A> as Index<I>>::Output)
    ensures
        exists|s: &[T]| #[trigger] s@ == vec@ && call_ensures(<I as SliceIndex<[T]>>::index, (i, s), r),
;

#[vcheck(T = u32, A = alloc::alloc::Global)]
pub assume_specification<T, A: Allocator>[ Vec::<T, A>::swap_remove ](
    vec: &mut Vec<T, A>,
    i: usize,
) -> (element: T)
    requires
        i < old(vec).len(),
    ensures
        element == old(vec)[i as int],
        final(vec)@ == old(vec)@.update(i as int, old(vec)@.last()).drop_last(),
;

#[vcheck(T = u32, A = alloc::alloc::Global)]
pub assume_specification<T, A: Allocator>[ Vec::<T, A>::insert ](
    vec: &mut Vec<T, A>,
    i: usize,
    element: T,
)
    requires
        i <= old(vec).len(),
    ensures
        final(vec)@ == old(vec)@.insert(i as int, element),
;

#[vcheck(T = u32, A = alloc::alloc::Global)]
pub assume_specification<T, A: Allocator> [ <Vec<T, A>>::is_empty ](
    v: &Vec<T, A>,
) -> (res: bool)
    ensures res <==> v@.len() == 0,
;

#[vcheck(T = u32, A = alloc::alloc::Global)]
pub assume_specification<T, A: Allocator>[ Vec::<T, A>::remove ](
    vec: &mut Vec<T, A>,
    i: usize,
) -> (element: T)
    requires
        i < old(vec).len(),
    ensures
        element == old(vec)[i as int],
        final(vec)@ == old(vec)@.remove(i as int),
;

#[vcheck(T = u32, A = alloc::alloc::Global)]
pub assume_specification<T, A: Allocator>[ Vec::<T, A>::clear ](vec: &mut Vec<T, A>)
    ensures
        final(vec).view() == Seq::<T>::empty(),
;

#[vcheck(T = u32, A = alloc::alloc::Global)]
pub assume_specification<T, A: Allocator>[ Vec::<T, A>::as_slice ](vec: &Vec<T, A>) -> (slice: &[T])
    ensures
        slice@ == vec@,
;

#[doc(hidden)]
#[vcheck(T = u32, A = alloc::alloc::Global)] // vc#1357
pub assume_specification<T, A: Allocator>[ Vec::<T, A>::as_mut_slice ](vec: &mut Vec<T, A>) -> (slice: &mut [T])
    ensures
        slice@ == old(vec)@,
        final(slice)@ == final(vec)@,
;

#[vcheck(T = u32, A = alloc::alloc::Global)]
pub assume_specification<T, A: Allocator>[ <Vec<T, A> as core::ops::Deref>::deref ](
    vec: &Vec<T, A>,
) -> (slice: &[T])
    ensures
        slice@ == vec@,
;

#[vcheck(T = u32, A = alloc::alloc::Global)] // vc#1356
pub assume_specification<T, A: Allocator>[ <Vec<T, A> as core::ops::DerefMut>::deref_mut ](
    vec: &mut Vec<T, A>,
) -> (slice: &mut [T])
    ensures
        slice@ == old(vec)@,
        final(slice)@ == final(vec)@,
;

#[vcheck(T = u32, A = alloc::alloc::Global)]
pub assume_specification<T, A: Allocator + core::clone::Clone>[ Vec::<T, A>::split_off ](
    vec: &mut Vec<T, A>,
    at: usize,
) -> (return_value: Vec<T, A>)
    requires
        at <= old(vec)@.len(),
    ensures
        final(vec)@ == old(vec)@.take(at as int),
        return_value@ == old(vec)@.skip(at as int),
;

pub open spec fn vec_clone_trigger<T, A: Allocator>(v1: Vec<T, A>, v2: Vec<T, A>) -> bool {
    true
}

// (no vcheck: the ensures references `vec_clone_trigger`, a spec fn over `Vec<T, A>`)
pub assume_specification<T: Clone, A: Allocator + Clone>[ <Vec<T, A> as Clone>::clone ](
    vec: &Vec<T, A>,
) -> (res: Vec<T, A>)
    ensures
        res.len() == vec.len(),
        forall|i| #![all_triggers] 0 <= i < vec.len() ==> cloned::<T>(vec[i], res[i]),
        vec_clone_trigger(*vec, res),
        vec@ =~= res@ ==> vec@ == res@,
;

pub broadcast proof fn vec_clone_deep_view_proof<T: DeepView, A: Allocator>(
    v1: Vec<T, A>,
    v2: Vec<T, A>,
)
    requires
        #[trigger] vec_clone_trigger(v1, v2),
        v1.deep_view() =~= v2.deep_view(),
    ensures
        v1.deep_view() == v2.deep_view(),
{
}

#[vcheck(T = u32, A = alloc::alloc::Global)]
pub assume_specification<T, A: Allocator>[ Vec::<T, A>::truncate ](vec: &mut Vec<T, A>, len: usize)
    ensures
        len <= old(vec).len() ==> final(vec)@ == old(vec)@.take(len as int),
        len > old(vec).len() ==> final(vec)@ == old(vec)@,
;

pub assume_specification<T: Clone, A: Allocator>[ Vec::<T, A>::resize ](
    vec: &mut Vec<T, A>,
    len: usize,
    value: T,
)
    ensures
        len <= old(vec).len() ==> final(vec)@ == old(vec)@[..len],
        len > old(vec).len() ==> {
            &&& final(vec)@.len() == len
            &&& final(vec)@[..old(vec).len()] == old(vec)@
            &&& forall|i| #![all_triggers] old(vec).len() <= i < len ==> cloned::<T>(value, final(vec)@[i])
        },
;

pub broadcast proof fn axiom_vec_index_decreases<A>(v: Vec<A>, i: int)
    requires
        0 <= i < v.len(),
    ensures
        #[trigger] (decreases_to!(v => v[i])),
{
    admit();
}

pub assume_specification<T: PartialEq<U>, U, A1: Allocator, A2: Allocator>[ <Vec<T, A1> as PartialEq<Vec<U, A2>>>::eq ](
    x: &Vec<T, A1>,
    y: &Vec<U, A2>,
) -> bool
;

#[cfg(verus_keep_ghost)]
impl<T: super::cmp::PartialEqSpec<U>, U, A1: Allocator, A2: Allocator> super::cmp::PartialEqSpecImpl<Vec<U, A2>> for Vec<T, A1> {
    open spec fn obeys_eq_spec() -> bool {
        T::obeys_eq_spec()
    }

    open spec fn eq_spec(&self, other: &Vec<U, A2>) -> bool {
        &&& self.len() == other.len()
        &&& forall|i: int| #![auto] 0 <= i < self.len() ==> self[i].eq_spec(&other[i])
    }
}

// The `into_iter` method of a `Vec` returns an iterator of type `IntoIter`,
// so we specify that type here.
#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::accept_recursive_types(T)]
#[verifier::reject_recursive_types(A)]
pub struct ExIntoIter<T, A: Allocator>(IntoIter<T, A>);

// To allow reasoning about the "contents" of the Vec iterator, without using
// a prophecy, we need a function that gives us the underlying sequence of the original vec.
pub uninterp spec fn into_iter_elts<T, A: Allocator>(i: IntoIter<T, A>) -> Seq<T>;

#[cfg(verus_keep_ghost)]
impl <T, A: Allocator> super::iter::IteratorSpecImpl for IntoIter<T, A> {
    open spec fn obeys_prophetic_iter_laws(&self) -> bool {
        true
    }

    uninterp spec fn remaining(&self) -> Seq<Self::Item>;
    uninterp spec fn will_return_none(&self) -> bool;
    uninterp spec fn decrease(&self) -> Option<nat>;

    open spec fn peek(&self, index: int) -> Option<Self::Item> {
        if 0 <= index < into_iter_elts(*self).len() {
            Some(into_iter_elts(*self)[index])
        } else {
            None
        }
    }
}

#[cfg(verus_keep_ghost)]
impl <T, A: Allocator> super::iter::DoubleEndedIteratorSpecImpl for IntoIter<T, A> {
    open spec fn peek_back(&self, index: int) -> Option<Self::Item> {
        let len = into_iter_elts(*self).len();
        if 0 <= index < len {
            Some(into_iter_elts(*self)[len - index - 1])
        } else {
            None
        }
    }
}

// This is used by `vec![x; n]`
pub assume_specification<T: Clone>[ alloc::vec::from_elem ](elem: T, n: usize) -> (v: Vec<T>)
    ensures
        v.len() == n,
        forall |i| 0 <= i < n ==> cloned(elem, #[trigger] v@[i]);

pub assume_specification<T, A: Allocator>[ Vec::<T, A>::into_iter ](vec: Vec<T, A>) -> (iter: <Vec<
    T,
    A,
> as core::iter::IntoIterator>::IntoIter)
    ensures
        IteratorSpec::remaining(&iter) == vec@,
        into_iter_elts(iter) == IteratorSpec::remaining(&iter),
        IteratorSpec::decrease(&iter) is Some,
;

pub assume_specification<'a, T, A: Allocator> [<&'a Vec<T, A> as core::iter::IntoIterator>::into_iter] (vec: &'a Vec<T, A>) ->
    (iter: <&'a Vec<T, A> as core::iter::IntoIterator>::IntoIter)
    ensures
        IteratorSpec::remaining(&iter) == vec@.as_ref(),
        super::slice::into_iter_elts(iter) == IteratorSpec::remaining(&iter).unref(),
        IteratorSpec::decrease(&iter) is Some,
;

#[cfg(verus_keep_ghost)]
impl<T>  FromIteratorSpecImpl<T> for Vec<T> {
    open spec fn from_iter_ensures(remaining: Seq<T>, s: Self) -> bool {
        remaining == s@
    }
}

pub broadcast proof fn lemma_vec_obeys_eq_spec<T: PartialEq>()
    requires
        super::super::laws_eq::obeys_eq::<T>(),
    ensures
        #[trigger] super::super::laws_eq::obeys_eq::<Vec<T>>(),
{
    broadcast use {axiom_spec_len, super::super::seq::group_seq_lemmas};
    reveal(super::super::laws_eq::obeys_eq_spec_properties);
}

pub broadcast proof fn lemma_vec_obeys_view_eq<T: PartialEq + View>()
    requires
        super::super::laws_eq::obeys_concrete_eq::<T>(),
    ensures
        #[trigger] super::super::laws_eq::obeys_view_eq::<Vec<T>>(),
{
    use super::cmp::PartialEqSpec;
    broadcast use {axiom_spec_len, super::super::seq::group_seq_lemmas};
    reveal(super::super::laws_eq::obeys_eq_spec_properties);
    reveal(super::super::laws_eq::obeys_concrete_eq);
    reveal(super::super::laws_eq::obeys_view_eq);
    assert(forall|x: Vec<T>, y: Vec<T>| x.eq_spec(&y) ==> x@ == y@);
}

pub broadcast proof fn lemma_vec_obeys_deep_eq<T: PartialEq + DeepView>()
    requires
        super::super::laws_eq::obeys_deep_eq::<T>(),
    ensures
        #[trigger] super::super::laws_eq::obeys_deep_eq::<Vec<T>>(),
{
    use super::cmp::PartialEqSpec;
    broadcast use {axiom_spec_len, super::super::seq::group_seq_lemmas};
    reveal(super::super::laws_eq::obeys_eq_spec_properties);
    reveal(super::super::laws_eq::obeys_deep_eq);
    assert(forall|x: Vec<T>, y: Vec<T>| x.eq_spec(&y) ==> x.deep_view() == y.deep_view());
    assert forall|x: Vec<T>, y: Vec<T>| x.deep_view() == y.deep_view() implies x.eq_spec(&y) by {
        assert(x.deep_view().len() == y.deep_view().len());
        assert forall|i: int| #![auto] 0 <= i < x.len() implies x[i].eq_spec(&y[i]) by {
            assert(x.deep_view()[i] == y.deep_view()[i]);
        }
    }
}

pub broadcast axiom fn axiom_vec_has_resolved<T>(vec: Vec<T>, i: int)
    ensures
        0 <= i < vec.len() ==> #[trigger] has_resolved::<Vec<T>>(vec) ==> has_resolved(
            #[trigger] vec@[i],
        ),
;

pub broadcast axiom fn axiom_vec_decreases_to_view<T>(v: Vec<T>)
    ensures
        #[trigger] (decreases_to!(v => v@));

pub broadcast group group_vec_axioms {
    axiom_spec_len,
    axiom_vec_index_decreases,
    vec_clone_deep_view_proof,
    axiom_vec_has_resolved,
    axiom_vec_decreases_to_view,
}

pub axiom fn tracked_borrow_slice<T, A: Allocator>(tracked vec: &Vec<T, A>) -> (tracked t: &[T])
    ensures t@ == vec@;

pub axiom fn tracked_borrow_mut_slice<T, A: Allocator>(tracked vec: &mut Vec<T, A>) -> (tracked t: &mut [T])
    ensures
        (*t)@ == old(vec)@,
        (*t).len() == final(t).len(),
        final(vec)@ == final(t)@;

} // verus!

verus! {

/// `extend_from_slice` appends clones of the other slice
#[cfg(not(any(verus_verify_core, verus_keep_ghost)))]
#[verifier::external_body]
#[vcheck]
pub fn vcheck_vec_extend_from_slice(v: Vec<u32>, other: Vec<u32>) -> (ret: bool)
    ensures
        ret,
{
    let mut v2 = v.clone();
    v2.extend_from_slice(&other);
    v2.len() == v.len() + other.len() && (0..v2.len()).all(
        |i|
            if i < v.len() {
                v2[i] == v[i]
            } else {
                v2[i] == other[i - v.len()]
            },
    )
}

/// `clone` copies element-wise and preserves the view
#[cfg(not(any(verus_verify_core, verus_keep_ghost)))]
#[verifier::external_body]
#[vcheck]
pub fn vcheck_vec_clone(v: Vec<u32>) -> (ret: bool)
    ensures
        ret,
{
    let c = <Vec<u32> as Clone>::clone(&v);
    c.len() == v.len() && (0..v.len()).all(|i| c[i] == v[i])
}

/// `Index` on Vec by usize and by ranges agrees with slice indexing when it returns
#[cfg(not(any(verus_verify_core, verus_keep_ghost)))]
#[verifier::external_body]
#[vcheck]
pub fn vcheck_vec_index(v: Vec<u32>, a: u8, b: u8) -> (ret: bool)
    ensures
        ret,
{
    let len = v.len();
    if len == 0 {
        return true;  // precondition excluded
    }
    let i = (a as usize) % len;
    let (lo, hi) = {
        let x = (a as usize) % (len + 1);
        let y = (b as usize) % (len + 1);
        if x <= y {
            (x, y)
        } else {
            (y, x)
        }
    };
    let e = &v[i];
    let r = &v[lo..hi];
    *e == v.as_slice()[i] && r == &v.as_slice()[lo..hi] && r.len() == hi - lo
}

/// `into_iter` on Vec and &Vec yields the elements in order
#[cfg(not(any(verus_verify_core, verus_keep_ghost)))]
#[verifier::external_body]
#[vcheck]
pub fn vcheck_vec_into_iter(v: Vec<u32>) -> (ret: bool)
    ensures
        ret,
{
    let by_ref: Vec<u32> = (&v).into_iter().copied().collect();
    let owned: Vec<u32> = v.clone().into_iter().collect();
    by_ref == v && owned == v
}

/// `vec_index_mut` returns the element and writes flow back into the vector
#[cfg(not(any(verus_verify_core, verus_keep_ghost)))]
#[verifier::external_body]
#[vcheck]
pub fn vcheck_vec_index_mut(v: Vec<u32>, i: u8, w: u32) -> (ret: bool)
    ensures
        ret,
{
    if v.is_empty() {
        return true;  // precondition excluded
    }
    let i = (i as usize) % v.len();
    let mut v2 = v.clone();
    let e = vec_index_mut(&mut v2, i);
    let ok = *e == v[i];
    *e = w;
    let mut exp = v.clone();
    exp[i] = w;
    ok && v2 == exp && v2[i] == w
}

} // verus!
