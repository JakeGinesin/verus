/// This code adds specifications for the standard-library type
/// `std::collections::VecDeque`.
use super::super::prelude::*;
// PBT in-place patch: iter/core spec-trait machinery stays ghost-gated
// (same pattern as vec.rs).
#[cfg(verus_keep_ghost)]
use super::iter::IteratorSpec;

use alloc::collections::vec_deque::Iter;
use alloc::collections::vec_deque::VecDeque;
use core::alloc::Allocator;
use core::clone::Clone;
use core::ops::{Index, IndexMut};
use core::option::Option;
use core::option::Option::None;

verus! {

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::accept_recursive_types(T)]
#[verifier::reject_recursive_types(A)]
pub struct ExVecDeque<T, A: Allocator>(VecDeque<T, A>);

impl<T, A: Allocator> View for VecDeque<T, A> {
    type V = Seq<T>;

    uninterp spec fn view(&self) -> Seq<T>;
}

impl<T: DeepView, A: Allocator> DeepView for VecDeque<T, A> {
    type V = Seq<T::V>;

    open spec fn deep_view(&self) -> Seq<T::V> {
        let v = self.view();
        Seq::new(v.len(), |i: int| v[i].deep_view())
    }
}

pub trait VecDequeAdditionalSpecFns<T>: View<V = Seq<T>> {
    spec fn spec_index(&self, i: int) -> T
        recommends
            0 <= i < self.view().len(),
    ;
}

impl<T, A: Allocator> VecDequeAdditionalSpecFns<T> for VecDeque<T, A> {
    #[verifier::inline]
    open spec fn spec_index(&self, i: int) -> T {
        self.view().index(i)
    }
}

////// Len (with autospec)
pub uninterp spec fn spec_vec_dequeue_len<T, A: Allocator>(v: &VecDeque<T, A>) -> usize;

// This axiom is slightly better than defining spec_vec_dequeue_len to just be `v@.len() as usize`
// (the axiom also shows that v@.len() is in-bounds for usize)
pub broadcast proof fn axiom_spec_len<T, A: Allocator>(v: &VecDeque<T, A>)
    ensures
        #[trigger] spec_vec_dequeue_len(v) == v@.len(),
{
    admit();
}

#[cfg(verus_keep_ghost)]
impl<T, A: Allocator> super::core::IndexSpecImpl<usize> for VecDeque<T, A> {
    open spec fn index_req(&self, index: &usize) -> bool {
        *index < self.len()
    }
}

pub assume_specification<T, A: Allocator>[ VecDeque::<T, A>::index ](
    v: &VecDeque<T, A>,
    i: usize,
) -> (output: &T)
    ensures
        output == v.spec_index(i as int),
;

pub assume_specification<T, A: Allocator>[ VecDeque::<T, A>::index_mut ](
    v: &mut VecDeque<T, A>,
    i: usize,
) -> (output: &mut T)
    ensures
        *output == old(v).spec_index(i as int),
        final(v)@ == old(v)@.update(i as int, *final(output)),
;

#[verifier::when_used_as_spec(spec_vec_dequeue_len)]
pub assume_specification<T, A: Allocator>[ VecDeque::<T, A>::len ](v: &VecDeque<T, A>) -> (len:
    usize)
    ensures
        len == spec_vec_dequeue_len(v),
;

#[pbt(T = u32)]
pub assume_specification<T>[ VecDeque::<T>::new ]() -> (v: VecDeque<T>)
    ensures
        v@ == Seq::<T>::empty(),
;

// PBT wrapper: `spec_vec_dequeue_len` is uninterp; this checks the
// composite claim with `axiom_spec_len` above (`len == v@.len()`).
#[cfg(not(verus_verify_core))]
#[verifier::external_body]
#[pbt]
pub fn pbt_vecdeque_len(v: VecDeque<u32>) -> (len: usize)
    ensures
        len == v@.len(),
{
    VecDeque::<u32>::len(&v)
}

// Bounded-size wrappers for the allocation-hazard family (u16 domain;
// see vec.rs `pbt_*_bounded` for rationale).
#[cfg(not(verus_verify_core))]
#[verifier::external_body]
#[pbt]
pub fn pbt_vecdeque_with_capacity_bounded(capacity: u16) -> (v: VecDeque<u32>)
    ensures
        v@ == Seq::<u32>::empty(),
{
    VecDeque::<u32>::with_capacity(capacity as usize)
}

#[cfg(not(verus_verify_core))]
#[verifier::external_body]
#[pbt]
pub fn pbt_vecdeque_reserve_bounded(v: &mut VecDeque<u32>, additional: u16)
    ensures
        final(v)@ == old(v)@,
{
    VecDeque::<u32>::reserve(v, additional as usize)
}

/// `VecDeque::resize` over the bounded (u16) size domain.
#[cfg(not(verus_verify_core))]
#[verifier::external_body]
#[pbt]
pub fn pbt_vecdeque_resize_bounded(v: VecDeque<u32>, n: u16, value: u32) -> (ret: bool)
    ensures
        ret,
{
    let mut r = v.clone();
    r.resize(n as usize, value);
    let n = n as usize;
    let keep = n.min(v.len());
    r.len() == n && (0..keep).all(|i| r[i] == v[i]) && (keep..n).all(|i| r[i] == value)
}

/// `VecDeque::index` (guarded element read; direct #[pbt] blocked: the
/// `i < len` precondition lives implicitly in the IndexSpec trait's
/// `index_req`, so an unguarded harness would panic on out-of-bounds).
#[cfg(not(verus_verify_core))]
#[verifier::external_body]
#[pbt]
pub fn pbt_vecdeque_index(v: VecDeque<u32>, i: u16) -> (ret: bool)
    ensures
        ret,
{
    if (i as usize) < v.len() {
        let by_index = v[i as usize];
        let by_iter = *v.iter().nth(i as usize).unwrap();
        by_index == by_iter
    } else {
        true  // precondition excluded
    }
}

#[pbt(T = u32)]
pub assume_specification<T>[ <VecDeque<T> as core::default::Default>::default ]() -> (v: VecDeque<
    T,
>)
    ensures
        v@ == Seq::<T>::empty(),
;

// (no #[pbt] directly on with_capacity / reserve: allocation-abort
// hazard on edge-biased usize samples; the `pbt_*_bounded` wrappers
// below cover a u16-bounded size domain, same pattern as vec.rs.)
pub assume_specification<T>[ VecDeque::<T>::with_capacity ](capacity: usize) -> (v: VecDeque<T>)
    ensures
        v@ == Seq::<T>::empty(),
;

pub assume_specification<T, A: Allocator>[ VecDeque::<T, A>::reserve ](
    v: &mut VecDeque<T, A>,
    additional: usize,
)
    ensures
        final(v)@ == old(v)@,
;

#[pbt(T = u32, A = alloc::alloc::Global)]
pub assume_specification<T, A: Allocator>[ VecDeque::<T, A>::push_back ](
    v: &mut VecDeque<T, A>,
    value: T,
)
    ensures
        final(v)@ == old(v)@.push(value),
;

#[pbt(T = u32, A = alloc::alloc::Global)]
pub assume_specification<T, A: Allocator>[ VecDeque::<T, A>::push_front ](
    v: &mut VecDeque<T, A>,
    value: T,
)
    ensures
        final(v)@ == seq![value] + old(v)@,
;

#[pbt(T = u32, A = alloc::alloc::Global)]
pub assume_specification<T, A: Allocator>[ VecDeque::<T, A>::pop_back ](
    v: &mut VecDeque<T, A>,
) -> (value: Option<T>)
    ensures
        match value {
            Some(x) => {
                &&& old(v)@.len() > 0
                &&& x == old(v)@[old(v)@.len() - 1]
                &&& final(v)@ == old(v)@.subrange(0, old(v)@.len() as int - 1)
            },
            None => {
                &&& old(v)@.len() == 0
                &&& final(v)@ == old(v)@
            },
        },
;

#[pbt(T = u32, A = alloc::alloc::Global)]
pub assume_specification<T, A: Allocator>[ VecDeque::<T, A>::pop_front ](
    v: &mut VecDeque<T, A>,
) -> (value: Option<T>)
    ensures
        match value {
            Some(x) => {
                &&& old(v)@.len() > 0
                &&& x == old(v)@[0]
                &&& final(v)@ == old(v)@.subrange(1, old(v)@.len() as int)
            },
            None => {
                &&& old(v)@.len() == 0
                &&& final(v)@ == old(v)@
            },
        },
;

#[pbt(T = u32, A = alloc::alloc::Global)]
pub assume_specification<T, A: Allocator>[ VecDeque::<T, A>::append ](
    v: &mut VecDeque<T, A>,
    other: &mut VecDeque<T, A>,
)
    ensures
        final(v)@ == old(v)@ + old(other)@,
        final(other)@ == Seq::<T>::empty(),
;

#[pbt(T = u32, A = alloc::alloc::Global)]
pub assume_specification<T, A: Allocator>[ VecDeque::<T, A>::insert ](
    v: &mut VecDeque<T, A>,
    i: usize,
    element: T,
)
    requires
        i <= old(v).len(),
    ensures
        final(v)@ == old(v)@.insert(i as int, element),
;

#[pbt(T = u32, A = alloc::alloc::Global)]
pub assume_specification<T, A: Allocator>[ VecDeque::<T, A>::remove ](
    v: &mut VecDeque<T, A>,
    i: usize,
) -> (element: Option<T>)
    ensures
        match element {
            Some(x) => {
                &&& i < old(v)@.len()
                &&& x == old(v)@[i as int]
                &&& final(v)@ == old(v)@.remove(i as int)
            },
            None => {
                &&& old(v)@.len() <= i
                &&& final(v)@ == old(v)@
            },
        },
;

#[pbt(T = u32, A = alloc::alloc::Global)]
pub assume_specification<T, A: Allocator>[ VecDeque::<T, A>::clear ](v: &mut VecDeque<T, A>)
    ensures
        final(v).view() == Seq::<T>::empty(),
;

#[pbt(T = u32, A = alloc::alloc::Global)]
pub assume_specification<T, A: Allocator + core::clone::Clone>[ VecDeque::<T, A>::split_off ](
    v: &mut VecDeque<T, A>,
    at: usize,
) -> (return_value: VecDeque<T, A>)
    requires
        at <= old(v)@.len(),
    ensures
        final(v)@ == old(v)@.subrange(0, at as int),
        return_value@ == old(v)@.subrange(at as int, old(v)@.len() as int),
;

pub open spec fn vec_dequeue_clone_trigger<T, A: Allocator>(
    v1: VecDeque<T, A>,
    v2: VecDeque<T, A>,
) -> bool {
    true
}

pub assume_specification<T: Clone, A: Allocator + Clone>[ <VecDeque<T, A> as Clone>::clone ](
    v: &VecDeque<T, A>,
) -> (res: VecDeque<T, A>)
    ensures
        res.len() == v.len(),
        forall|i| #![all_triggers] 0 <= i < v.len() ==> cloned::<T>(v[i], res[i]),
        vec_dequeue_clone_trigger(*v, res),
        v@ =~= res@ ==> v@ == res@,
;

#[pbt(T = u32, A = alloc::alloc::Global)]
pub assume_specification<T, A: Allocator>[ VecDeque::<T, A>::truncate ](
    v: &mut VecDeque<T, A>,
    len: usize,
)
    ensures
        len <= old(v).len() ==> final(v)@ == old(v)@.subrange(0, len as int),
        len > old(v).len() ==> final(v)@ == old(v)@,
;

pub assume_specification<T: Clone, A: Allocator>[ VecDeque::<T, A>::resize ](
    v: &mut VecDeque<T, A>,
    len: usize,
    value: T,
)
    ensures
        len <= old(v).len() ==> final(v)@ == old(v)@.subrange(0, len as int),
        len > old(v).len() ==> {
            &&& final(v)@.len() == len
            &&& final(v)@.subrange(0, old(v).len() as int) == old(v)@
            &&& forall|i|
                #![all_triggers]
                old(v).len() <= i < len ==> cloned::<T>(value, final(v)@[i])
        },
;

pub broadcast proof fn axiom_vec_dequeue_index_decreases<A>(v: VecDeque<A>, i: int)
    requires
        0 <= i < v.len(),
    ensures
        #[trigger] (decreases_to!(v => v[i])),
{
    admit();
}

// The `iter` method of a `VecDeque` returns an iterator of type `Iter`,
// so we specify that type here.
#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::accept_recursive_types(T)]
pub struct ExIter<'a, T: 'a>(Iter<'a, T>);

// To allow reasoning about the "contents" of the VecDeque iterator, without using
// a prophecy, we need a function that gives us the underlying sequence of the original vec.
pub uninterp spec fn into_iter_elts<'a, T: 'a>(i: Iter<'a, T>) -> Seq<&'a T>;

#[cfg(verus_keep_ghost)]
impl<'a, T: 'a> super::iter::IteratorSpecImpl for Iter<'a, T> {
    open spec fn obeys_prophetic_iter_laws(&self) -> bool {
        true
    }

    uninterp spec fn remaining(&self) -> Seq<Self::Item>;

    uninterp spec fn will_return_none(&self) -> bool;

    #[verifier::prophetic]
    open spec fn initial_value_relation(&self, init: &Self) -> bool {
        &&& IteratorSpec::remaining(init) == IteratorSpec::remaining(self)
        &&& into_iter_elts(*self) == IteratorSpec::remaining(self)
    }

    uninterp spec fn decrease(&self) -> Option<nat>;

    open spec fn peek(&self, index: int) -> Option<Self::Item> {
        if 0 <= index < into_iter_elts(*self).len() {
            Some(&into_iter_elts(*self)[index])
        } else {
            None
        }
    }
}

#[cfg(verus_keep_ghost)]
impl<'a, T: 'a> super::iter::DoubleEndedIteratorSpecImpl for Iter<'a, T> {
    open spec fn peek_back(&self, index: int) -> Option<Self::Item> {
        if 0 <= index < into_iter_elts(*self).len() {
            Some(&into_iter_elts(*self)[into_iter_elts(*self).len() - index - 1])
        } else {
            None
        }
    }
}

// To allow reasoning about the ghost iterator when the executable
// function `iter()` is invoked in a `for` loop header (e.g., in
// `for x in it: v.iter() { ... }`), we need to specify the behavior of
// the iterator in spec mode. To do that, we add
// `#[verifier::when_used_as_spec(spec_iter)` to the specification for
// the executable `iter` method and define that spec function here.
pub uninterp spec fn spec_iter<'a, T, A: Allocator>(v: &'a VecDeque<T, A>) -> (r: Iter<'a, T>);

pub broadcast proof fn axiom_spec_iter<'a, T, A: Allocator>(v: &'a VecDeque<T, A>)
    ensures
        #[trigger] spec_iter(v).remaining() == v@.as_ref(),
{
    admit();
}

#[verifier::when_used_as_spec(spec_iter)]
pub assume_specification<'a, T, A: Allocator>[ VecDeque::<T, A>::iter ](
    v: &'a VecDeque<T, A>,
) -> (iter: Iter<'a, T>)
    ensures
        iter == spec_iter(v),
        IteratorSpec::decrease(&iter) is Some,
        IteratorSpec::initial_value_relation(&iter, &iter),
;

pub broadcast group group_vec_dequeue_axioms {
    axiom_spec_len,
    axiom_vec_dequeue_index_decreases,
    axiom_spec_iter,
}

} // verus!
