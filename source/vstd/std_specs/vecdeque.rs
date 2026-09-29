/// This code adds specifications for the standard-library type
/// `std::collections::VecDeque`.
use super::super::prelude::*;
// iter/core spec-trait machinery stays ghost-gated (same pattern as vec.rs)
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

#[vcheck(T = u32)]
#[vcheck(T = ())]
pub assume_specification<T>[ VecDeque::<T>::new ]() -> (v: VecDeque<T>)
    ensures
        v@ == Seq::<T>::empty(),
;

// vcheck wrapper: `spec_vec_dequeue_len` is uninterp
#[cfg(not(any(verus_verify_core, verus_keep_ghost)))]
#[verifier::external_body]
#[vcheck]
pub fn vcheck_vecdeque_len(v: VecDeque<u32>) -> (len: usize)
    ensures
        len == v@.len(),
{
    VecDeque::<u32>::len(&v)
}

// Bounded-size wrappers for the allocation-hazard family
#[cfg(not(any(verus_verify_core, verus_keep_ghost)))]
#[verifier::external_body]
#[vcheck]
pub fn vcheck_vecdeque_with_capacity_bounded(capacity: u16) -> (v: VecDeque<u32>)
    ensures
        v@ == Seq::<u32>::empty(),
{
    VecDeque::<u32>::with_capacity(capacity as usize)
}

#[cfg(not(any(verus_verify_core, verus_keep_ghost)))]
#[verifier::external_body]
#[vcheck]
pub fn vcheck_vecdeque_reserve_bounded(v: &mut VecDeque<u32>, additional: u16)
    ensures
        final(v)@ == old(v)@,
{
    VecDeque::<u32>::reserve(v, additional as usize)
}

/// `VecDeque::resize` over the bounded (u16) size domain
#[cfg(not(any(verus_verify_core, verus_keep_ghost)))]
#[verifier::external_body]
#[vcheck]
pub fn vcheck_vecdeque_resize_bounded(v: VecDeque<u32>, n: u16, value: u32) -> (ret: bool)
    ensures
        ret,
{
    let mut r = v.clone();
    r.resize(n as usize, value);
    let n = n as usize;
    let keep = n.min(v.len());
    r.len() == n && (0..keep).all(|i| r[i] == v[i]) && (keep..n).all(|i| r[i] == value)
}

/// `VecDeque::index`
#[cfg(not(any(verus_verify_core, verus_keep_ghost)))]
#[verifier::external_body]
#[vcheck]
pub fn vcheck_vecdeque_index(v: VecDeque<u32>, i: u16) -> (ret: bool)
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

#[vcheck(T = u32)]
#[vcheck(T = ())]
pub assume_specification<T>[ <VecDeque<T> as core::default::Default>::default ]() -> (v: VecDeque<
    T,
>)
    ensures
        v@ == Seq::<T>::empty(),
;

// (no vcheck directly on with_capacity / reserve)
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

#[vcheck(T = u32, A = alloc::alloc::Global)]
#[vcheck(T = (), A = alloc::alloc::Global)]
pub assume_specification<T, A: Allocator>[ VecDeque::<T, A>::push_back ](
    v: &mut VecDeque<T, A>,
    value: T,
)
    ensures
        final(v)@ == old(v)@.push(value),
;

#[vcheck(T = u32, A = alloc::alloc::Global)]
#[vcheck(T = (), A = alloc::alloc::Global)]
pub assume_specification<T, A: Allocator>[ VecDeque::<T, A>::push_front ](
    v: &mut VecDeque<T, A>,
    value: T,
)
    ensures
        final(v)@ == seq![value] + old(v)@,
;

#[vcheck(T = u32, A = alloc::alloc::Global)]
pub assume_specification<T, A: Allocator>[ VecDeque::<T, A>::pop_back ](
    v: &mut VecDeque<T, A>,
) -> (value: Option<T>)
    ensures
        match value {
            Some(x) => {
                &&& old(v)@.len() > 0
                &&& x == old(v)@[old(v)@.len() - 1]
                &&& final(v)@ == old(v)@.take(old(v)@.len() - 1)
            },
            None => {
                &&& old(v)@.len() == 0
                &&& final(v)@ == old(v)@
            },
        },
;

#[vcheck(T = u32, A = alloc::alloc::Global)]
pub assume_specification<T, A: Allocator>[ VecDeque::<T, A>::pop_front ](
    v: &mut VecDeque<T, A>,
) -> (value: Option<T>)
    ensures
        match value {
            Some(x) => {
                &&& old(v)@.len() > 0
                &&& x == old(v)@[0]
                &&& final(v)@ == old(v)@.skip(1)
            },
            None => {
                &&& old(v)@.len() == 0
                &&& final(v)@ == old(v)@
            },
        },
;

#[vcheck(T = u32, A = alloc::alloc::Global)]
#[vcheck(T = (), A = alloc::alloc::Global)]
pub assume_specification<T, A: Allocator>[ VecDeque::<T, A>::append ](
    v: &mut VecDeque<T, A>,
    other: &mut VecDeque<T, A>,
)
    ensures
        final(v)@ == old(v)@ + old(other)@,
        final(other)@ == Seq::<T>::empty(),
;

#[vcheck(T = u32, A = alloc::alloc::Global)]
#[vcheck(T = (), A = alloc::alloc::Global)]
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

#[vcheck(T = u32, A = alloc::alloc::Global)]
#[vcheck(T = (), A = alloc::alloc::Global)]
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

#[vcheck(T = u32, A = alloc::alloc::Global)]
#[vcheck(T = (), A = alloc::alloc::Global)]
pub assume_specification<T, A: Allocator>[ VecDeque::<T, A>::clear ](v: &mut VecDeque<T, A>)
    ensures
        final(v).view() == Seq::<T>::empty(),
;

#[vcheck(T = u32, A = alloc::alloc::Global)]
pub assume_specification<T, A: Allocator + core::clone::Clone>[ VecDeque::<T, A>::split_off ](
    v: &mut VecDeque<T, A>,
    at: usize,
) -> (return_value: VecDeque<T, A>)
    requires
        at <= old(v)@.len(),
    ensures
        final(v)@ == old(v)@.take(at as int),
        return_value@ == old(v)@.skip(at as int),
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

#[vcheck(T = u32, A = alloc::alloc::Global)]
pub assume_specification<T, A: Allocator>[ VecDeque::<T, A>::truncate ](
    v: &mut VecDeque<T, A>,
    len: usize,
)
    ensures
        len <= old(v).len() ==> final(v)@ == old(v)@.take(len as int),
        len > old(v).len() ==> final(v)@ == old(v)@,
;

pub assume_specification<T: Clone, A: Allocator>[ VecDeque::<T, A>::resize ](
    v: &mut VecDeque<T, A>,
    len: usize,
    value: T,
)
    ensures
        len <= old(v).len() ==> final(v)@ == old(v)@[..len],
        len > old(v).len() ==> {
            &&& final(v)@.len() == len
            &&& final(v)@[..old(v).len()] == old(v)@
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

pub assume_specification<'a, T, A: Allocator>[ VecDeque::<T, A>::iter ](
    v: &'a VecDeque<T, A>,
) -> (iter: Iter<'a, T>)
    ensures
        IteratorSpec::remaining(&iter) == v@.as_ref(),
        into_iter_elts(iter) == IteratorSpec::remaining(&iter),
        IteratorSpec::decrease(&iter) is Some,
;

pub broadcast group group_vec_dequeue_axioms {
    axiom_spec_len,
    axiom_vec_dequeue_index_decreases,
}

} // verus!

verus! {

/// `index` / `index_mut` / `iter` / `clone` on a wrapped ring buffer match the logical sequence
#[cfg(not(any(verus_verify_core, verus_keep_ghost)))]
#[verifier::external_body]
#[vcheck]
pub fn vcheck_vecdeque_ring_ops(front: Vec<u32>, back: Vec<u32>, pops: u8, i: u8, w: u32) -> (ret: bool)
    ensures
        ret,
{
    let mut d: VecDeque<u32> = VecDeque::with_capacity(4);
    let mut model: Vec<u32> = Vec::new();
    for x in back.iter() {
        d.push_back(*x);
        model.push(*x);
    }
    for _ in 0..(pops as usize % (model.len() + 1)) {
        d.pop_front();
        model.remove(0);
    }
    for x in front.iter() {
        d.push_front(*x);
        model.insert(0, *x);
    }
    let iter_ok = d.iter().copied().collect::<Vec<u32>>() == model;
    let c = <VecDeque<u32> as Clone>::clone(&d);
    let clone_ok = c.len() == d.len() && (0..d.len()).all(|k| c[k] == d[k]);
    if model.is_empty() {
        return iter_ok && clone_ok;
    }
    let k = (i as usize) % model.len();
    let idx_ok = d[k] == model[k];
    let r = &mut d[k];
    let mut_ok = *r == model[k];
    *r = w;
    model[k] = w;
    iter_ok && clone_ok && idx_ok && mut_ok && d.iter().copied().collect::<Vec<u32>>() == model
}

} // verus!
