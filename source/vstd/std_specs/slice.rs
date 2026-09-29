use super::super::prelude::*;
// spec-trait machinery only exists in verifier builds
#[cfg(verus_keep_ghost)]
use super::super::slice::SliceIndexSpec;
#[cfg(verus_keep_ghost)]
use super::core::IndexSpec;
#[cfg(verus_keep_ghost)]
use super::iter::IteratorSpec;
#[cfg(verus_keep_ghost)]
use super::range::{
    ExRange, RangeBoundsSpec, slice_range_end, slice_range_start, slice_range_valid,
};

use core::ops::{
    Index, IndexMut, Range, RangeFrom, RangeFull, RangeInclusive, RangeTo, RangeToInclusive,
};
use core::slice::{Iter, IterMut, SliceIndex};

use verus as verus_skip_verusfmt;
verus_skip_verusfmt! {

#[cfg(verus_keep_ghost)]
impl<T> super::super::slice::SliceIndexSpecImpl<[T]> for usize {
    open spec fn in_bounds(&self, slice: &[T]) -> bool {
        *self < slice@.len()
    }

    open spec fn index_postcondition(&self, slice: &[T], r: &T) -> bool {
        r == slice@[self as int]
    }

    open spec fn index_mut_postcondition(
        &self,
        old_slice: &[T],
        final_slice: &[T],
        immediate_output: &T,
        final_output: &T,
    ) -> bool {
        &&& *immediate_output == old_slice@[*self as int]
        &&& final_slice@ == old_slice@.update(*self as int, *final_output)
    }
}

pub assume_specification<T>[ <usize as SliceIndex<[T]>>::get ](i: usize, slice: &[T]) -> Option<&T>;

pub assume_specification<T>[ <usize as SliceIndex<[T]>>::index ](i: usize, slice: &[T]) -> &T
;

pub assume_specification<T>[ <usize as SliceIndex<[T]>>::get_mut ](i: usize, slice: &mut [T]) -> Option<&mut T>;

pub assume_specification<T>[ <usize as SliceIndex<[T]>>::index_mut ](i: usize, slice: &mut [T]) -> (output: &mut T)
;

pub open spec fn generic_slice_in_bounds<R: RangeBoundsSpec<usize>, T>(
    range: &R,
    s: Seq<T>
) -> bool {
    slice_range_valid(range, s.len())
}

pub open spec fn generic_slice_index_postcondition<R: RangeBoundsSpec<usize>, T>(
    range: &R,
    slice: Seq<T>,
    r: Seq<T>,
) -> bool {
    r == slice[slice_range_start(range)..slice_range_end(range, slice.len())]
}

pub open spec fn generic_slice_index_mut_postcondition<R: RangeBoundsSpec<usize>, T>(
    range: &R,
    old_slice: Seq<T>,
    final_slice: Seq<T>,
    immediate_output: Seq<T>,
    final_output: Seq<T>,
) -> bool {
    &&& immediate_output == old_slice[slice_range_start(range)..slice_range_end(range, old_slice.len())]
    &&& final_slice.len() == old_slice.len()
    &&& final_slice[..slice_range_start(range)] == old_slice[..slice_range_start(range)]
    &&& final_slice[slice_range_start(range)..slice_range_end(range, old_slice.len())] == final_output
    &&& final_slice[slice_range_end(range, old_slice.len())..old_slice.len()] ==
        old_slice[slice_range_end(range, old_slice.len())..old_slice.len()]
    // The following conjunct can be derived from the above four, but
    // it's useful to include anyway.
    &&& final_slice == old_slice[..slice_range_start(range)] + final_output + old_slice[
           slice_range_end(range, old_slice.len())..old_slice.len()]
}

#[cfg(verus_keep_ghost)]
impl<T> super::super::slice::SliceIndexSpecImpl<[T]> for Range<usize> {
    open spec fn in_bounds(&self, slice: &[T]) -> bool {
        generic_slice_in_bounds(self, slice@)
    }

    open spec fn index_postcondition(&self, slice: &[T], r: &[T]) -> bool {
        generic_slice_index_postcondition(self, slice@, r@)
    }

    open spec fn index_mut_postcondition(
        &self,
        old_slice: &[T],
        final_slice: &[T],
        immediate_output: &[T],
        final_output: &[T]
    ) -> bool {
        generic_slice_index_mut_postcondition(self, old_slice@, final_slice@, immediate_output@, final_output@)
    }
}

pub assume_specification<T>[ <Range<usize> as SliceIndex<[T]>>::get ](i: Range<usize>, slice: &[T]) -> Option<&[T]>;

pub assume_specification<T>[ <Range<usize> as SliceIndex<[T]>>::index ](i: Range<usize>, slice: &[T]) -> (r: &[T])
;

pub assume_specification<T>[ <Range<usize> as SliceIndex<[T]>>::get_mut ](i: Range<usize>, slice: &mut [T]) -> Option<&mut [T]>;

pub assume_specification<T>[ <Range<usize> as SliceIndex<[T]>>::index_mut ](i: Range<usize>, slice: &mut [T]) -> (r: &mut [T])
;

impl<T> super::super::slice::SliceIndexSpecImpl<[T]> for RangeTo<usize> {
    open spec fn in_bounds(&self, slice: &[T]) -> bool {
        generic_slice_in_bounds(self, slice@)
    }

    open spec fn index_postcondition(&self, slice: &[T], r: &[T]) -> bool {
        generic_slice_index_postcondition(self, slice@, r@)
    }

    open spec fn index_mut_postcondition(
        &self,
        old_slice: &[T],
        final_slice: &[T],
        immediate_output: &[T],
        final_output: &[T]
    ) -> bool {
        generic_slice_index_mut_postcondition(self, old_slice@, final_slice@, immediate_output@, final_output@)
    }
}

pub assume_specification<T>[ <RangeTo<usize> as SliceIndex<[T]>>::get ](i: RangeTo<usize>, slice: &[T]) -> Option<&[T]>;

pub assume_specification<T>[ <RangeTo<usize> as SliceIndex<[T]>>::index ](i: RangeTo<usize>, slice: &[T]) -> (r: &[T])
;

pub assume_specification<T>[ <RangeTo<usize> as SliceIndex<[T]>>::get_mut ](i: RangeTo<usize>, slice: &mut [T]) -> Option<&mut [T]>;

pub assume_specification<T>[ <RangeTo<usize> as SliceIndex<[T]>>::index_mut ](i: RangeTo<usize>, slice: &mut [T]) -> (r: &mut [T])
;

impl<T> super::super::slice::SliceIndexSpecImpl<[T]> for RangeFrom<usize> {
    open spec fn in_bounds(&self, slice: &[T]) -> bool {
        generic_slice_in_bounds(self, slice@)
    }

    open spec fn index_postcondition(&self, slice: &[T], r: &[T]) -> bool {
        generic_slice_index_postcondition(self, slice@, r@)
    }

    open spec fn index_mut_postcondition(
        &self,
        old_slice: &[T],
        final_slice: &[T],
        immediate_output: &[T],
        final_output: &[T]
    ) -> bool {
        generic_slice_index_mut_postcondition(self, old_slice@, final_slice@, immediate_output@, final_output@)
    }
}

pub assume_specification<T>[ <RangeFrom<usize> as SliceIndex<[T]>>::get ](i: RangeFrom<usize>, slice: &[T]) -> Option<&[T]>;

pub assume_specification<T>[ <RangeFrom<usize> as SliceIndex<[T]>>::index ](i: RangeFrom<usize>, slice: &[T]) -> (r: &[T])
;

pub assume_specification<T>[ <RangeFrom<usize> as SliceIndex<[T]>>::get_mut ](i: RangeFrom<usize>, slice: &mut [T]) -> Option<&mut [T]>;

pub assume_specification<T>[ <RangeFrom<usize> as SliceIndex<[T]>>::index_mut ](i: RangeFrom<usize>, slice: &mut [T]) -> (r: &mut [T])
;

impl<T> super::super::slice::SliceIndexSpecImpl<[T]> for RangeToInclusive<usize> {
    open spec fn in_bounds(&self, slice: &[T]) -> bool {
        generic_slice_in_bounds(self, slice@)
    }

    open spec fn index_postcondition(&self, slice: &[T], r: &[T]) -> bool {
        generic_slice_index_postcondition(self, slice@, r@)
    }

    open spec fn index_mut_postcondition(
        &self,
        old_slice: &[T],
        final_slice: &[T],
        immediate_output: &[T],
        final_output: &[T]
    ) -> bool {
        generic_slice_index_mut_postcondition(self, old_slice@, final_slice@, immediate_output@, final_output@)
    }
}

pub assume_specification<T>[ <RangeToInclusive<usize> as SliceIndex<[T]>>::get ](i: RangeToInclusive<usize>, slice: &[T]) -> Option<&[T]>;

pub assume_specification<T>[ <RangeToInclusive<usize> as SliceIndex<[T]>>::index ](i: RangeToInclusive<usize>, slice: &[T]) -> (r: &[T])
;

pub assume_specification<T>[ <RangeToInclusive<usize> as SliceIndex<[T]>>::get_mut ](i: RangeToInclusive<usize>, slice: &mut [T]) -> Option<&mut [T]>;

pub assume_specification<T>[ <RangeToInclusive<usize> as SliceIndex<[T]>>::index_mut ](i: RangeToInclusive<usize>, slice: &mut [T]) -> (r: &mut [T])
;

impl<T> super::super::slice::SliceIndexSpecImpl<[T]> for RangeFull {
    open spec fn in_bounds(&self, slice: &[T]) -> bool {
        generic_slice_in_bounds(self, slice@)
    }

    open spec fn index_postcondition(&self, slice: &[T], r: &[T]) -> bool {
        generic_slice_index_postcondition(self, slice@, r@)
    }

    open spec fn index_mut_postcondition(
        &self,
        old_slice: &[T],
        final_slice: &[T],
        immediate_output: &[T],
        final_output: &[T]
    ) -> bool {
        generic_slice_index_mut_postcondition(self, old_slice@, final_slice@, immediate_output@, final_output@)
    }
}

pub assume_specification<T>[ <RangeFull as SliceIndex<[T]>>::get ](i: RangeFull, slice: &[T]) -> Option<&[T]>;

pub assume_specification<T>[ <RangeFull as SliceIndex<[T]>>::index ](i: RangeFull, slice: &[T]) -> (r: &[T])
;

pub assume_specification<T>[ <RangeFull as SliceIndex<[T]>>::get_mut ](i: RangeFull, slice: &mut [T]) -> Option<&mut [T]>;

pub assume_specification<T>[ <RangeFull as SliceIndex<[T]>>::index_mut ](i: RangeFull, slice: &mut [T]) -> (r: &mut [T])
;

impl<T> super::super::slice::SliceIndexSpecImpl<[T]> for RangeInclusive<usize> {
    open spec fn in_bounds(&self, slice: &[T]) -> bool {
        generic_slice_in_bounds(self, slice@)
    }

    open spec fn index_postcondition(&self, slice: &[T], r: &[T]) -> bool {
        generic_slice_index_postcondition(self, slice@, r@)
    }

    open spec fn index_mut_postcondition(
        &self,
        old_slice: &[T],
        final_slice: &[T],
        immediate_output: &[T],
        final_output: &[T]
    ) -> bool {
        generic_slice_index_mut_postcondition(self, old_slice@, final_slice@, immediate_output@, final_output@)
    }
}

pub assume_specification<T>[ <RangeInclusive<usize> as SliceIndex<[T]>>::get ](i: RangeInclusive<usize>, slice: &[T]) -> Option<&[T]>;

pub assume_specification<T>[ <RangeInclusive<usize> as SliceIndex<[T]>>::index ](i: RangeInclusive<usize>, slice: &[T]) -> (r: &[T])
;

pub assume_specification<T>[ <RangeInclusive<usize> as SliceIndex<[T]>>::get_mut ](i: RangeInclusive<usize>, slice: &mut [T]) -> Option<&mut [T]>;

pub assume_specification<T>[ <RangeInclusive<usize> as SliceIndex<[T]>>::index_mut ](i: RangeInclusive<usize>, slice: &mut [T]) -> (r: &mut [T])
;

// starts_with
pub open spec fn spec_slice_starts_with<T: PartialEq>(slice: &[T], needle: &[T]) -> bool {
    &&& needle@.len() <= slice@.len()
    &&& forall|i: int| #![auto]
        0 <= i < needle@.len() ==>
            <T as super::cmp::PartialEqSpec<T>>::eq_spec(
                &slice@[i],
                &needle@[i],
            )
}

#[verifier::when_used_as_spec(spec_slice_starts_with)]
pub assume_specification<T: PartialEq>[ <[T]>::starts_with ](
    slice: &[T],
    needle: &[T],
) -> (result: bool)
    ensures
        needle@.len() > slice@.len() ==> !result,
        <T as super::cmp::PartialEqSpec<T>>::obeys_eq_spec() ==> (result == spec_slice_starts_with(
            slice,
            needle,
        )),
;

// ends_with
pub open spec fn spec_slice_ends_with<T: PartialEq>(slice: &[T], needle: &[T]) -> bool {
    &&& needle@.len() <= slice@.len()
    &&& forall|i: int| #![auto]
        0 <= i < needle@.len() ==>
            <T as super::cmp::PartialEqSpec<T>>::eq_spec(
                &slice@[slice@.len() - needle@.len() + i],
                &needle@[i],
            )
}

#[verifier::when_used_as_spec(spec_slice_ends_with)]
pub assume_specification<T: PartialEq>[ <[T]>::ends_with ](
    slice: &[T],
    needle: &[T],
) -> (result: bool)
    ensures
        needle@.len() > slice@.len() ==> !result,
        <T as super::cmp::PartialEqSpec<T>>::obeys_eq_spec() ==> (result == spec_slice_ends_with(
            slice,
            needle,
        )),
;

#[cfg(verus_keep_ghost)]
impl<T, I: SliceIndex<[T]>> super::core::IndexSpecImpl<I> for [T] {
    open spec fn index_req(&self, index: &I) -> bool {
        index.in_bounds(self)
    }
}

pub assume_specification<T, I>[ <[T]>::get::<I> ](slice: &[T], i: I) -> (b: Option<
    &<I as SliceIndex<[T]>>::Output,
>) where I: SliceIndex<[T]>
    ensures
        call_ensures(<I as SliceIndex<[T]>>::get, (i, slice), b),
;

pub assume_specification<T, I>[ <[T]>::get_mut::<I> ](slice: &mut [T], i: I) -> (b: Option<
    &mut <I as SliceIndex<[T]>>::Output,
>) where I: SliceIndex<[T]>
    ensures
        call_ensures(<I as SliceIndex<[T]>>::get_mut, (i, slice), b),
;

pub assume_specification<T, I: SliceIndex<[T]>>[ <[T] as Index<I>>::index ](
    slice: &[T],
    index: I,
) -> (output: &<I as SliceIndex<[T]>>::Output)
    ensures
        call_ensures(<I as SliceIndex<[T]>>::index, (index, slice), output),
;

pub assume_specification<T, I: SliceIndex<[T]>>[ <[T] as IndexMut<I>>::index_mut ](
    slice: &mut [T],
    index: I,
) -> (output: &mut <I as SliceIndex<[T]>>::Output)
    ensures
        call_ensures(<I as SliceIndex<[T]>>::index_mut, (index, slice), output),
;

#[cfg(verus_keep_ghost)]
impl<T, I, const N: usize> super::core::IndexSpecImpl<I> for [T; N]
where
    [T]: Index<I>,
{
    open spec fn index_req(&self, index: &I) -> bool {
        <[T] as IndexSpec<I>>::index_req(self, index)
    }
}

pub assume_specification<T, I, const N: usize>[ <[T; N]>::index ](array: &[T; N], index: I) -> (output: &<[T; N] as Index<I>>::Output)
    where
        [T]: Index<I>,
    ensures
        call_ensures(<[T]>::index, (array, index), output),
;

pub assume_specification<T, I, const N: usize>[ <[T; N]>::index_mut ](array: &mut [T; N], index: I) -> (output: &mut <[T; N] as Index<I>>::Output)
    where
        [T]: IndexMut<I>,
    ensures
        exists|slice: &mut [T]| {
            &&& #[trigger] slice@ == old(array)@
            &&& final(slice)@ == final(array)@
            &&& call_ensures(<[T]>::index_mut, (slice, index), output)
        },
;

pub assume_specification[ core::hint::unreachable_unchecked ]() -> !
    requires
        false,
;

// slice == slice
pub assume_specification<T: PartialEq<U>, U>[ <[T] as PartialEq<[U]>>::eq ](
    left: &[T],
    right: &[U],
) -> bool
;

impl<T, U> super::cmp::PartialEqSpecImpl<[U]> for [T] where T: PartialEq<U> + super::cmp::PartialEqSpec<U> {
    open spec fn obeys_eq_spec() -> bool {
        <T as super::cmp::PartialEqSpec<U>>::obeys_eq_spec()
    }

    open spec fn eq_spec(&self, other: &[U]) -> bool {
        &&& self@.len() == other@.len()
        &&& forall|i: int|
            #![auto]
            0 <= i < self@.len() ==> <T as super::cmp::PartialEqSpec<U>>::eq_spec(&self@[i], &other@[i])
    }
}

// The `iter` method of a `<T>` returns an iterator of type `Iter<'_, T>`,
// so we specify that type here.
#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::accept_recursive_types(T)]
pub struct ExIter<'a, T: 'a>(Iter<'a, T>);

// To allow reasoning about the "contents" of the slice iterator, without using
// a prophecy, we need a function that gives us the underlying sequence of the original slice.
pub uninterp spec fn into_iter_elts<'a, T: 'a>(i: Iter<'a, T>) -> Seq<T>;

#[cfg(verus_keep_ghost)]
impl <'a, T: 'a> super::iter::IteratorSpecImpl for Iter<'a, T> {
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

pub assume_specification<'a, T>[ <[T]>::iter ](s: &'a [T]) -> (iter: Iter<'a, T>)
    ensures
        IteratorSpec::remaining(&iter) == s@.as_ref(),
        into_iter_elts(iter) == IteratorSpec::remaining(&iter).unref(),
        IteratorSpec::decrease(&iter) is Some,
;

pub assume_specification<'a, T> [<&'a [T] as core::iter::IntoIterator>::into_iter] (s: &'a [T]) ->
    (iter: Iter<'a, T>)
    ensures
        IteratorSpec::remaining(&iter) == s@.as_ref(),
        into_iter_elts(iter) == IteratorSpec::remaining(&iter).unref(),
        IteratorSpec::decrease(&iter) is Some,
;

/***********************************************************************************************
 * Definitions for `slice::IterMut` (the iterator behind `<[T]>::iter_mut` and `Vec::iter_mut`)
 ***********************************************************************************************/
#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::accept_recursive_types(T)]
pub struct ExIterMut<'a, T: 'a>(IterMut<'a, T>);

// See exampes/iterators/slice_iter_mut.rs for a verified implementation of this interface.
// Any changes here should first be verified over there.
#[cfg(verus_keep_ghost)]
impl<'a, T: 'a> super::iter::IteratorSpecImpl for IterMut<'a, T> {
    open spec fn obeys_prophetic_iter_laws(&self) -> bool {
        true
    }

    #[verifier::prophetic]
    uninterp spec fn remaining(&self) -> Seq<Self::Item>;

    open spec fn will_return_none(&self) -> bool { true }

    uninterp spec fn decrease(&self) -> Option<nat>;

    open spec fn peek(&self, index: int) -> Option<Self::Item> { None }
}

// Also covers `vec.iter_mut(), which reaches this slice fn through `Vec`'s `DerefMut`
pub assume_specification<'a, T>[ <[T]>::iter_mut ](slice: &'a mut [T]) -> (iter: IterMut<'a, T>)
    ensures
        IteratorSpec::remaining(&iter).len() == old(slice)@.len() == final(slice)@.len(),
        // Each yielded reference initially points at the corresponding element...
        forall|i: int| #![trigger IteratorSpec::remaining(&iter)[i]]
            0 <= i < old(slice)@.len() ==> *(IteratorSpec::remaining(&iter)[i]) == old(slice)@[i],
        // ...and its eventual value flows back to the corresponding element.
        forall|i: int|
            #![trigger IteratorSpec::remaining(&iter)[i]]
            #![trigger final(slice)@[i]]
            0 <= i < old(slice)@.len() ==> *final(IteratorSpec::remaining(&iter)[i]) == final(slice)@[i],
        IteratorSpec::obeys_prophetic_iter_laws(&iter),
        IteratorSpec::will_return_none(&iter),
        IteratorSpec::decrease(&iter) is Some,
;

#[vcheck(T = u32)]
pub assume_specification<T> [ <[T]>::first ](slice: &[T]) -> (res: Option<&T>)
    ensures
        slice.len() == 0 ==> res.is_none(),
        slice.len() != 0 ==> res.is_some() && res.unwrap() == slice[0]
    no_unwind
;

#[vcheck(T = u32)]
pub assume_specification<T> [ <[T]>::last ](slice: &[T]) -> (res: Option<&T>)
    ensures
        slice.len() == 0 ==> res.is_none(),
        slice.len() != 0 ==> res.is_some() && res.unwrap() == slice@.last()
    no_unwind
;

#[doc(hidden)]
pub assume_specification<T> [ <[T]>::first_mut ](slice: &mut [T]) -> (res: Option<&mut T>)
    ensures
        old(slice).len() == 0 ==> res.is_none() && final(slice)@ == seq![],
        old(slice).len() != 0 ==> res.is_some() && *res.unwrap() == old(slice)[0]
            && final(slice)@ == old(slice)@.update(0, *final(res.unwrap()))
    no_unwind
;

#[doc(hidden)]
pub assume_specification<T> [ <[T]>::last_mut ](slice: &mut [T]) -> (res: Option<&mut T>)
    ensures
        old(slice).len() == 0 ==> res.is_none() && final(slice)@ == seq![],
        old(slice).len() != 0 ==> res.is_some() && *res.unwrap() == old(slice)@.last()
            && final(slice)@ == old(slice)@.update(old(slice).len() - 1, *final(res.unwrap()))
    no_unwind
;

#[vcheck(T = u32)]
pub assume_specification<T> [ <[T]>::split_at ](slice: &[T], mid: usize) -> (ret: (&[T], &[T]))
    requires
        0 <= mid <= slice.len(),
    ensures
        ret.0@ == slice@.take(mid as int),
        ret.1@ == slice@.skip(mid as int),
    no_unwind
;

#[doc(hidden)]
pub assume_specification<T> [ <[T]>::split_at_mut ](slice: &mut [T], mid: usize) -> (ret: (&mut [T], &mut [T]))
    requires
        0 <= mid <= slice.len(),
    ensures
        ret.0@ == old(slice)@[..mid],
        ret.1@ == old(slice)@[mid..],
        final(slice)@ == final(ret.0)@ + final(ret.1)@,
    no_unwind
;

// The non-panicking (`Option`-returning) form of `split_at`: `Some((a, b))` split at `mid`
// when `mid <= len`, else `None`.
pub assume_specification<T> [ <[T]>::split_at_checked ](slice: &[T], mid: usize) -> (ret: Option<(&[T], &[T])>)
    ensures
        mid <= slice.len() ==> (ret matches Some((a, b))
            && a@ == slice@[..mid]
            && b@ == slice@[mid..]),
        mid > slice.len() ==> ret is None,
    no_unwind
;

pub assume_specification<T> [ <[T]>::split_first ](slice: &[T]) -> (ret: Option<(&T, &[T])>)
    ensures
        slice.len() == 0 ==> ret.is_none(),
        slice.len() > 0 ==> (ret matches Some((a, b)) && a == slice[0] && b@ == slice@[1..])
    no_unwind
;

pub assume_specification<T> [ <[T]>::split_first_mut ](slice: &mut [T]) -> (ret: Option<(&mut T, &mut [T])>)
    ensures
        old(slice).len() == 0 ==> ret.is_none() && final(slice)@ == seq![],
        old(slice).len() > 0 ==> (ret matches Some((a, b))
            && *a == old(slice)[0]
            && b@ == old(slice)@[1..]
            && b@.len() == final(b)@.len()
            && final(slice)@ == seq![*final(a)] + final(b)@
        )
    no_unwind
;

/// Copy the contents of `src` into `dst`, which must have the same length.
pub assume_specification<T: Copy>[ <[T]>::copy_from_slice ](dst: &mut [T], src: &[T])
    requires
        old(dst)@.len() == src@.len(),
    ensures
        final(dst)@ == src@,
;

/// The sequence resulting from copying `old_slice[src_start..src_end]` to start
/// at index `dest`, leaving all other positions unchanged. Reads are taken from
/// `old_slice`, so overlapping source and destination ranges are handled like
/// std's `<[T]>::copy_within` (which uses `ptr::copy`).
pub open spec fn copy_within_result<T>(
    old_slice: Seq<T>,
    src_start: int,
    src_end: int,
    dest: int,
) -> Seq<T> {
    let count = src_end - src_start;
    Seq::new(
        old_slice.len(),
        |i: int|
            if dest <= i && i < dest + count {
                old_slice[src_start + (i - dest)]
            } else {
                old_slice[i]
            },
    )
}

/// Copy the elements in range `src` within the slice to start at index `dest`.
pub assume_specification<T: Copy, R: core::ops::RangeBounds<usize>>[ <[T]>::copy_within::<R> ](
    slice: &mut [T],
    src: R,
    dest: usize,
)
    requires
        slice_range_valid(&src, old(slice)@.len()),
        (dest as int) + (slice_range_end(&src, old(slice)@.len()) - slice_range_start(&src))
            <= old(slice)@.len(),
    ensures
        final(slice)@ == copy_within_result(
            old(slice)@,
            slice_range_start(&src),
            slice_range_end(&src, old(slice)@.len()),
            dest as int,
        ),
;

// vcheck wrappers for the guarded slice ops

/// `split_at_checked`: Some of the two subranges iff `mid <= len`
#[cfg(not(any(verus_verify_core, verus_keep_ghost)))]
#[verifier::external_body]
#[vcheck]
pub fn vcheck_slice_split_at_checked(v: Vec<u32>, mid: u16) -> (ret: bool)
    ensures
        ret,
{
    let mid = mid as usize;
    match v.split_at_checked(mid) {
        Some((a, b)) => mid <= v.len() && a == &v[..mid] && b == &v[mid..],
        None => mid > v.len(),
    }
}

/// `copy_from_slice` (equal-length guard): dst becomes src
#[cfg(not(any(verus_verify_core, verus_keep_ghost)))]
#[verifier::external_body]
#[vcheck]
pub fn vcheck_slice_copy_from_slice(dst: Vec<u32>, src: Vec<u32>) -> (ret: bool)
    ensures
        ret,
{
    if dst.len() != src.len() {
        return true;  // precondition excluded
    }
    let mut dst = dst;
    dst.copy_from_slice(&src);
    dst == src
}

/// `copy_within` at `R = Range<usize>` (validity guards discharged by filtering)
#[cfg(not(any(verus_verify_core, verus_keep_ghost)))]
#[verifier::external_body]
#[vcheck]
pub fn vcheck_slice_copy_within(v: Vec<u32>, start: u16, end: u16, dest: u16) -> (ret: bool)
    ensures
        ret,
{
    let (start, end, dest) = (start as usize, end as usize, dest as usize);
    if !(start <= end && end <= v.len()) || dest + (end - start) > v.len() {
        return true;  // precondition excluded
    }
    let mut r = v.clone();
    r.copy_within(start..end, dest);
    let count = end - start;
    (0..v.len()).all(|i| {
        let expected = if dest <= i && i < dest + count { v[start + (i - dest)] } else { v[i] };
        r[i] == expected
    })
}

} // verus!

verus! {

// SliceIndexSpec bounds model at each sampled range type

#[cfg(not(any(verus_verify_core, verus_keep_ghost)))]
#[verifier::external_body]
#[vcheck]
pub fn vcheck_slice_get_range(v: &[u8], r: Range<usize>) -> (out: Option<usize>)
    ensures
        out is Some <==> r.start <= r.end && r.end <= v@.len(),
        out is Some ==> out->Some_0 == r.end - r.start,
{
    v.get(r).map(|x| x.len())
}

#[cfg(not(any(verus_verify_core, verus_keep_ghost)))]
#[verifier::external_body]
#[vcheck]
pub fn vcheck_slice_get_range_to(v: &[u8], r: RangeTo<usize>) -> (out: Option<usize>)
    ensures
        out is Some <==> r.end <= v@.len(),
        out is Some ==> out->Some_0 == r.end,
{
    v.get(r).map(|x| x.len())
}

#[cfg(not(any(verus_verify_core, verus_keep_ghost)))]
#[verifier::external_body]
#[vcheck]
pub fn vcheck_slice_get_range_from(v: &[u8], r: RangeFrom<usize>) -> (out: Option<usize>)
    ensures
        out is Some <==> r.start <= v@.len(),
        out is Some ==> out->Some_0 == v@.len() - r.start,
{
    v.get(r).map(|x| x.len())
}

#[cfg(not(any(verus_verify_core, verus_keep_ghost)))]
#[verifier::external_body]
#[vcheck]
pub fn vcheck_slice_get_range_full(v: &[u8], r: RangeFull) -> (out: Option<usize>)
    ensures
        out is Some,
        out->Some_0 == v@.len(),
{
    v.get(r).map(|x| x.len())
}

#[cfg(not(any(verus_verify_core, verus_keep_ghost)))]
#[verifier::external_body]
#[vcheck]
pub fn vcheck_slice_get_range_to_inclusive(v: &[u8], r: RangeToInclusive<usize>) -> (out: Option<usize>)
    ensures
        out is Some <==> r.end as int + 1 <= v@.len(),
        out is Some ==> out->Some_0 == r.end as int + 1,
{
    v.get(r).map(|x| x.len())
}

#[cfg(not(any(verus_verify_core, verus_keep_ghost)))]
#[verifier::external_body]
#[vcheck]
pub fn vcheck_slice_get_range_inclusive(v: &[u8], r: RangeInclusive<usize>) -> (out: Option<usize>)
    ensures
        out is Some <==> r@.start <= (if r@.exhausted { r@.end as int } else { r@.end as int + 1 })
            && (if r@.exhausted { r@.end as int } else { r@.end as int + 1 }) <= v@.len(),
        out is Some ==> out->Some_0 == (if r@.exhausted { r@.end as int } else { r@.end as int + 1 })
            - r@.start,
{
    v.get(r).map(|x| x.len())
}

#[cfg(not(any(verus_verify_core, verus_keep_ghost)))]
#[verifier::external_body]
#[vcheck]
pub fn vcheck_slice_get_mut_range_inclusive(v: &mut Vec<u8>, r: RangeInclusive<usize>, w: u8) -> (ok: bool)
    ensures
        ok <==> r@.start <= (if r@.exhausted { r@.end as int } else { r@.end as int + 1 })
            && (if r@.exhausted { r@.end as int } else { r@.end as int + 1 }) <= old(v)@.len(),
        !ok ==> final(v)@ == old(v)@,
        final(v)@.len() == old(v)@.len(),
{
    match v.as_mut_slice().get_mut(r) {
        Some(x) => {
            for e in x.iter_mut() {
                *e = w;
            }
            true
        },
        None => false,
    }
}

} // verus!

verus! {

/// `starts_with` / `ends_with` against the spec fns, with needles cut from the haystack
#[cfg(not(any(verus_verify_core, verus_keep_ghost)))]
#[verifier::external_body]
#[vcheck]
pub fn vcheck_slice_starts_ends_with(s: Vec<u8>, k: u8, flip: u8, extra: bool, tail: bool) -> (ret: bool)
    ensures
        ret,
{
    let len = s.len();
    let k = (k as usize) % (len + 2);
    let mut needle: Vec<u8> = if tail {
        s[len - k.min(len)..].to_vec()
    } else {
        s[..k.min(len)].to_vec()
    };
    if extra {
        needle.push(7);
    }
    if !needle.is_empty() && flip % 3 == 0 {
        let i = (flip as usize) % needle.len();
        needle[i] = needle[i].wrapping_add(1);
    }
    let n = needle.len();
    let spec = n <= len && (0..n).all(
        |i|
            if tail {
                s[len - n + i] == needle[i]
            } else {
                s[i] == needle[i]
            },
    );
    let result = if tail {
        s.ends_with(&needle)
    } else {
        s.starts_with(&needle)
    };
    (n <= len || !result) && result == spec
}

/// `first_mut` / `last_mut` read the end element and write through to the slice
#[cfg(not(any(verus_verify_core, verus_keep_ghost)))]
#[verifier::external_body]
#[vcheck]
pub fn vcheck_slice_first_last_mut(v: Vec<u32>, w: u32, last: bool) -> (ret: bool)
    ensures
        ret,
{
    let mut v2 = v.clone();
    let r = if last {
        v2.as_mut_slice().last_mut()
    } else {
        v2.as_mut_slice().first_mut()
    };
    match r {
        None => v.is_empty() && v2.is_empty(),
        Some(x) => {
            let i = if last {
                v.len() - 1
            } else {
                0
            };
            let ok = !v.is_empty() && *x == v[i];
            *x = w;
            let mut exp = v.clone();
            exp[i] = w;
            ok && v2 == exp
        },
    }
}

/// `split_first` / `split_first_mut` split off the head, with writes through both parts
#[cfg(not(any(verus_verify_core, verus_keep_ghost)))]
#[verifier::external_body]
#[vcheck]
pub fn vcheck_slice_split_first(v: Vec<u32>, w: u32, w2: u32) -> (ret: bool)
    ensures
        ret,
{
    let shared_ok = match v.split_first() {
        None => v.is_empty(),
        Some((a, b)) => !v.is_empty() && *a == v[0] && b == &v[1..],
    };
    let mut v2 = v.clone();
    let mut_ok = match v2.as_mut_slice().split_first_mut() {
        None => v.is_empty(),
        Some((a, b)) => {
            let ok = !v.is_empty() && *a == v[0] && &*b == &v[1..];
            *a = w;
            if let Some(y) = b.last_mut() {
                *y = w2;
            }
            ok
        },
    };
    let mut exp = v.clone();
    if !exp.is_empty() {
        exp[0] = w;
        if exp.len() > 1 {
            let l = exp.len() - 1;
            exp[l] = w2;
        }
    }
    shared_ok && mut_ok && v2 == exp
}

/// `split_at_mut` halves match the subranges and writes flow back into the slice
#[cfg(not(any(verus_verify_core, verus_keep_ghost)))]
#[verifier::external_body]
#[vcheck]
pub fn vcheck_slice_split_at_mut(v: Vec<u32>, mid: u8, w: u32, w2: u32) -> (ret: bool)
    ensures
        ret,
{
    let mid = (mid as usize) % (v.len() + 1);
    let mut v2 = v.clone();
    let (a, b) = v2.as_mut_slice().split_at_mut(mid);
    let ok = &*a == &v[..mid] && &*b == &v[mid..];
    if let Some(x) = a.last_mut() {
        *x = w;
    }
    if let Some(y) = b.first_mut() {
        *y = w2;
    }
    let mut exp = v.clone();
    if mid > 0 {
        exp[mid - 1] = w;
    }
    if mid < exp.len() {
        exp[mid] = w2;
    }
    ok && v2 == exp
}

/// `iter` / `into_iter` yield exactly the slice's elements in order
#[cfg(not(any(verus_verify_core, verus_keep_ghost)))]
#[verifier::external_body]
#[vcheck]
pub fn vcheck_slice_iter(v: Vec<u32>) -> (ret: bool)
    ensures
        ret,
{
    let a: Vec<u32> = v.as_slice().iter().copied().collect();
    let b: Vec<u32> = (&v[..]).into_iter().copied().collect();
    a == v && b == v
}

/// `iter_mut` yields references to each element whose final values flow back
#[cfg(not(any(verus_verify_core, verus_keep_ghost)))]
#[verifier::external_body]
#[vcheck]
pub fn vcheck_slice_iter_mut(v: Vec<u32>, w: u32) -> (ret: bool)
    ensures
        ret,
{
    let mut v2 = v.clone();
    let mut ok = true;
    let mut n = 0usize;
    for (i, r) in v2.as_mut_slice().iter_mut().enumerate() {
        ok = ok && *r == v[i];
        *r = w.wrapping_add(i as u32);
        n += 1;
    }
    ok && n == v.len() && (0..v.len()).all(|i| v2[i] == w.wrapping_add(i as u32))
}

/// usize `get` / `get_mut` agree with `in_bounds`, and `get_mut` writes through
#[cfg(not(any(verus_verify_core, verus_keep_ghost)))]
#[verifier::external_body]
#[vcheck]
pub fn vcheck_slice_get_usize(v: Vec<u32>, i: u8, w: u32) -> (ret: bool)
    ensures
        ret,
{
    let i = (i as usize) % (v.len() + 2);
    let g = match v.get(i) {
        Some(x) => i < v.len() && *x == v[i],
        None => i >= v.len(),
    };
    let mut v2 = v.clone();
    let gm = match v2.get_mut(i) {
        Some(x) => {
            let ok = i < v.len() && *x == v[i];
            *x = w;
            ok
        },
        None => i >= v.len(),
    };
    let mut exp = v.clone();
    if i < exp.len() {
        exp[i] = w;
    }
    g && gm && v2 == exp
}

} // verus!

verus! {

/// `all` / `any` / `find` on a slice iterator consume exactly through the deciding element
#[cfg(not(any(verus_verify_core, verus_keep_ghost)))]
#[verifier::external_body]
#[vcheck]
pub fn vcheck_iter_all_any_find(v: Vec<u8>, k: u8) -> (ret: bool)
    ensures
        ret,
{
    let pred = |x: &u8| *x < k;
    let first_fail = v.iter().position(|x| !pred(x));
    let first_hit = v.iter().position(|x| pred(x));
    let mut it = v.iter();
    let r_all = it.all(|x| pred(x));
    let rest_all = it.as_slice().len();
    let all_ok = match first_fail {
        None => r_all && rest_all == 0,
        Some(i) => !r_all && rest_all == v.len() - i - 1,
    };
    let mut it = v.iter();
    let r_any = it.any(|x| pred(x));
    let rest_any = it.as_slice().len();
    let any_ok = match first_hit {
        None => !r_any && rest_any == 0,
        Some(i) => r_any && rest_any == v.len() - i - 1,
    };
    let mut it = v.iter();
    let r_find = it.find(|x| pred(*x)).copied();
    let rest_find = it.as_slice().len();
    let find_ok = match first_hit {
        None => r_find.is_none() && rest_find == 0,
        Some(i) => r_find == Some(v[i]) && rest_find == v.len() - i - 1,
    };
    all_ok && any_ok && find_ok
}

} // verus!
