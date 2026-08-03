use super::super::prelude::*;
use super::super::view::View;
use super::cmp::{PartialOrdIs, PartialOrdSpec};
// PBT in-place patch: std_specs::iter is still ghost-gated, so the items
// below that implement / reference its spec traits are gated per-item.
#[cfg(verus_keep_ghost)]
use super::iter::{IteratorSpec, StepSpec, StepSpecImpl};
use core::ops::{
    Bound, Range, RangeBounds, RangeFrom, RangeFull, RangeInclusive, RangeTo, RangeToInclusive,
};

verus! {

#[verifier::external_type_specification]
#[verifier::reject_recursive_types_in_ground_variants(Idx)]
pub struct ExRange<Idx>(Range<Idx>);

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types_in_ground_variants(Idx)]
pub struct ExRangeInclusive<Idx>(RangeInclusive<Idx>);

pub struct RangeInclusiveView<Idx> {
    pub start: Idx,
    pub end: Idx,
    pub exhausted: bool,
}

pub trait ContainsSpec<Idx, U> where Idx: PartialOrd<U>, U: ?Sized + PartialOrd<Idx> {
    spec fn obeys_contains() -> bool;

    spec fn contains_spec(&self, i: &U) -> bool;
}

impl<Idx, U> ContainsSpec<Idx, U> for RangeInclusive<Idx> where
    Idx: PartialOrd<U>,
    U: ?Sized + PartialOrd<Idx>,
 {
    open spec fn obeys_contains() -> bool {
        (U::obeys_partial_cmp_spec() && <Idx as PartialOrdSpec<U>>::obeys_partial_cmp_spec())
    }

    open spec fn contains_spec(&self, i: &U) -> bool {
        self@.start.is_le(&i) && if self@.exhausted {
            i.is_lt(&self@.end)
        } else {
            i.is_le(&self@.end)
        }
    }
}

impl<Idx, U> ContainsSpec<Idx, U> for Range<Idx> where
    Idx: PartialOrd<U>,
    U: ?Sized + PartialOrd<Idx>,
 {
    open spec fn obeys_contains() -> bool {
        (U::obeys_partial_cmp_spec() && <Idx as PartialOrdSpec<U>>::obeys_partial_cmp_spec())
    }

    open spec fn contains_spec(&self, i: &U) -> bool {
        self.start.is_le(&i) && i.is_lt(&self.end)
    }
}

impl<Idx> View for RangeInclusive<Idx> {
    type V = RangeInclusiveView<Idx>;

    uninterp spec fn view(&self) -> Self::V;
}

pub uninterp spec fn spec_range_next<A>(a: Range<A>) -> (Range<A>, Option<A>);

/// Range::contains method is valid and safe to use only when cmp operations are implemented to satisfy
/// obeys_partial_cmp_spec. Specifically, the comparison must be deterministic, and `lt` (less than)
/// and `le` (less than or equal to) must define total orders.
/// If using Range::contains with types that do not satisfy obeys_partial_cmp_spec, no spec is provided.
pub assume_specification<Idx: PartialOrd<Idx>, U>[ Range::<Idx>::contains ](
    r: &Range<Idx>,
    i: &U,
) -> (ret: bool) where Idx: PartialOrd<U>, U: ?Sized + PartialOrd<Idx>
    ensures
        <Range::<Idx> as ContainsSpec<Idx, U>>::obeys_contains() ==> ret == r.contains_spec(i),
;

pub assume_specification<Idx: PartialOrd<Idx>, U>[ RangeInclusive::<Idx>::contains ](
    r: &RangeInclusive<Idx>,
    i: &U,
) -> (ret: bool) where Idx: PartialOrd<U>, U: ?Sized + PartialOrd<Idx>
    ensures
        <RangeInclusive::<Idx> as ContainsSpec<Idx, U>>::obeys_contains() ==> ret
            == r.contains_spec(i),
;

// To allow reasoning about the returned range when the executable
// function `RangeInclusive::new()` is invoked in a `for` loop header
// (e.g., in `for x in it: start..=end { ... }`), we need to specify the
// behavior of the constructed range in spec mode. To do that, we add
// `#[verifier::when_used_as_spec(spec_range_inclusive_new)]` to the
// specification for the executable `RangeInclusive::new` method and define
// that spec function here.
pub uninterp spec fn spec_range_inclusive_new<Idx>(
    start: Idx,
    end: Idx,
) -> core::ops::RangeInclusive<Idx>;

pub broadcast axiom fn axiom_spec_range_inclusive_new<Idx>(start: Idx, end: Idx)
    ensures
        (#[trigger] spec_range_inclusive_new(start, end))@ == {
            RangeInclusiveView { start, end, exhausted: false }
        },
;

#[verifier::when_used_as_spec(spec_range_inclusive_new)]
pub assume_specification<Idx>[ RangeInclusive::<Idx>::new ](start: Idx, end: Idx) -> (ret:
    core::ops::RangeInclusive<Idx>)
    ensures
        ret == spec_range_inclusive_new(start, end),
;

#[cfg(verus_keep_ghost)]
impl<A: core::iter::Step> super::iter::IteratorSpecImpl for Range<A> {
    open spec fn obeys_prophetic_iter_laws(&self) -> bool {
        true
    }

    open spec fn remaining(&self) -> Seq<Self::Item> {
        Seq::new(
            self.start.spec_steps_between_int(self.end) as nat,
            |i: int| self.start.spec_forward_checked_int(i).unwrap(),
        )
    }

    uninterp spec fn will_return_none(&self) -> bool;

    #[verifier::prophetic]
    open spec fn initial_value_relation(&self, init: &Self) -> bool {
        // Standard invariant for the iterator itself:
        //   If there are no steps between start and end, then remaining is empty;
        //   otherwise it contains all of the steps in between start and end
        &&& (self.start.spec_steps_between_int(self.end) <= 0 && IteratorSpec::remaining(self).len()
            == 0) || (self.start.spec_steps_between_int(self.end) == IteratorSpec::remaining(
            self,
        ).len() as int)
        &&& forall|i: int|
            0 <= i < IteratorSpec::remaining(self).len() ==> #[trigger] IteratorSpec::remaining(
                self,
            )[i] == self.start.spec_forward_checked_int(
                i,
            ).unwrap()
        // Connections to init
        &&& self.start == init.start
        &&& self.end == init.end
        &&& (init.start.spec_steps_between_int(init.end) <= 0 && IteratorSpec::remaining(self).len()
            == 0) || (init.start.spec_steps_between_int(self.end) == IteratorSpec::remaining(
            self,
        ).len() as int)
        &&& forall|i: int|
            0 <= i < IteratorSpec::remaining(self).len() ==> #[trigger] IteratorSpec::remaining(
                self,
            )[i] == init.start.spec_forward_checked_int(i).unwrap()
    }

    open spec fn decrease(&self) -> Option<nat> {
        Some(self.start.spec_steps_between_int(self.end) as nat)
    }

    open spec fn peek(&self, index: int) -> Option<Self::Item> {
        //Some(self.start.spec_forward_checked_int(index).unwrap())
        if 0 <= index <= self.start.spec_steps_between_int(self.end) {
            Some(self.start.spec_forward_checked_int(index).unwrap())
        } else {
            None
        }
    }
}

#[cfg(verus_keep_ghost)]
impl<A: core::iter::Step> super::iter::IteratorSpecImpl for RangeInclusive<A> {
    open spec fn obeys_prophetic_iter_laws(&self) -> bool {
        true
    }

    open spec fn remaining(&self) -> Seq<Self::Item> {
        Seq::new(
            (self@.start.spec_steps_between_int(self@.end) + 1) as nat,
            |i: int| self@.start.spec_forward_checked_int(i).unwrap(),
        )
    }

    uninterp spec fn will_return_none(&self) -> bool;

    #[verifier::prophetic]
    open spec fn initial_value_relation(&self, init: &Self) -> bool {
        // Standard invariant for the iterator itself:
        //   If there are no steps between start and end, then remaining is empty;
        //   otherwise it contains all of the steps in between start and end
        &&& (self@.start.spec_steps_between_int(self@.end) + 1 <= 0 && IteratorSpec::remaining(
            self,
        ).len() == 0) || (self@.start.spec_steps_between_int(self@.end) + 1
            == IteratorSpec::remaining(self).len() as int)
        &&& forall|i: int|
            0 <= i < IteratorSpec::remaining(self).len() ==> #[trigger] IteratorSpec::remaining(
                self,
            )[i] == self@.start.spec_forward_checked_int(
                i,
            ).unwrap()
        // Connections to init
        &&& self@.start == init@.start
        &&& self@.end == init@.end
        &&& (init@.start.spec_steps_between_int(init@.end) + 1 <= 0 && IteratorSpec::remaining(
            self,
        ).len() == 0) || (init@.start.spec_steps_between_int(self@.end) + 1
            == IteratorSpec::remaining(self).len() as int)
        &&& forall|i: int|
            0 <= i < IteratorSpec::remaining(self).len() ==> #[trigger] IteratorSpec::remaining(
                self,
            )[i] == init@.start.spec_forward_checked_int(i).unwrap()
    }

    open spec fn decrease(&self) -> Option<nat> {
        Some((self@.start.spec_steps_between_int(self@.end) + 1) as nat)
    }

    open spec fn peek(&self, index: int) -> Option<Self::Item> {
        if 0 <= index <= self@.start.spec_steps_between_int(self@.end) + 1 {
            Some(self@.start.spec_forward_checked_int(index).unwrap())
        } else {
            None
        }
    }
}

pub assume_specification<A: core::iter::Step>[ <Range<A> as Iterator>::next ](
    range: &mut Range<A>,
) -> (r: Option<A>)
    ensures
        (*final(range), r) == spec_range_next(*old(range)),
;

/// Spec model of [`core::ops::Bound`], used by [`RangeBoundsSpec`] to describe
/// the start and end bounds of a range. See [`spec_bound`] for the connection
/// to `Bound` values.
pub enum SpecBound<T> {
    Included(T),
    Excluded(T),
    Unbounded,
}

/// Spec model of a [`core::ops::Bound`] value as a [`SpecBound`].
pub open spec fn spec_bound<T>(bound: Bound<T>) -> SpecBound<T> {
    match bound {
        Bound::Included(value) => SpecBound::Included(value),
        Bound::Excluded(value) => SpecBound::Excluded(value),
        Bound::Unbounded => SpecBound::Unbounded,
    }
}

/// Spec model of a borrowed [`core::ops::Bound`] value as a [`SpecBound`].
pub open spec fn spec_bound_ref<'a, T>(bound: &'a Bound<T>) -> SpecBound<&'a T> {
    match bound {
        Bound::Included(value) => SpecBound::Included(value),
        Bound::Excluded(value) => SpecBound::Excluded(value),
        Bound::Unbounded => SpecBound::Unbounded,
    }
}

#[verifier::external_type_specification]
pub struct ExBound<T>(Bound<T>);

#[verifier::external_type_specification]
pub struct ExRangeFull(RangeFull);

#[verifier::external_type_specification]
#[verifier::reject_recursive_types(Idx)]
pub struct ExRangeFrom<Idx>(RangeFrom<Idx>);

#[verifier::external_type_specification]
#[verifier::reject_recursive_types(Idx)]
pub struct ExRangeTo<Idx>(RangeTo<Idx>);

#[verifier::external_type_specification]
#[verifier::reject_recursive_types(Idx)]
pub struct ExRangeToInclusive<Idx>(RangeToInclusive<Idx>);

// Per-type specifications for `RangeBounds::start_bound`/`end_bound`, so these
// methods can also be called directly in exec code (not just via the spec-mode
// models above). Each spec agrees with the corresponding `RangeBoundsSpecImpl`.
pub assume_specification<'s, T>[ <Range<T> as RangeBounds<T>>::start_bound ](
    range: &'s Range<T>,
) -> (result: Bound<&'s T>)
    ensures
        spec_bound(result) == SpecBound::Included(&range.start),
;

pub assume_specification<'s, T>[ <Range<T> as RangeBounds<T>>::end_bound ](
    range: &'s Range<T>,
) -> (result: Bound<&'s T>)
    ensures
        spec_bound(result) == SpecBound::Excluded(&range.end),
;

pub assume_specification<'s, T: ?Sized>[ <RangeFull as RangeBounds<T>>::start_bound ](
    range: &'s RangeFull,
) -> (result: Bound<&'s T>)
    ensures
        spec_bound(result) == SpecBound::Unbounded,
;

pub assume_specification<'s, T: ?Sized>[ <RangeFull as RangeBounds<T>>::end_bound ](
    range: &'s RangeFull,
) -> (result: Bound<&'s T>)
    ensures
        spec_bound(result) == SpecBound::Unbounded,
;

pub assume_specification<'s, T>[ <RangeFrom<T> as RangeBounds<T>>::start_bound ](
    range: &'s RangeFrom<T>,
) -> (result: Bound<&'s T>)
    ensures
        spec_bound(result) == SpecBound::Included(&range.start),
;

pub assume_specification<'s, T>[ <RangeFrom<T> as RangeBounds<T>>::end_bound ](
    range: &'s RangeFrom<T>,
) -> (result: Bound<&'s T>)
    ensures
        spec_bound(result) == SpecBound::Unbounded,
;

pub assume_specification<'s, T>[ <RangeTo<T> as RangeBounds<T>>::start_bound ](
    range: &'s RangeTo<T>,
) -> (result: Bound<&'s T>)
    ensures
        spec_bound(result) == SpecBound::Unbounded,
;

pub assume_specification<'s, T>[ <RangeTo<T> as RangeBounds<T>>::end_bound ](
    range: &'s RangeTo<T>,
) -> (result: Bound<&'s T>)
    ensures
        spec_bound(result) == SpecBound::Excluded(&range.end),
;

pub assume_specification<'s, T>[ <RangeInclusive<T> as RangeBounds<T>>::start_bound ](
    range: &'s RangeInclusive<T>,
) -> (result: Bound<&'s T>)
    ensures
        spec_bound(result) == SpecBound::Included(&range@.start),
;

pub assume_specification<'s, T>[ <RangeInclusive<T> as RangeBounds<T>>::end_bound ](
    range: &'s RangeInclusive<T>,
) -> (result: Bound<&'s T>)
    ensures
        spec_bound(result) == SpecBound::Included(&range@.end),
;

pub assume_specification<'s, T>[ <RangeToInclusive<T> as RangeBounds<T>>::start_bound ](
    range: &'s RangeToInclusive<T>,
) -> (result: Bound<&'s T>)
    ensures
        spec_bound(result) == SpecBound::Unbounded,
;

pub assume_specification<'s, T>[ <RangeToInclusive<T> as RangeBounds<T>>::end_bound ](
    range: &'s RangeToInclusive<T>,
) -> (result: Bound<&'s T>)
    ensures
        spec_bound(result) == SpecBound::Included(&range.end),
;

pub assume_specification<'s, T>[ <(Bound<T>, Bound<T>) as RangeBounds<T>>::start_bound ](
    range: &'s (Bound<T>, Bound<T>),
) -> (result: Bound<&'s T>)
    ensures
        spec_bound(result) == spec_bound_ref(&range.0),
;

pub assume_specification<'s, T>[ <(Bound<T>, Bound<T>) as RangeBounds<T>>::end_bound ](
    range: &'s (Bound<T>, Bound<T>),
) -> (result: Bound<&'s T>)
    ensures
        spec_bound(result) == spec_bound_ref(&range.1),
;

/// Specification for [`core::ops::RangeBounds`], exposing spec-mode models
/// [`spec_start_bound`](RangeBoundsSpec::spec_start_bound) and
/// [`spec_end_bound`](RangeBoundsSpec::spec_end_bound) of the trait's
/// `start_bound`/`end_bound` methods. This mirrors std's normalization of an
/// arbitrary range into a pair of bounds and is the model used by
/// `<[T]>::copy_within` (see `vstd::std_specs::slice`).
#[verifier::external_trait_specification]
#[verifier::external_trait_extension(RangeBoundsSpec via RangeBoundsSpecImpl)]
pub trait ExRangeBounds<T: ?Sized> {
    type ExternalTraitSpecificationFor: RangeBounds<T>;

    spec fn spec_start_bound(&self) -> SpecBound<&T>;

    spec fn spec_end_bound(&self) -> SpecBound<&T>;

    fn start_bound(&self) -> Bound<&T>;

    fn end_bound(&self) -> Bound<&T>;
}

impl<T> RangeBoundsSpecImpl<T> for Range<T> {
    open spec fn spec_start_bound(&self) -> SpecBound<&T> {
        SpecBound::Included(&self.start)
    }

    open spec fn spec_end_bound(&self) -> SpecBound<&T> {
        SpecBound::Excluded(&self.end)
    }
}

impl<T: ?Sized> RangeBoundsSpecImpl<T> for RangeFull {
    open spec fn spec_start_bound(&self) -> SpecBound<&T> {
        SpecBound::Unbounded
    }

    open spec fn spec_end_bound(&self) -> SpecBound<&T> {
        SpecBound::Unbounded
    }
}

impl<T> RangeBoundsSpecImpl<T> for RangeFrom<T> {
    open spec fn spec_start_bound(&self) -> SpecBound<&T> {
        SpecBound::Included(&self.start)
    }

    open spec fn spec_end_bound(&self) -> SpecBound<&T> {
        SpecBound::Unbounded
    }
}

impl<T> RangeBoundsSpecImpl<T> for RangeTo<T> {
    open spec fn spec_start_bound(&self) -> SpecBound<&T> {
        SpecBound::Unbounded
    }

    open spec fn spec_end_bound(&self) -> SpecBound<&T> {
        SpecBound::Excluded(&self.end)
    }
}

impl<T> RangeBoundsSpecImpl<T> for RangeInclusive<T> {
    open spec fn spec_start_bound(&self) -> SpecBound<&T> {
        SpecBound::Included(&self@.start)
    }

    open spec fn spec_end_bound(&self) -> SpecBound<&T> {
        SpecBound::Included(&self@.end)
    }
}

impl<T> RangeBoundsSpecImpl<T> for RangeToInclusive<T> {
    open spec fn spec_start_bound(&self) -> SpecBound<&T> {
        SpecBound::Unbounded
    }

    open spec fn spec_end_bound(&self) -> SpecBound<&T> {
        SpecBound::Included(&self.end)
    }
}

impl<T> RangeBoundsSpecImpl<T> for (Bound<T>, Bound<T>) {
    open spec fn spec_start_bound(&self) -> SpecBound<&T> {
        spec_bound_ref(&self.0)
    }

    open spec fn spec_end_bound(&self) -> SpecBound<&T> {
        spec_bound_ref(&self.1)
    }
}

impl<'a, T: ?Sized + 'a> RangeBoundsSpecImpl<T> for (Bound<&'a T>, Bound<&'a T>) {
    open spec fn spec_start_bound(&self) -> SpecBound<&T> {
        match self.0 {
            Bound::Included(start) => SpecBound::Included(start),
            Bound::Excluded(start) => SpecBound::Excluded(start),
            Bound::Unbounded => SpecBound::Unbounded,
        }
    }

    open spec fn spec_end_bound(&self) -> SpecBound<&T> {
        match self.1 {
            Bound::Included(end) => SpecBound::Included(end),
            Bound::Excluded(end) => SpecBound::Excluded(end),
            Bound::Unbounded => SpecBound::Unbounded,
        }
    }
}

impl<T> RangeBoundsSpecImpl<T> for RangeFrom<&T> {
    open spec fn spec_start_bound(&self) -> SpecBound<&T> {
        SpecBound::Included(self.start)
    }

    open spec fn spec_end_bound(&self) -> SpecBound<&T> {
        SpecBound::Unbounded
    }
}

impl<T> RangeBoundsSpecImpl<T> for RangeTo<&T> {
    open spec fn spec_start_bound(&self) -> SpecBound<&T> {
        SpecBound::Unbounded
    }

    open spec fn spec_end_bound(&self) -> SpecBound<&T> {
        SpecBound::Excluded(self.end)
    }
}

impl<T> RangeBoundsSpecImpl<T> for Range<&T> {
    open spec fn spec_start_bound(&self) -> SpecBound<&T> {
        SpecBound::Included(self.start)
    }

    open spec fn spec_end_bound(&self) -> SpecBound<&T> {
        SpecBound::Excluded(self.end)
    }
}

impl<T> RangeBoundsSpecImpl<T> for RangeInclusive<&T> {
    open spec fn spec_start_bound(&self) -> SpecBound<&T> {
        SpecBound::Included(self@.start)
    }

    open spec fn spec_end_bound(&self) -> SpecBound<&T> {
        SpecBound::Included(self@.end)
    }
}

impl<T> RangeBoundsSpecImpl<T> for RangeToInclusive<&T> {
    open spec fn spec_start_bound(&self) -> SpecBound<&T> {
        SpecBound::Unbounded
    }

    open spec fn spec_end_bound(&self) -> SpecBound<&T> {
        SpecBound::Included(self.end)
    }
}

/// Normalized (inclusive) start index of `range`, matching std's
/// `core::slice::range`: an inclusive bound `i` stays `i`, an exclusive bound
/// `i` becomes `i + 1`, and an unbounded start is `0`.
pub open spec fn slice_range_start<R: RangeBoundsSpec<usize>>(range: &R) -> int {
    match range.spec_start_bound() {
        SpecBound::Included(i) => *i as int,
        SpecBound::Excluded(i) => (*i as int) + 1,
        SpecBound::Unbounded => 0,
    }
}

/// Normalized (exclusive) end index of a range over a sequence of length `len`,
/// matching std's `core::slice::range`: an inclusive bound `i` becomes `i + 1`,
/// an exclusive bound `i` stays `i`, and an unbounded end is `len`.
pub open spec fn slice_range_end<R: RangeBoundsSpec<usize>>(range: &R, len: nat) -> int {
    match range.spec_end_bound() {
        SpecBound::Included(i) => (*i as int) + 1,
        SpecBound::Excluded(i) => *i as int,
        SpecBound::Unbounded => len as int,
    }
}

/// Whether a range normalizes to `start <= end <= len`, i.e. the condition
/// under which std's `core::slice::range` does not panic.
pub open spec fn slice_range_valid<R: RangeBoundsSpec<usize>>(range: &R, len: nat) -> bool {
    slice_range_start(range) <= slice_range_end(range, len) <= len
}

} // verus!
macro_rules! step_specs {
    ($t: ty, $axiom: ident) => {
        verus! {
        // PBT in-place patch: StepSpecImpl lives in the ghost-gated
        // std_specs::iter, so the spec impl is ghost-only.
        #[cfg(verus_keep_ghost)]
        impl StepSpecImpl for $t {
            open spec fn spec_is_lt(self, other: Self) -> bool {
                self < other
            }
            open spec fn spec_steps_between(self, end: Self) -> Option<usize> {
                let n = end - self;
                if usize::MIN <= n <= usize::MAX {
                    Some(n as usize)
                } else {
                    None
                }
            }
            open spec fn spec_steps_between_int(self, end: Self) -> int {
                end - self
            }
            open spec fn spec_forward_checked(self, count: usize) -> Option<Self> {
                StepSpec::spec_forward_checked_int(self, count as int)
            }
            open spec fn spec_forward_checked_int(self, count: int) -> Option<Self> {
                if self + count <= $t::MAX {
                    Some((self + count) as $t)
                } else {
                    None
                }
            }
            open spec fn spec_backward_checked(self, count: usize) -> Option<Self> {
                StepSpec::spec_backward_checked_int(self, count as int)
            }
            open spec fn spec_backward_checked_int(self, count: int) -> Option<Self> {
                if self - count >= $t::MIN {
                    Some((self - count) as $t)
                } else {
                    None
                }
            }
        }
        // TODO: we might be able to make this generic over A: StepSpec
        // once we settle on a way to connect std traits like Step with spec traits like StepSpec.
        pub broadcast proof fn $axiom(range: Range<$t>)
            ensures
                StepSpec::spec_is_lt(range.start, range.end) ==>
                    // TODO (not important): use new "matches ==>" syntax here
                    (if let Some(n) = StepSpec::spec_forward_checked(range.start, 1) {
                        spec_range_next(range) == (Range { start: n, ..range }, Some(range.start))
                    } else {
                        true
                    }),
                !StepSpec::spec_is_lt(range.start, range.end) ==>
                    #[trigger] spec_range_next(range) == (range, None::<$t>),
        {
            admit();
        }
        } // verus!
    };
}

step_specs!(u8, axiom_spec_range_next_u8);
step_specs!(u16, axiom_spec_range_next_u16);
step_specs!(u32, axiom_spec_range_next_u32);
step_specs!(u64, axiom_spec_range_next_u64);
step_specs!(u128, axiom_spec_range_next_u128);
step_specs!(usize, axiom_spec_range_next_usize);
step_specs!(i8, axiom_spec_range_next_i8);
step_specs!(i16, axiom_spec_range_next_i16);
step_specs!(i32, axiom_spec_range_next_i32);
step_specs!(i64, axiom_spec_range_next_i64);
step_specs!(i128, axiom_spec_range_next_i128);
step_specs!(isize, axiom_spec_range_next_isize);

verus! {

pub broadcast group group_range_axioms {
    axiom_spec_range_next_u8,
    axiom_spec_range_next_u16,
    axiom_spec_range_next_u32,
    axiom_spec_range_next_u64,
    axiom_spec_range_next_u128,
    axiom_spec_range_next_usize,
    axiom_spec_range_next_i8,
    axiom_spec_range_next_i16,
    axiom_spec_range_next_i32,
    axiom_spec_range_next_i64,
    axiom_spec_range_next_i128,
    axiom_spec_range_next_isize,
    axiom_spec_range_inclusive_new,
}

// ---------------------------------------------------------------------------
// Composite PBT wrappers. `contains` guards through obeys_partial_cmp_spec
// (checked at Idx = U = u32, where the spec-impl guard holds),
// `RangeInclusive` contracts route through its uninterp view (pinned via
// fresh construction + axiom_spec_range_inclusive_new, exhausted = false),
// and the RangeBounds specs compare against spec_bound projections. The
// pbt_range_next_specs! wrappers below check the per-width trusted admits
// (axiom_spec_range_next_*) composed with the `<Range as Iterator>::next`
// assume_specification.
// ---------------------------------------------------------------------------

/// `Range::contains` == `start <= i && i < end` (obeys_contains holds at u32).
#[cfg(not(verus_verify_core))]
#[verifier::external_body]
#[pbt]
pub fn pbt_range_contains(start: u32, end: u32, i: u32) -> (ret: bool)
    ensures
        ret,
{
    (start..end).contains(&i) == (start <= i && i < end)
}

/// `RangeInclusive::new` + view axiom + `contains`: a fresh (non-exhausted)
/// inclusive range contains `i` iff `start <= i <= end`.
#[cfg(not(verus_verify_core))]
#[verifier::external_body]
#[pbt]
pub fn pbt_range_inclusive_new_contains(start: u32, end: u32, i: u32) -> (ret: bool)
    ensures
        ret,
{
    RangeInclusive::new(start, end).contains(&i) == (start <= i && i <= end)
}

/// `Range` RangeBounds: Included(start) / Excluded(end).
#[cfg(not(verus_verify_core))]
#[verifier::external_body]
#[pbt]
pub fn pbt_range_bounds(start: u32, end: u32) -> (ret: bool)
    ensures
        ret,
{
    let r = start..end;
    matches!(RangeBounds::<u32>::start_bound(&r), Bound::Included(&s) if s == start)
        && matches!(RangeBounds::<u32>::end_bound(&r), Bound::Excluded(&e) if e == end)
}

/// `RangeFull` RangeBounds: Unbounded / Unbounded.
#[cfg(not(verus_verify_core))]
#[verifier::external_body]
#[pbt]
pub fn pbt_range_full_bounds() -> (ret: bool)
    ensures
        ret,
{
    matches!(RangeBounds::<u32>::start_bound(&(..)), Bound::Unbounded)
        && matches!(RangeBounds::<u32>::end_bound(&(..)), Bound::Unbounded)
}

/// `RangeFrom` RangeBounds: Included(start) / Unbounded.
#[cfg(not(verus_verify_core))]
#[verifier::external_body]
#[pbt]
pub fn pbt_range_from_bounds(start: u32) -> (ret: bool)
    ensures
        ret,
{
    let r = start..;
    matches!(RangeBounds::<u32>::start_bound(&r), Bound::Included(&s) if s == start)
        && matches!(RangeBounds::<u32>::end_bound(&r), Bound::Unbounded)
}

/// `RangeTo` RangeBounds: Unbounded / Excluded(end).
#[cfg(not(verus_verify_core))]
#[verifier::external_body]
#[pbt]
pub fn pbt_range_to_bounds(end: u32) -> (ret: bool)
    ensures
        ret,
{
    let r = ..end;
    matches!(RangeBounds::<u32>::start_bound(&r), Bound::Unbounded)
        && matches!(RangeBounds::<u32>::end_bound(&r), Bound::Excluded(&e) if e == end)
}

/// Exhausted `RangeInclusive`: the `contains` spec's exhausted branch
/// (`i.is_lt(&end)`) and `start_bound` (unchanged by exhaustion) both match
/// std. NOTE: the `end_bound` assume_spec does NOT hold for exhausted
/// ranges (std switches to `Excluded(&end)`, the spec claims `Included`
/// unconditionally) — deliberately not encoded as a harness; see
/// verus-pbt/repros/vstd_range_inclusive_end_bound.
#[cfg(not(verus_verify_core))]
#[verifier::external_body]
#[pbt]
pub fn pbt_range_inclusive_exhausted_contains(start: u8, end: u8, i: u8) -> (ret: bool)
    ensures
        ret,
{
    let mut r = RangeInclusive::new(start, end);
    while r.next().is_some() {}
    // r is now exhausted with r.start() == r.end() (when start <= end) or
    // untouched (when start > end, already empty). Either way the spec's
    // exhausted/empty semantics reduce to "contains nothing".
    let (s, e) = (*r.start(), *r.end());
    r.contains(&i) == (s <= i && i < e)
        && matches!(RangeBounds::<u8>::start_bound(&r), Bound::Included(&b) if b == s)
}

/// `RangeInclusive` `end_bound` restated on a possibly-exhausted range: the
/// assume_spec claims the result is `Included(&range@.end)` unconditionally.
/// FAILS against real std (Excluded once exhausted); see
/// verus-pbt/repros/vstd_range_inclusive_end_bound.
#[cfg(not(verus_verify_core))]
#[verifier::external_body]
#[pbt]
pub fn pbt_range_inclusive_end_bound_exhausted(start: u8, end: u8) -> (ret: bool)
    ensures
        ret,
{
    let mut r = RangeInclusive::new(start, end);
    while r.next().is_some() {}
    let e = *r.end();
    matches!(RangeBounds::<u8>::end_bound(&r), Bound::Included(&b) if b == e)
}

/// `RangeInclusive` RangeBounds (fresh construction pins the view):
/// Included(start) / Included(end).
#[cfg(not(verus_verify_core))]
#[verifier::external_body]
#[pbt]
pub fn pbt_range_inclusive_bounds(start: u32, end: u32) -> (ret: bool)
    ensures
        ret,
{
    let r = RangeInclusive::new(start, end);
    matches!(RangeBounds::<u32>::start_bound(&r), Bound::Included(&s) if s == start)
        && matches!(RangeBounds::<u32>::end_bound(&r), Bound::Included(&e) if e == end)
}

/// `RangeToInclusive` RangeBounds: Unbounded / Included(end).
#[cfg(not(verus_verify_core))]
#[verifier::external_body]
#[pbt]
pub fn pbt_range_to_inclusive_bounds(end: u32) -> (ret: bool)
    ensures
        ret,
{
    let r = ..=end;
    matches!(RangeBounds::<u32>::start_bound(&r), Bound::Unbounded)
        && matches!(RangeBounds::<u32>::end_bound(&r), Bound::Included(&e) if e == end)
}

/// `(Bound<T>, Bound<T>)` RangeBounds: each side projects its component
/// (bounds constructed from sampled selectors — `Bound` itself has no
/// sampling strategy).
#[cfg(not(verus_verify_core))]
#[verifier::external_body]
#[pbt]
pub fn pbt_bound_pair_bounds(a: u32, b: u32, sel_a: u8, sel_b: u8) -> (ret: bool)
    ensures
        ret,
{
    let mk = |v: u32, sel: u8| match sel % 3 {
        0 => Bound::Included(v),
        1 => Bound::Excluded(v),
        _ => Bound::Unbounded,
    };
    let pair = (mk(a, sel_a), mk(b, sel_b));
    let start_ok = match (RangeBounds::<u32>::start_bound(&pair), &pair.0) {
        (Bound::Included(x), Bound::Included(y)) => x == y,
        (Bound::Excluded(x), Bound::Excluded(y)) => x == y,
        (Bound::Unbounded, Bound::Unbounded) => true,
        _ => false,
    };
    let end_ok = match (RangeBounds::<u32>::end_bound(&pair), &pair.1) {
        (Bound::Included(x), Bound::Included(y)) => x == y,
        (Bound::Excluded(x), Bound::Excluded(y)) => x == y,
        (Bound::Unbounded, Bound::Unbounded) => true,
        _ => false,
    };
    start_ok && end_ok
}

} // verus!

// Per-width composite checks of the trusted `axiom_spec_range_next_*` admits
// with the `<Range<A> as Iterator>::next` assume_specification: if
// `start < end`, `next()` yields `start` and advances `start` by one;
// otherwise it yields `None` and leaves the range unchanged.
macro_rules! pbt_range_next_specs {
    ($t: ty, $f: ident) => {
        verus! {
        #[cfg(not(verus_verify_core))]
        #[verifier::external_body]
        #[pbt]
        pub fn $f(start: $t, end: $t) -> (ret: bool)
            ensures
                ret,
        {
            let mut r = start..end;
            let out = r.next();
            if start < end {
                out == Some(start) && r.start == start + 1 && r.end == end
            } else {
                out == None && r.start == start && r.end == end
            }
        }
        } // verus!
    };
}

pbt_range_next_specs!(u8, pbt_range_next_u8);
pbt_range_next_specs!(u16, pbt_range_next_u16);
pbt_range_next_specs!(u32, pbt_range_next_u32);
pbt_range_next_specs!(u64, pbt_range_next_u64);
pbt_range_next_specs!(u128, pbt_range_next_u128);
pbt_range_next_specs!(usize, pbt_range_next_usize);
pbt_range_next_specs!(i8, pbt_range_next_i8);
pbt_range_next_specs!(i16, pbt_range_next_i16);
pbt_range_next_specs!(i32, pbt_range_next_i32);
pbt_range_next_specs!(i64, pbt_range_next_i64);
pbt_range_next_specs!(i128, pbt_range_next_i128);
pbt_range_next_specs!(isize, pbt_range_next_isize);
