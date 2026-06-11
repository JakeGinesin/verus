//! PBT experiment: mirrors `vstd::slice` (the parts my pipeline can compile
//! today). The free-fn API on `[T]` is concrete, well-defined, and entirely
//! `external_body` — the trusted bodies are the only thing connecting the
//! spec contracts to actual runtime behavior, so PBT here directly checks
//! that connection.
//!
//! Coverage:
//!   - `slice_index_get<T>(&[T], usize) -> &T` at T = u8 (Phase-5: &T return)
//!   - `slice_to_vec<T: Copy>(&[T]) -> Vec<T>` at T = u8
//!   - `slice_subrange<T, 'a>(&'a [T], usize, usize) -> &'a [T]` at T = u8
//!     (lifetime carries through, &[T] return)
//!   - `[T]::len`, `[T]::is_empty` (via assume_specification synthesis)
//!
//! What's *not* mirrored (bookkeeping):
//!   - `SliceAdditionalSpecFns::spec_index` is a spec method on `[T]`; the
//!     engine's `Seq::index` lowering handles it through the harness
//!     contract rewrites.
//!   - `SliceAdditionalExecFns::set` requires `&mut self` which my v1
//!     harness doesn't support cleanly.
//!   - `ExSliceIndex` is a trait extension binding rustc's `SliceIndex`;
//!     out of scope for PBT.

#[allow(unused_imports)]
use vstd::contrib::exec_spec::*;
#[allow(unused_imports)]
use vstd::contrib::verus_pbt::*;
use vstd::prelude::*;

verus! {

#[pbt(T = u8)]
#[verifier::external_body]
pub exec fn slice_index_get<T: Copy>(slice: &[T], i: usize) -> (out: &T)
    requires 0 <= i < slice.view().len(),
    ensures *out == slice@.index(i as int),
{
    &slice[i]
}

#[pbt(T = u8)]
#[verifier::external_body]
pub exec fn slice_to_vec<T: Copy>(slice: &[T]) -> (out: Vec<T>)
    ensures out@ == slice@,
{
    slice.to_vec()
}

#[pbt(T = u8)]
#[verifier::external_body]
pub exec fn slice_subrange<'a, T: Copy>(slice: &'a [T], i: usize, j: usize) -> (out: &'a [T])
    requires 0 <= i <= j <= slice@.len(),
    ensures out@ == slice@.subrange(i as int, j as int),
{
    &slice[i..j]
}

// ---------------------------------------------------------------------------
// `[T]::len` and `[T]::is_empty` via assume_specification synthesis.
// ---------------------------------------------------------------------------

pub open spec fn spec_slice_is_empty<T>(slice: &[T]) -> bool {
    slice@.len() == 0
}

#[pbt(T = u8)]
pub assume_specification<T>[ <[T]>::is_empty ](slice: &[T]) -> (b: bool)
    ensures b == (slice@.len() == 0);

} // verus!
