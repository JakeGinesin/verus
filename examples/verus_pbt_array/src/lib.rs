//! PBT demo for vstd's array external_body fns.
//!
//! Exercises the const-generic instantiation feature: each `#[pbt(N = 4)]`
//! tells the closure pass to monomorphize `[T; N]` to a concrete length, so
//! the harness can sample fixed-size arrays and check the contract against
//! the array's `Seq<T>` view.

#![cfg_attr(verus_keep_ghost, feature(allocator_api))]

use vstd::prelude::*;
use vstd::contrib::verus_pbt::*;

verus! {

// ---------------------------------------------------------------------------
// Array indexing — mirrors `vstd::array::array_index_get`.
//
// The signature `fn array_index_get<T, const N: usize>(ar: &[T; N], i: usize)
// -> &T` carries one type param and one const param. `#[pbt(T = u32, N = 4)]`
// instantiates both.
//
// The contract reads `i < N` (index in bounds) and `*out == ar@.index(i as
// int)` (returned ref equals the i'th element). After substitution the
// array is fixed-size, the Vec strategy samples exactly 4 elements, and
// `ar@.index(i as int)` lowers to indexing the slice.
// ---------------------------------------------------------------------------

#[pbt(T = u32, N = 4)]
pub exec fn array_index_get<T: Copy, const N: usize>(ar: &[T; N], i: usize) -> (out: T)
    requires
        i < N,
    ensures
        out == ar@.index(i as int),
{
    ar[i]
}

// ---------------------------------------------------------------------------
// Array reflection through `as_slice` — mirrors `array_as_slice` shape.
// Returns `&[T]` so we exercise the RefSlice path on the return side.
// ---------------------------------------------------------------------------

#[pbt(T = u8, N = 8)]
pub exec fn array_as_slice<T, const N: usize>(ar: &[T; N]) -> (out: &[T])
    ensures
        out@.len() == N,
{
    ar
}

// ---------------------------------------------------------------------------
// Owned array round-trip. Demonstrates `OwnedArray` on the return side too
// (the param accepts `[T; N]` by value and the result is the same).
// ---------------------------------------------------------------------------

#[pbt(T = i32, N = 3)]
pub exec fn array_clone<T: Copy, const N: usize>(ar: [T; N]) -> (out: [T; N])
    ensures
        out@ == ar@,
{
    ar
}

}
