//! PBT experiment: a curated sweep of `#[verifier::external_body]` exec fns
//! mirroring patterns from `vstd`. Each is a trusted body whose claimed
//! behavior is the contract — Verus does not check the body, so PBT is the
//! only place where the body's actual runtime behavior gets compared to the
//! spec.
//!
//! Scope: contracts that lower cleanly through my engine today. The deeper
//! `s@.index(i as int)` / `s@.subrange(...)` / `s@.update(...)` shapes
//! depend on engine-side `Seq` method lowering that's not in the Phase-1
//! support set; they're omitted here. Future work in the engine will
//! unlock them.
//!
//! What's intentionally out of scope:
//!   - Functions with `Tracked<...>` / `Ghost<...>` parameters (refused
//!     at the harness step with a clear diagnostic).
//!   - Functions returning `&T` / `&[T]` (current limitation; adapt to a
//!     `T` / `Vec<T>` return for PBT purposes).
//!   - Iterator-returning functions (sample-able iterator types are out
//!     of scope for v1).

#[allow(unused_imports)]
use vstd::contrib::exec_spec::*;
#[allow(unused_imports)]
use vstd::contrib::verus_pbt::*;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Saturating add — mirrors the shape of vstd's `std_specs/num.rs`
// `assume_specification`s but expressed in `external_body` form.
// ---------------------------------------------------------------------------

pub open spec fn sat_add_u32_spec(a: u32, b: u32) -> u32 {
    if a as u64 + b as u64 > u32::MAX as u64 { u32::MAX } else { (a + b) as u32 }
}

#[pbt]
#[verifier::external_body]
pub fn sat_add_u32(a: u32, b: u32) -> (r: u32)
    ensures r == sat_add_u32_spec(a, b),
{
    a.saturating_add(b)
}

// ---------------------------------------------------------------------------
// Wrapping multiply.
// ---------------------------------------------------------------------------

pub open spec fn wrap_mul_u32_spec(a: u32, b: u32) -> u32 {
    ((a as u64 * b as u64) as u64 & 0xffff_ffff) as u32
}

#[pbt]
#[verifier::external_body]
pub fn wrap_mul_u32(a: u32, b: u32) -> (r: u32)
    ensures r == wrap_mul_u32_spec(a, b),
{
    a.wrapping_mul(b)
}

// ---------------------------------------------------------------------------
// Min via `<` — straightforward primitive comparison.
// ---------------------------------------------------------------------------

pub open spec fn min_u64_spec(a: u64, b: u64) -> u64 {
    if a < b { a } else { b }
}

#[pbt]
#[verifier::external_body]
pub fn min_u64(a: u64, b: u64) -> (r: u64)
    ensures r == min_u64_spec(a, b),
{
    if a < b { a } else { b }
}

// ---------------------------------------------------------------------------
// Bitwise xor + popcount-style spec. Uses the recursive popcount over u8
// to mirror how vstd specs bit operations.
// ---------------------------------------------------------------------------

pub open spec fn xor_u32_spec(a: u32, b: u32) -> u32 { a ^ b }

#[pbt]
#[verifier::external_body]
pub fn xor_u32(a: u32, b: u32) -> (r: u32)
    ensures r == xor_u32_spec(a, b),
{
    a ^ b
}

// ---------------------------------------------------------------------------
// Identity at primitive types. Trivial but exercises the
// `#[pbt]` + `external_body` + ensures pipeline end-to-end.
// ---------------------------------------------------------------------------

pub open spec fn id_u8_spec(x: u8) -> u8 { x }

#[pbt]
#[verifier::external_body]
pub fn id_u8(x: u8) -> (r: u8)
    ensures r == id_u8_spec(x),
{ x }

pub open spec fn id_bool_spec(x: bool) -> bool { x }

#[pbt]
#[verifier::external_body]
pub fn id_bool(x: bool) -> (r: bool)
    ensures r == id_bool_spec(x),
{ x }

// ---------------------------------------------------------------------------
// Vec round-trip: pushing then popping returns the same element.
// Captures the trusted-body assumption that std::vec::Vec::{push, pop}
// preserve the runtime semantics matching `Seq::push` / `Seq::last`.
// ---------------------------------------------------------------------------

pub open spec fn vec_push_pop_spec(_v: Seq<u32>, x: u32) -> u32 { x }

#[pbt]
#[verifier::external_body]
pub fn vec_push_pop(v: Vec<u32>, x: u32) -> (r: u32)
    ensures r == vec_push_pop_spec(v.deep_view(), x),
{
    let mut v = v;
    v.push(x);
    v.pop().unwrap()
}

// ---------------------------------------------------------------------------
// Slice contains-element (T = u8). Demonstrates an `exists` quantifier in
// the contract over a runtime-primitive bound variable.
// ---------------------------------------------------------------------------

pub open spec fn slice_contains_spec(s: Seq<u8>, x: u8) -> bool {
    exists |k: usize| 0 <= k < s.len() && s[k as int] == x
}

#[pbt]
#[verifier::external_body]
pub fn slice_contains_u8(s: Vec<u8>, x: u8) -> (r: bool)
    ensures r == slice_contains_spec(s.deep_view(), x),
{
    s.contains(&x)
}

// ---------------------------------------------------------------------------
// vstd::slice — `slice_index_get` at T = u8 with `&T` return.
// Demonstrates the new `&T` return-shape support.
// ---------------------------------------------------------------------------

#[pbt(T = u8)]
#[verifier::external_body]
pub exec fn slice_index_get<T>(slice: &[T], i: usize) -> (out: &T)
    requires 0 <= i < slice@.len(),
    ensures *out == slice@.index(i as int),
{
    &slice[i]
}

// ---------------------------------------------------------------------------
// Vec.update via the `Seq::update` lowering: contract written in spec
// terms gets compiled to slice-update at the harness side.
// ---------------------------------------------------------------------------

#[pbt(T = u32)]
#[verifier::external_body]
pub fn vec_set<T: Copy>(v: Vec<T>, i: usize, value: T) -> (out: Vec<T>)
    requires 0 <= i < v@.len(),
    ensures out@ == v@.update(i as int, value),
{
    let mut out = v;
    out[i] = value;
    out
}

} // verus!
