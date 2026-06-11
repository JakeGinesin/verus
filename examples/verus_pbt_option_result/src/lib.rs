//! PBT experiment: Option-returning helpers, mirroring patterns from
//! `vstd::std_specs::option` and `vstd::std_specs::num`. The harness
//! samples primitive inputs and validates that runtime behavior matches
//! Verus's spec for an `Option<T>` return value.
//!
//! Note on scope: vstd's `Option::is_some`-style methods take `&Option<T>`
//! parameters. The `&Option<T>` parameter shape exposes a deeper engine
//! limitation around `&Option<T>` views (no `ExecSpecType` impl for that
//! shape today). We instead PBT contracts that *return* `Option<T>` —
//! which my pipeline does support — to demonstrate the same concept.

#[allow(unused_imports)]
use vstd::contrib::exec_spec::*;
#[allow(unused_imports)]
use vstd::contrib::verus_pbt::*;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// `u32::checked_add` etc. — spec returns `Option<u32>`.
// (The same shape lives in vstd::std_specs::num.)
// ---------------------------------------------------------------------------

pub open spec fn checked_add_u32_spec(x: u32, y: u32) -> Option<u32> {
    if (x as u64) + (y as u64) > u32::MAX as u64 { None } else { Some((x + y) as u32) }
}

#[pbt]
#[verifier::when_used_as_spec(checked_add_u32_spec)]
pub assume_specification[ u32::checked_add ](x: u32, y: u32) -> (r: Option<u32>)
    ensures r == checked_add_u32_spec(x, y);

pub open spec fn checked_sub_u32_spec(x: u32, y: u32) -> Option<u32> {
    if x < y { None } else { Some((x - y) as u32) }
}

#[pbt]
#[verifier::when_used_as_spec(checked_sub_u32_spec)]
pub assume_specification[ u32::checked_sub ](x: u32, y: u32) -> (r: Option<u32>)
    ensures r == checked_sub_u32_spec(x, y);

pub open spec fn checked_mul_u32_spec(x: u32, y: u32) -> Option<u32> {
    if (x as u64) * (y as u64) > u32::MAX as u64 {
        None
    } else {
        Some((x * y) as u32)
    }
}

#[pbt]
#[verifier::when_used_as_spec(checked_mul_u32_spec)]
pub assume_specification[ u32::checked_mul ](x: u32, y: u32) -> (r: Option<u32>)
    ensures r == checked_mul_u32_spec(x, y);

pub open spec fn checked_div_u32_spec(lhs: u32, rhs: u32) -> Option<u32> {
    if rhs == 0 { None } else { Some((lhs / rhs) as u32) }
}

#[pbt]
#[verifier::when_used_as_spec(checked_div_u32_spec)]
pub assume_specification[ u32::checked_div ](lhs: u32, rhs: u32) -> (r: Option<u32>)
    ensures r == checked_div_u32_spec(lhs, rhs);

} // verus!
