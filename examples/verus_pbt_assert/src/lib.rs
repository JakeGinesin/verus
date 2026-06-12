//! Demo for `#[pbt]` on inline asserts.
//!
//! Two forms are supported:
//!
//!   - **Path-form** `#[pbt] assert(P)`: the harness drives the
//!     enclosing fn with random params and panics at the assert site
//!     if `P` is false. Picks up captured locals from the enclosing
//!     scope for free.
//!
//!   - **Forall-form** `#[pbt] assert forall |x: T| P(x) by { }` (and
//!     the `... implies Q(x)` form): the harness samples `(x, ...)`
//!     directly and evaluates `P` (or `P → Q`). Tier 1 doesn't
//!     spec→exec lower the predicate, so it must use only types and
//!     fns that are valid in exec context.
//!
//! Run `cargo test` to see the per-assert tests; pass `-- --nocapture`
//! for the full proptest output.

use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Path-form: catches a body bug that the ensures clause doesn't pin
// down. `safe_div`'s ensures clause `r == spec_safe_div(num, den)` is
// strong, but the inline assert is a useful intermediate sanity check.
// ---------------------------------------------------------------------------

pub open spec fn spec_safe_div(num: u32, den: u32) -> u32 {
    if den != 0u32 { num / den } else { 0u32 }
}

#[pbt]
#[verifier::external_body]
pub exec fn safe_div(num: u32, den: u32) -> (r: u32)
    ensures r == spec_safe_div(num, den),
{
    let result = if den != 0u32 { num / den } else { 0u32 };
    // Path-form inline assert: surface a body invariant. Captures
    // `result`, `num`, `den` from the enclosing scope.
    #[pbt] assert(den == 0u32 || result <= num);
    result
}

// ---------------------------------------------------------------------------
// Forall-form on its own.
// ---------------------------------------------------------------------------

#[pbt]
#[verifier::external_body]
pub exec fn double(x: u32) -> (r: u32)
    requires x <= u32::MAX / 2,
    ensures r == (x + x) as u32,
{
    let r = x + x;
    // Forall-form: sample `w` directly. Predicate must compile as exec.
    #[pbt] assert forall |w: u32|
        w <= u32::MAX / 2u32 implies w + w == 2u32 * w by { };
    r
}

// ---------------------------------------------------------------------------
// Combined: path-form + forall-form in the same fn. Each gets its own
// `#[test]` harness independently.
// ---------------------------------------------------------------------------

#[pbt]
#[verifier::external_body]
pub exec fn triple(x: u32) -> (r: u32)
    requires x <= u32::MAX / 3,
    ensures r == (x + x + x) as u32,
{
    let r = x + x + x;
    #[pbt] assert(r >= x);
    #[pbt] assert forall |w: u32|
        w <= u32::MAX / 3u32 implies w + w + w == 3u32 * w by { };
    r
}

}
