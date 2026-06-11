//! PBT demo for `&mut <T>` parameters and `final(...)`/`old(...)` contracts.
//!
//! Mirrors the shape of vstd `external_body` exec fns that mutate their
//! receiver — for example `String::append`, `<[T]>::set`, and the
//! `contrib::exec_spec` mirror methods. The harness samples an owned value
//! of the inner shape, snapshots its deep_view *before* the call, runs the
//! real fn (which mutates in place), then evaluates the contract using both
//! the snapshot (for `old(...)`) and the post-call binding (for `final(...)`).
//!
//! Verus requires postcondition references to `&mut` params to be
//! disambiguated with either `old(<id>)` or `final(<id>)`, so the demos
//! here use that syntax explicitly.

use vstd::prelude::*;
use vstd::contrib::verus_pbt::*;

verus! {

// ---------------------------------------------------------------------------
// `&mut Vec<T>`: append a single element.
// ---------------------------------------------------------------------------

#[pbt(T = u32)]
#[verifier::external_body]
pub exec fn vec_push<T>(v: &mut Vec<T>, x: T)
    ensures
        final(v)@ == old(v)@.push(x),
{
    v.push(x);
}

// ---------------------------------------------------------------------------
// `&mut Vec<T>`: in-place set at an index.
// ---------------------------------------------------------------------------

#[pbt(T = u32)]
#[verifier::external_body]
pub exec fn vec_set<T>(v: &mut Vec<T>, i: usize, x: T)
    requires
        i < old(v)@.len(),
    ensures
        final(v)@ == old(v)@.update(i as int, x),
{
    v[i] = x;
}

// ---------------------------------------------------------------------------
// `&mut String`: append `&str`.
// ---------------------------------------------------------------------------

#[pbt]
#[verifier::external_body]
pub exec fn string_append(s: &mut String, t: &str)
    ensures
        final(s)@ == old(s)@ + t@,
{
    s.push_str(t);
}

// ---------------------------------------------------------------------------
// `&mut Vec<T>`: clear.
// ---------------------------------------------------------------------------

#[pbt(T = u32)]
#[verifier::external_body]
pub exec fn vec_clear<T>(v: &mut Vec<T>)
    ensures
        final(v)@.len() == 0,
{
    v.clear();
}

// NOTE: `&mut self` on user-defined types verifies through Verus (the
// macro generates well-formed engine items), but the engine's auto-
// generated Exec* companions don't yet expose a `deep_clone` impl that
// the harness's `ToExecModel` lowering of `old(self).value()` expects.
// This is a separate enhancement to the exec_spec engine — out of scope
// for the Tier 2a `&mut` work here. Receivers that mutate primitive
// shapes (Vec, String, HashMap, HashSet) work today, which covers the
// bulk of the vstd `&mut` API surface.

}
