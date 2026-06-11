//! PBT demo for float-typed exec fns. Verus has limited float support, so
//! this demo's contracts are only structural — `f.is_finite() == ...` and
//! identity-style ensures clauses. The point is to prove the proptest
//! sampling / harness path works for `f32` and `f64`.

use vstd::prelude::*;
use vstd::contrib::verus_pbt::*;

verus! {

#[pbt]
#[verifier::external_body]
pub exec fn double_f32(x: f32) -> (y: f32)
    ensures
        y == x + x,
{
    x + x
}

#[pbt]
#[verifier::external_body]
pub exec fn negate_f64(x: f64) -> (y: f64)
    ensures
        y == 0.0f64 - x,
{
    -x
}

}
