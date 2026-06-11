// PBT experiment: mirrors `vstd::std_specs::num` with adjustments for the
// engine's runtime arithmetic. vstd uses `assume_specification` to attach
// contracts to stdlib's `<uN>::{checked_*, saturating_*, wrapping_*, ...}`
// methods. Verus *axiomatizes* the equivalence — there's no SMT proof
// connecting the spec to the LLVM intrinsic. PBT validates it by running
// both.
//
// Note: my engine compiles spec `int` arithmetic to runtime `i128`, which
// preserves correctness for u32 inputs but means `x as int + y as int`
// in the spec lowers to checked arithmetic *in i128*, not unbounded math.
// The specs below use `u64` for overflow-detection arithmetic, which gives
// the same semantics for u32 inputs and compiles cleanly.

#[allow(unused_imports)]
use vstd::contrib::exec_spec::*;
#[allow(unused_imports)]
use vstd::contrib::verus_pbt::*;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// u32 — checked_*
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

pub open spec fn checked_rem_u32_spec(lhs: u32, rhs: u32) -> Option<u32> {
    if rhs == 0 { None } else { Some((lhs % rhs) as u32) }
}

#[pbt]
#[verifier::when_used_as_spec(checked_rem_u32_spec)]
pub assume_specification[ u32::checked_rem ](lhs: u32, rhs: u32) -> (r: Option<u32>)
    ensures r == checked_rem_u32_spec(lhs, rhs);

// ---------------------------------------------------------------------------
// u32 — saturating_*
// ---------------------------------------------------------------------------

pub open spec fn saturating_add_u32_spec(x: u32, y: u32) -> u32 {
    if (x as u64) + (y as u64) > u32::MAX as u64 { u32::MAX } else { (x + y) as u32 }
}

#[pbt]
#[verifier::when_used_as_spec(saturating_add_u32_spec)]
pub assume_specification[ u32::saturating_add ](x: u32, y: u32) -> (r: u32)
    ensures r == saturating_add_u32_spec(x, y);

pub open spec fn saturating_sub_u32_spec(x: u32, y: u32) -> u32 {
    if x < y { 0u32 } else { (x - y) as u32 }
}

#[pbt]
#[verifier::when_used_as_spec(saturating_sub_u32_spec)]
pub assume_specification[ u32::saturating_sub ](x: u32, y: u32) -> (r: u32)
    ensures r == saturating_sub_u32_spec(x, y);

pub open spec fn saturating_mul_u32_spec(x: u32, y: u32) -> u32 {
    if (x as u64) * (y as u64) > u32::MAX as u64 { u32::MAX } else { (x * y) as u32 }
}

#[pbt]
#[verifier::when_used_as_spec(saturating_mul_u32_spec)]
pub assume_specification[ u32::saturating_mul ](x: u32, y: u32) -> (r: u32)
    ensures r == saturating_mul_u32_spec(x, y);

} // verus!
