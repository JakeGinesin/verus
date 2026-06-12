//! Demo for `#[pbt_cov_mutate]`. Drop the attribute on a `#[pbt]`-marked
//! exec fn, run `cargo test`, and the synthesized `__pbt_mutation_report`
//! test prints a per-fn kill-rate report.
//!
//! Requires `cargo install cargo-mutants` (one-time setup). Without it
//! the report test prints a clear note and skips, so plain `cargo test`
//! still passes.

use vstd::prelude::*;
use vstd::contrib::verus_pbt::*;

verus! {

// ---------------------------------------------------------------------------
// Strong contract: the ensures clause pins down every observable byte of
// the body's behavior. cargo-mutants should report a high kill rate.
// ---------------------------------------------------------------------------

pub open spec fn spec_strong_double(x: u32) -> u32 {
    if x <= u32::MAX / 2 { (x + x) as u32 } else { 0 }
}

#[pbt_cov_mutate]
#[pbt]
#[verifier::external_body]
pub exec fn strong_double(x: u32) -> (y: u32)
    requires x <= u32::MAX / 2,
    ensures y == spec_strong_double(x),
{
    x + x
}

// ---------------------------------------------------------------------------
// Weak contract: the ensures clause only constrains the parity of the
// result. Many body mutations preserve parity, so a lot of mutants will
// survive.
// ---------------------------------------------------------------------------

pub open spec fn spec_is_even(y: u32) -> bool {
    y % 2 == 0
}

#[pbt_cov_mutate]
#[pbt]
#[verifier::external_body]
pub exec fn weak_double(x: u32) -> (y: u32)
    requires x <= u32::MAX / 2,
    ensures spec_is_even(y),
{
    x + x
}

// ---------------------------------------------------------------------------
// Larger body: triple sum. The body has 2 `+` operators yielding 2
// arith-swap sites, so the report shows 2 mutants per fn. Both contracts
// (strong + weak) cover the same body for direct comparison.
//
// Preconditions are kept tight enough that proptest's default sampling
// produces enough valid inputs (no smart sampling kicks in for
// non-collection params with relational bounds against literals on
// non-`usize` types).
// ---------------------------------------------------------------------------

pub open spec fn spec_triple_sum_u8(a: u8, b: u8, c: u8) -> u32 {
    (a as u32 + b as u32 + c as u32) as u32
}

#[pbt_cov_mutate]
#[pbt]
#[verifier::external_body]
pub exec fn triple_sum_strong(a: u8, b: u8, c: u8) -> (y: u32)
    ensures y == spec_triple_sum_u8(a, b, c),
{
    a as u32 + b as u32 + c as u32
}

#[pbt_cov_mutate]
#[pbt]
#[verifier::external_body]
pub exec fn triple_sum_weak(a: u8, b: u8, c: u8) -> (y: u32)
    ensures y >= a as u32,
{
    a as u32 + b as u32 + c as u32
}

// ---------------------------------------------------------------------------
// Bitwise body: pack two bytes. Strong contract pins down every bit, so
// the bitwise-swap operator should produce killable mutants.
// ---------------------------------------------------------------------------

pub open spec fn spec_pack_u16(hi: u8, lo: u8) -> u16 {
    (hi as u16) * 256u16 + (lo as u16)
}

#[pbt_cov_mutate]
#[pbt]
#[verifier::external_body]
pub exec fn pack_u16(hi: u8, lo: u8) -> (y: u16)
    ensures y == spec_pack_u16(hi, lo),
{
    ((hi as u16) << 8u16) | (lo as u16)
}

// ---------------------------------------------------------------------------
// ABS demo: a signed-int body the strong contract pins down. The ABS
// operator (`x → -x`) should fire on the signed param and be killed by
// the spec.
// ---------------------------------------------------------------------------

pub open spec fn spec_signed_double(x: i32) -> i32 {
    if x >= -1073741824i32 && x <= 1073741823i32 { (x + x) as i32 } else { 0i32 }
}

#[pbt_cov_mutate]
#[pbt]
#[verifier::external_body]
pub exec fn signed_double(x: i32) -> (y: i32)
    requires x >= -1073741824i32, x <= 1073741823i32,
    ensures y == spec_signed_double(x),
{
    x + x
}

}
