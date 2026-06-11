//! PBT experiment: validate that the trusted implementations behind
//! `<uXX>::{trailing,leading}_{zeros,ones}` match the recursive Verus spec
//! definitions in `vstd::std_specs::bits`.
//!
//! Why this matters: Verus *axiomatizes* the equivalence between the
//! recursive spec (`u8_trailing_zeros` etc.) and the LLVM intrinsic via
//! `assume_specification`. There is no SMT proof connecting the two — Verus
//! takes the equivalence on faith. PBT is the only check.
//!
//! For each integer width × {trailing, leading} × {zeros, ones} we wrap the
//! corresponding stdlib method in a free fn whose contract states equality
//! with the recursive spec, then drop `#[pbt]` on it. The macro generates a
//! proptest harness that samples the integer type and checks the equality
//! across thousands of inputs in seconds.

#[allow(unused_imports)]
use vstd::contrib::exec_spec::*;
#[allow(unused_imports)]
use vstd::contrib::verus_pbt::*;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// u8
// ---------------------------------------------------------------------------

#[pbt_provide]
pub closed spec fn u8_tz(i: u8) -> u32
    decreases i,
{
    if i == 0 { 8 }
    else if (i & 1) != 0 { 0 }
    else { (1 + u8_tz(i / 2)) as u32 }
}

#[pbt_provide]
pub closed spec fn u8_lz(i: u8) -> u32
    decreases i,
{
    if i == 0 { 8 } else { (u8_lz(i / 2) - 1) as u32 }
}

#[pbt_provide]
pub open spec fn u8_to(i: u8) -> u32 { u8_tz(!i) }

#[pbt_provide]
pub open spec fn u8_lo(i: u8) -> u32 { u8_lz(!i) }

#[pbt]
#[verifier::external_body]
pub fn pbt_u8_tz(i: u8) -> (r: u32) ensures r == u8_tz(i), { i.trailing_zeros() }

#[pbt]
#[verifier::external_body]
pub fn pbt_u8_lz(i: u8) -> (r: u32) ensures r == u8_lz(i), { i.leading_zeros() }

#[pbt]
#[verifier::external_body]
pub fn pbt_u8_to(i: u8) -> (r: u32) ensures r == u8_to(i), { i.trailing_ones() }

#[pbt]
#[verifier::external_body]
pub fn pbt_u8_lo(i: u8) -> (r: u32) ensures r == u8_lo(i), { i.leading_ones() }

// ---------------------------------------------------------------------------
// u16
// ---------------------------------------------------------------------------

#[pbt_provide]
pub closed spec fn u16_tz(i: u16) -> u32
    decreases i,
{
    if i == 0 { 16 }
    else if (i & 1) != 0 { 0 }
    else { (1 + u16_tz(i / 2)) as u32 }
}

#[pbt_provide]
pub closed spec fn u16_lz(i: u16) -> u32
    decreases i,
{
    if i == 0 { 16 } else { (u16_lz(i / 2) - 1) as u32 }
}

#[pbt_provide]
pub open spec fn u16_to(i: u16) -> u32 { u16_tz(!i) }

#[pbt_provide]
pub open spec fn u16_lo(i: u16) -> u32 { u16_lz(!i) }

#[pbt]
#[verifier::external_body]
pub fn pbt_u16_tz(i: u16) -> (r: u32) ensures r == u16_tz(i), { i.trailing_zeros() }

#[pbt]
#[verifier::external_body]
pub fn pbt_u16_lz(i: u16) -> (r: u32) ensures r == u16_lz(i), { i.leading_zeros() }

#[pbt]
#[verifier::external_body]
pub fn pbt_u16_to(i: u16) -> (r: u32) ensures r == u16_to(i), { i.trailing_ones() }

#[pbt]
#[verifier::external_body]
pub fn pbt_u16_lo(i: u16) -> (r: u32) ensures r == u16_lo(i), { i.leading_ones() }

// ---------------------------------------------------------------------------
// u32
// ---------------------------------------------------------------------------

#[pbt_provide]
pub closed spec fn u32_tz(i: u32) -> u32
    decreases i,
{
    if i == 0 { 32 }
    else if (i & 1) != 0 { 0 }
    else { (1 + u32_tz(i / 2)) as u32 }
}

#[pbt_provide]
pub closed spec fn u32_lz(i: u32) -> u32
    decreases i,
{
    if i == 0 { 32 } else { (u32_lz(i / 2) - 1) as u32 }
}

#[pbt_provide]
pub open spec fn u32_to(i: u32) -> u32 { u32_tz(!i) }

#[pbt_provide]
pub open spec fn u32_lo(i: u32) -> u32 { u32_lz(!i) }

#[pbt]
#[verifier::external_body]
pub fn pbt_u32_tz(i: u32) -> (r: u32) ensures r == u32_tz(i), { i.trailing_zeros() }

#[pbt]
#[verifier::external_body]
pub fn pbt_u32_lz(i: u32) -> (r: u32) ensures r == u32_lz(i), { i.leading_zeros() }

#[pbt]
#[verifier::external_body]
pub fn pbt_u32_to(i: u32) -> (r: u32) ensures r == u32_to(i), { i.trailing_ones() }

#[pbt]
#[verifier::external_body]
pub fn pbt_u32_lo(i: u32) -> (r: u32) ensures r == u32_lo(i), { i.leading_ones() }

// ---------------------------------------------------------------------------
// u64
// ---------------------------------------------------------------------------

#[pbt_provide]
pub closed spec fn u64_tz(i: u64) -> u32
    decreases i,
{
    if i == 0 { 64 }
    else if (i & 1) != 0 { 0 }
    else { (1 + u64_tz(i / 2)) as u32 }
}

#[pbt_provide]
pub closed spec fn u64_lz(i: u64) -> u32
    decreases i,
{
    if i == 0 { 64 } else { (u64_lz(i / 2) - 1) as u32 }
}

#[pbt_provide]
pub open spec fn u64_to(i: u64) -> u32 { u64_tz(!i) }

#[pbt_provide]
pub open spec fn u64_lo(i: u64) -> u32 { u64_lz(!i) }

#[pbt]
#[verifier::external_body]
pub fn pbt_u64_tz(i: u64) -> (r: u32) ensures r == u64_tz(i), { i.trailing_zeros() }

#[pbt]
#[verifier::external_body]
pub fn pbt_u64_lz(i: u64) -> (r: u32) ensures r == u64_lz(i), { i.leading_zeros() }

#[pbt]
#[verifier::external_body]
pub fn pbt_u64_to(i: u64) -> (r: u32) ensures r == u64_to(i), { i.trailing_ones() }

#[pbt]
#[verifier::external_body]
pub fn pbt_u64_lo(i: u64) -> (r: u32) ensures r == u64_lo(i), { i.leading_ones() }

} // verus!
