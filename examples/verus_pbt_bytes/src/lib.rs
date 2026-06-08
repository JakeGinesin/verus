//! PBT experiment: verus_pbt's `#[pbt]` markers applied to a copy of the
//! integer / little-endian byte conversion functions from `vstd::bytes`.
//!
//! The spec layer is byte-for-byte the upstream definitions (closed/open
//! spec fns) and the `external_body` exec wrappers around stdlib's
//! `u<n>::from_le_bytes` / `to_le_bytes`. Each `#[pbt]`-tagged exec fn
//! produces a proptest harness comparing the trusted exec body's output to
//! the engine-lowered `exec_spec_*` companion of the spec fn. A drift
//! between the spec and the trusted body shows up as a proptest failure
//! with a concrete byte sequence as the counterexample.

#[allow(unused_imports)]
use vstd::contrib::exec_spec::*;
#[allow(unused_imports)]
use vstd::contrib::verus_pbt::*;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// u16 — little-endian
// ---------------------------------------------------------------------------

#[pbt_provide]
pub closed spec fn spec_u16_from_le_bytes(s: Seq<u8>) -> u16
    recommends s.len() == 2,
{
    (s[0] as u16) | (s[1] as u16) << 8
}

#[pbt_provide]
pub closed spec fn spec_u16_to_le_bytes(x: u16) -> Seq<u8> {
    seq![
        (x & 0xff) as u8,
        ((x >> 8) & 0xff) as u8,
    ]
}

// spec -> verified impl (if there are no bad patterns in the spec, i.e. Seq.all)
// verified_impl -> output ... ensures output == spec

#[pbt]
#[verifier::external_body]
pub exec fn u16_from_le_bytes(s: &[u8]) -> (x: u16)
    requires s@.len() == 2,
    ensures x == spec_u16_from_le_bytes(s@),
{
    use core::convert::TryInto;
    u16::from_be_bytes(s.try_into().unwrap())
}

#[pbt]
#[verifier::external_body]
pub exec fn u16_to_le_bytes(x: u16) -> (r: Vec<u8>)
    ensures
        r@ == spec_u16_to_le_bytes(x),
        r@.len() == 2,
{
    x.to_le_bytes().to_vec()
}

// ---------------------------------------------------------------------------
// u32 — little-endian
// ---------------------------------------------------------------------------

#[pbt_provide]
pub closed spec fn spec_u32_from_le_bytes(s: Seq<u8>) -> u32
    recommends s.len() == 4,
{
    (s[0] as u32) | (s[1] as u32) << 8 | (s[2] as u32) << 16 | (s[3] as u32) << 24
}

#[pbt_provide]
pub closed spec fn spec_u32_to_le_bytes(x: u32) -> Seq<u8> {
    seq![
        (x & 0xff) as u8,
        ((x >> 8) & 0xff) as u8,
        ((x >> 16) & 0xff) as u8,
        ((x >> 24) & 0xff) as u8,
    ]
}

#[pbt]
#[verifier::external_body]
pub exec fn u32_from_le_bytes(s: &[u8]) -> (x: u32)
    requires s@.len() == 4,
    ensures x == spec_u32_from_le_bytes(s@),
{
    use core::convert::TryInto;
    u32::from_le_bytes(s.try_into().unwrap())
}

#[pbt]
#[verifier::external_body]
pub exec fn u32_to_le_bytes(x: u32) -> (r: Vec<u8>)
    ensures
        r@ == spec_u32_to_le_bytes(x),
        r@.len() == 4,
{
    x.to_le_bytes().to_vec()
}


// ---------------------------------------------------------------------------
// u64 — little-endian
// ---------------------------------------------------------------------------

#[pbt_provide]
pub closed spec fn spec_u64_from_le_bytes(s: Seq<u8>) -> u64
    recommends s.len() == 8,
{
    (s[0] as u64) | (s[1] as u64) << 8 | (s[2] as u64) << 16 | (s[3] as u64) << 24
        | (s[4] as u64) << 32 | (s[5] as u64) << 40 | (s[6] as u64) << 48
        | (s[7] as u64) << 56
}

#[pbt_provide]
pub closed spec fn spec_u64_to_le_bytes(x: u64) -> Seq<u8> {
    seq![
        (x & 0xff) as u8,
        ((x >> 8) & 0xff) as u8,
        ((x >> 16) & 0xff) as u8,
        ((x >> 24) & 0xff) as u8,
        ((x >> 32) & 0xff) as u8,
        ((x >> 40) & 0xff) as u8,
        ((x >> 48) & 0xff) as u8,
        ((x >> 56) & 0xff) as u8,
    ]
}

#[pbt]
#[verifier::external_body]
pub exec fn u64_from_le_bytes(s: &[u8]) -> (x: u64)
    requires s@.len() == 8,
    ensures x == spec_u64_from_le_bytes(s@),
{
    use core::convert::TryInto;
    u64::from_le_bytes(s.try_into().unwrap())
}

#[pbt]
#[verifier::external_body]
pub exec fn u64_to_le_bytes(x: u64) -> (r: Vec<u8>)
    ensures
        r@ == spec_u64_to_le_bytes(x),
        r@.len() == 8,
{
    x.to_le_bytes().to_vec()
}

// ---------------------------------------------------------------------------
// u128 — little-endian
// ---------------------------------------------------------------------------

#[pbt_provide]
pub closed spec fn spec_u128_from_le_bytes(s: Seq<u8>) -> u128
    recommends s.len() == 16,
{
    (s[0] as u128) | (s[1] as u128) << 8 | (s[2] as u128) << 16 | (s[3] as u128) << 24
        | (s[4] as u128) << 32 | (s[5] as u128) << 40 | (s[6] as u128) << 48
        | (s[7] as u128) << 56 | (s[8] as u128) << 64 | (s[9] as u128) << 72
        | (s[10] as u128) << 80 | (s[11] as u128) << 88 | (s[12] as u128) << 96
        | (s[13] as u128) << 104 | (s[14] as u128) << 112 | (s[15] as u128) << 120
}

#[pbt_provide]
pub closed spec fn spec_u128_to_le_bytes(x: u128) -> Seq<u8> {
    seq![
        (x & 0xff) as u8,
        ((x >> 8) & 0xff) as u8,
        ((x >> 16) & 0xff) as u8,
        ((x >> 24) & 0xff) as u8,
        ((x >> 32) & 0xff) as u8,
        ((x >> 40) & 0xff) as u8,
        ((x >> 48) & 0xff) as u8,
        ((x >> 56) & 0xff) as u8,
        ((x >> 64) & 0xff) as u8,
        ((x >> 72) & 0xff) as u8,
        ((x >> 80) & 0xff) as u8,
        ((x >> 88) & 0xff) as u8,
        ((x >> 96) & 0xff) as u8,
        ((x >> 104) & 0xff) as u8,
        ((x >> 112) & 0xff) as u8,
        ((x >> 120) & 0xff) as u8,
    ]
}

#[pbt]
#[verifier::external_body]
pub exec fn u128_from_le_bytes(s: &[u8]) -> (x: u128)
    requires s@.len() == 16,
    ensures x == spec_u128_from_le_bytes(s@),
{
    use core::convert::TryInto;
    u128::from_le_bytes(s.try_into().unwrap())
}

#[pbt]
#[verifier::external_body]
pub exec fn u128_to_le_bytes(x: u128) -> (r: Vec<u8>)
    ensures
        r@ == spec_u128_to_le_bytes(x),
        r@.len() == 16,
{
    x.to_le_bytes().to_vec()
}

} // verus!
