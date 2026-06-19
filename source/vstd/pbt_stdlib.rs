//! PBT-only re-declarations of stdlib `assume_specification` items.
//!
//! ## Why this module exists
//!
//! Most of vstd's contracts on Rust's standard library live in
//! `vstd::std_specs::*`. That module is gated behind
//! `#[cfg(verus_keep_ghost)]` in `vstd.rs`, which means plain `cargo build`
//! / `cargo test` (the path the PBT harness runs through) doesn't see any
//! of those items. The gate exists because the std_specs files use
//! `verifier::*` attributes, ghost-mode constructs, and other parts of the
//! verifier surface that don't compile cleanly under plain rustc.
//!
//! For PBT exploration we want to drive a subset of those items as
//! property tests. This module re-declares them in a *plain-cargo-visible*
//! location, gated `#[cfg(not(verus_keep_ghost))]` so the verifier
//! continues to see the originals (no duplicate-specification errors at
//! verification time).
//!
//! ## How the dual gating works
//!
//! - When `verus_keep_ghost` is on (verifier build / `vargo build`):
//!   - This module is gated OUT (its items don't exist).
//!   - The originals in `std_specs/*` are present.
//!   - Verifier sees one copy of each spec.
//!
//! - When `verus_keep_ghost` is off (plain cargo / PBT harness):
//!   - This module is present.
//!   - `std_specs/*` is gated out (per `vstd.rs:83`).
//!   - The plain-cargo build sees only the copies here, so they're the
//!     ones the `#[pbt]` markers attach to.
//!
//! ## Contract shape constraints
//!
//! Contracts here must be *flat expressions*, not blocks. The harness
//! emits each `ensures` clause inside `proptest::prop_assert!(...)`, which
//! routes through Rust's format-string parser. A contract like
//! `if x { a } else { b }` contains `{` braces that the format scanner
//! interprets as format placeholders, producing "invalid format string"
//! errors. Use `==>` chains and `&&`/`||` instead of `if`/`else` blocks.
//!
//! ## Adding a new target
//!
//! 1. Find the `assume_specification` item in `vstd::std_specs::*` you
//!    want to PBT.
//! 2. Copy the `assume_specification[<path>](sig) ensures/returns ...` line
//!    here, INSIDE the `verus! {}` block below.
//! 3. Reshape the contract to a flat boolean expression (no `if`/`else`
//!    blocks) — see the existing items for examples.
//! 4. Add `#[pbt]` (or `#[pbt(T = ...)]` for generics) on top.

#![cfg(not(verus_keep_ghost))]
#![cfg(all(feature = "alloc", feature = "std"))]
#[allow(unused_imports)]
use super::contrib::exec_spec::*;
use super::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Saturating arithmetic — saturate at MAX/MIN when the math would overflow.
// Contract is split into two `==>` clauses so the formatter doesn't see
// `if`/`else` braces.
// ---------------------------------------------------------------------------

#[pbt]
pub assume_specification[ u8::saturating_add ](x: u8, y: u8) -> (r: u8)
    ensures
        ((x as u16) + (y as u16) > u8::MAX as u16) ==> (r == u8::MAX),
        ((x as u16) + (y as u16) <= u8::MAX as u16) ==> (r == (x + y)),
;

#[pbt]
pub assume_specification[ u8::saturating_sub ](x: u8, y: u8) -> (r: u8)
    ensures
        (x < y) ==> (r == 0u8),
        (x >= y) ==> (r == (x - y)),
;

#[pbt]
pub assume_specification[ u16::saturating_add ](x: u16, y: u16) -> (r: u16)
    ensures
        ((x as u32) + (y as u32) > u16::MAX as u32) ==> (r == u16::MAX),
        ((x as u32) + (y as u32) <= u16::MAX as u32) ==> (r == (x + y)),
;

#[pbt]
pub assume_specification[ u16::saturating_sub ](x: u16, y: u16) -> (r: u16)
    ensures
        (x < y) ==> (r == 0u16),
        (x >= y) ==> (r == (x - y)),
;

#[pbt]
pub assume_specification[ u32::saturating_add ](x: u32, y: u32) -> (r: u32)
    ensures
        ((x as u64) + (y as u64) > u32::MAX as u64) ==> (r == u32::MAX),
        ((x as u64) + (y as u64) <= u32::MAX as u64) ==> (r == (x + y)),
;

#[pbt]
pub assume_specification[ u32::saturating_sub ](x: u32, y: u32) -> (r: u32)
    ensures
        (x < y) ==> (r == 0u32),
        (x >= y) ==> (r == (x - y)),
;

#[pbt]
pub assume_specification[ u32::saturating_mul ](x: u32, y: u32) -> (r: u32)
    ensures
        ((x as u64) * (y as u64) > u32::MAX as u64) ==> (r == u32::MAX),
        ((x as u64) * (y as u64) <= u32::MAX as u64) ==> (r == ((x as u64) * (y as u64)) as u32),
;

#[pbt]
pub assume_specification[ u64::saturating_add ](x: u64, y: u64) -> (r: u64)
    ensures
        ((x as u128) + (y as u128) > u64::MAX as u128) ==> (r == u64::MAX),
        ((x as u128) + (y as u128) <= u64::MAX as u128) ==> (r == (x + y)),
;

#[pbt]
pub assume_specification[ u64::saturating_sub ](x: u64, y: u64) -> (r: u64)
    ensures
        (x < y) ==> (r == 0u64),
        (x >= y) ==> (r == (x - y)),
;

#[pbt]
pub assume_specification[ u64::saturating_mul ](x: u64, y: u64) -> (r: u64)
    ensures
        ((x as u128) * (y as u128) > u64::MAX as u128) ==> (r == u64::MAX),
        ((x as u128) * (y as u128) <= u64::MAX as u128) ==> (r == ((x as u128) * (y as u128)) as u64),
;

// ---------------------------------------------------------------------------
// Checked arithmetic — returns Option<T>, None on overflow / division-by-zero.
// `r.is_some()` and `r.unwrap()` keep the contract a flat expression.
// ---------------------------------------------------------------------------

#[pbt]
pub assume_specification[ u32::checked_add ](x: u32, y: u32) -> (r: Option<u32>)
    ensures
        ((x as u64) + (y as u64) > u32::MAX as u64) ==> r.is_none(),
        ((x as u64) + (y as u64) <= u32::MAX as u64) ==>
            (r.is_some() && r.unwrap() == (x + y)),
;

#[pbt]
pub assume_specification[ u32::checked_sub ](x: u32, y: u32) -> (r: Option<u32>)
    ensures
        (x < y) ==> r.is_none(),
        (x >= y) ==> (r.is_some() && r.unwrap() == (x - y)),
;

#[pbt]
pub assume_specification[ u32::checked_mul ](x: u32, y: u32) -> (r: Option<u32>)
    ensures
        ((x as u64) * (y as u64) > u32::MAX as u64) ==> r.is_none(),
        ((x as u64) * (y as u64) <= u32::MAX as u64) ==>
            (r.is_some() && r.unwrap() == ((x as u64) * (y as u64)) as u32),
;

#[pbt]
pub assume_specification[ u32::checked_div ](x: u32, y: u32) -> (r: Option<u32>)
    ensures
        (y == 0) ==> r.is_none(),
        (y != 0) ==> (r.is_some() && r.unwrap() == x / y),
;

#[pbt]
pub assume_specification[ u32::checked_rem ](x: u32, y: u32) -> (r: Option<u32>)
    ensures
        (y == 0) ==> r.is_none(),
        (y != 0) ==> (r.is_some() && r.unwrap() == x % y),
;

#[pbt]
pub assume_specification[ u64::checked_add ](x: u64, y: u64) -> (r: Option<u64>)
    ensures
        ((x as u128) + (y as u128) > u64::MAX as u128) ==> r.is_none(),
        ((x as u128) + (y as u128) <= u64::MAX as u128) ==>
            (r.is_some() && r.unwrap() == (x + y)),
;

#[pbt]
pub assume_specification[ u64::checked_sub ](x: u64, y: u64) -> (r: Option<u64>)
    ensures
        (x < y) ==> r.is_none(),
        (x >= y) ==> (r.is_some() && r.unwrap() == (x - y)),
;

#[pbt]
pub assume_specification[ u64::checked_div ](x: u64, y: u64) -> (r: Option<u64>)
    ensures
        (y == 0) ==> r.is_none(),
        (y != 0) ==> (r.is_some() && r.unwrap() == x / y),
;

#[pbt]
pub assume_specification[ u64::checked_rem ](x: u64, y: u64) -> (r: Option<u64>)
    ensures
        (y == 0) ==> r.is_none(),
        (y != 0) ==> (r.is_some() && r.unwrap() == x % y),
;

// ---------------------------------------------------------------------------
// Wrapping arithmetic — modular at 2^N for u8/u16/u32. The runtime spec
// mirrors the trusted impl's behavior using the same op cast through a
// wider integer; PBT cross-checks the impl against this open-coded form.
// ---------------------------------------------------------------------------

#[pbt]
pub assume_specification[ u8::wrapping_add ](x: u8, y: u8) -> (r: u8)
    ensures
        r == ((x as u16 + y as u16) % (1u16 << 8)) as u8,
;

#[pbt]
pub assume_specification[ u8::wrapping_sub ](x: u8, y: u8) -> (r: u8)
    ensures
        r == ((x as i32 - y as i32).rem_euclid(1i32 << 8)) as u8,
;

#[pbt]
pub assume_specification[ u16::wrapping_add ](x: u16, y: u16) -> (r: u16)
    ensures
        r == ((x as u32 + y as u32) % (1u32 << 16)) as u16,
;

#[pbt]
pub assume_specification[ u16::wrapping_sub ](x: u16, y: u16) -> (r: u16)
    ensures
        r == ((x as i64 - y as i64).rem_euclid(1i64 << 16)) as u16,
;

#[pbt]
pub assume_specification[ u32::wrapping_add ](x: u32, y: u32) -> (r: u32)
    ensures
        r == ((x as u64 + y as u64) % (1u64 << 32)) as u32,
;

#[pbt]
pub assume_specification[ u32::wrapping_sub ](x: u32, y: u32) -> (r: u32)
    ensures
        r == ((x as i64 - y as i64).rem_euclid(1i64 << 32)) as u32,
;

#[pbt]
pub assume_specification[ u32::wrapping_mul ](x: u32, y: u32) -> (r: u32)
    ensures
        r == ((x as u64 * y as u64) % (1u64 << 32)) as u32,
;

// ---------------------------------------------------------------------------
// is_multiple_of — total predicate; y=0 case returns whether x is also 0.
// ---------------------------------------------------------------------------

#[pbt]
pub assume_specification[ u32::is_multiple_of ](x: u32, y: u32) -> (r: bool)
    ensures
        (y == 0) ==> (r == (x == 0)),
        (y != 0) ==> (r == (x % y == 0)),
;

#[pbt]
pub assume_specification[ u64::is_multiple_of ](x: u64, y: u64) -> (r: bool)
    ensures
        (y == 0) ==> (r == (x == 0)),
        (y != 0) ==> (r == (x % y == 0)),
;

// ---------------------------------------------------------------------------
// Trailing / leading zeros and ones — return the count as u32. Spec is
// "result equals the bit-counting answer." For u8 these have closed-form
// recursive specs in `std_specs::bits`; we mirror the *behavior* by
// deferring to the impl through a tautological contract that exercises
// the bit-counting path for every sample.
// ---------------------------------------------------------------------------

#[pbt]
pub assume_specification[ u8::trailing_zeros ](i: u8) -> (r: u32)
    ensures
        r <= 8,
        (i == 0) ==> (r == 8),
        (i & 1 != 0) ==> (r == 0),
;

#[pbt]
pub assume_specification[ u8::leading_zeros ](i: u8) -> (r: u32)
    ensures
        r <= 8,
        (i == 0) ==> (r == 8),
        (i >= 0x80) ==> (r == 0),
;

#[pbt]
pub assume_specification[ u32::trailing_zeros ](i: u32) -> (r: u32)
    ensures
        r <= 32,
        (i == 0) ==> (r == 32),
        (i & 1 != 0) ==> (r == 0),
;

#[pbt]
pub assume_specification[ u32::leading_zeros ](i: u32) -> (r: u32)
    ensures
        r <= 32,
        (i == 0) ==> (r == 32),
        (i >= 0x80000000) ==> (r == 0),
;

#[pbt]
pub assume_specification[ u64::trailing_zeros ](i: u64) -> (r: u32)
    ensures
        r <= 64,
        (i == 0) ==> (r == 64),
        (i & 1 != 0) ==> (r == 0),
;

#[pbt]
pub assume_specification[ u64::leading_zeros ](i: u64) -> (r: u32)
    ensures
        r <= 64,
        (i == 0) ==> (r == 64),
        (i >= 0x8000000000000000u64) ==> (r == 0),
;

#[pbt]
pub assume_specification[ u16::trailing_zeros ](i: u16) -> (r: u32)
    ensures
        r <= 16,
        (i == 0) ==> (r == 16),
        (i & 1 != 0) ==> (r == 0),
;

#[pbt]
pub assume_specification[ u16::leading_zeros ](i: u16) -> (r: u32)
    ensures
        r <= 16,
        (i == 0) ==> (r == 16),
        (i >= 0x8000) ==> (r == 0),
;

#[pbt]
pub assume_specification[ u128::trailing_zeros ](i: u128) -> (r: u32)
    ensures
        r <= 128,
        (i == 0) ==> (r == 128),
        (i & 1 != 0) ==> (r == 0),
;

#[pbt]
pub assume_specification[ u128::leading_zeros ](i: u128) -> (r: u32)
    ensures
        r <= 128,
        (i == 0) ==> (r == 128),
        (i >= 0x8000_0000_0000_0000_0000_0000_0000_0000u128) ==> (r == 0),
;

// ---------------------------------------------------------------------------
// Trailing / leading ONES — symmetric to the zeros counts. `(i == MAX) ==> (r == N)`
// is the all-ones edge; `(i & 1 == 0) ==> (r == 0)` for trailing; `(i < HIGH_BIT) ==> (r == 0)`
// for leading.
// ---------------------------------------------------------------------------

#[pbt]
pub assume_specification[ u8::trailing_ones ](i: u8) -> (r: u32)
    ensures
        r <= 8,
        (i == u8::MAX) ==> (r == 8),
        (i & 1 == 0) ==> (r == 0),
;

#[pbt]
pub assume_specification[ u8::leading_ones ](i: u8) -> (r: u32)
    ensures
        r <= 8,
        (i == u8::MAX) ==> (r == 8),
        (i < 0x80) ==> (r == 0),
;

#[pbt]
pub assume_specification[ u16::trailing_ones ](i: u16) -> (r: u32)
    ensures
        r <= 16,
        (i == u16::MAX) ==> (r == 16),
        (i & 1 == 0) ==> (r == 0),
;

#[pbt]
pub assume_specification[ u16::leading_ones ](i: u16) -> (r: u32)
    ensures
        r <= 16,
        (i == u16::MAX) ==> (r == 16),
        (i < 0x8000) ==> (r == 0),
;

#[pbt]
pub assume_specification[ u32::trailing_ones ](i: u32) -> (r: u32)
    ensures
        r <= 32,
        (i == u32::MAX) ==> (r == 32),
        (i & 1 == 0) ==> (r == 0),
;

#[pbt]
pub assume_specification[ u32::leading_ones ](i: u32) -> (r: u32)
    ensures
        r <= 32,
        (i == u32::MAX) ==> (r == 32),
        (i < 0x80000000) ==> (r == 0),
;

#[pbt]
pub assume_specification[ u64::trailing_ones ](i: u64) -> (r: u32)
    ensures
        r <= 64,
        (i == u64::MAX) ==> (r == 64),
        (i & 1 == 0) ==> (r == 0),
;

#[pbt]
pub assume_specification[ u64::leading_ones ](i: u64) -> (r: u32)
    ensures
        r <= 64,
        (i == u64::MAX) ==> (r == 64),
        (i < 0x8000000000000000u64) ==> (r == 0),
;

// ---------------------------------------------------------------------------
// Saturating mul on u8 / u16 — wider widths already covered above.
// ---------------------------------------------------------------------------

#[pbt]
pub assume_specification[ u8::saturating_mul ](x: u8, y: u8) -> (r: u8)
    ensures
        ((x as u16) * (y as u16) > u8::MAX as u16) ==> (r == u8::MAX),
        ((x as u16) * (y as u16) <= u8::MAX as u16) ==> (r == ((x as u16) * (y as u16)) as u8),
;

#[pbt]
pub assume_specification[ u16::saturating_mul ](x: u16, y: u16) -> (r: u16)
    ensures
        ((x as u32) * (y as u32) > u16::MAX as u32) ==> (r == u16::MAX),
        ((x as u32) * (y as u32) <= u16::MAX as u32) ==> (r == ((x as u32) * (y as u32)) as u16),
;

#[pbt]
pub assume_specification[ u128::saturating_add ](x: u128, y: u128) -> (r: u128)
    ensures
        (x > u128::MAX - y) ==> (r == u128::MAX),
        (x <= u128::MAX - y) ==> (r == x + y),
;

#[pbt]
pub assume_specification[ u128::saturating_sub ](x: u128, y: u128) -> (r: u128)
    ensures
        (x < y) ==> (r == 0u128),
        (x >= y) ==> (r == (x - y)),
;

// ---------------------------------------------------------------------------
// Checked add/sub on u8, u16, u128 — wider widths already covered.
// ---------------------------------------------------------------------------

#[pbt]
pub assume_specification[ u8::checked_add ](x: u8, y: u8) -> (r: Option<u8>)
    ensures
        ((x as u16) + (y as u16) > u8::MAX as u16) ==> r.is_none(),
        ((x as u16) + (y as u16) <= u8::MAX as u16) ==>
            (r.is_some() && r.unwrap() == (x + y)),
;

#[pbt]
pub assume_specification[ u8::checked_sub ](x: u8, y: u8) -> (r: Option<u8>)
    ensures
        (x < y) ==> r.is_none(),
        (x >= y) ==> (r.is_some() && r.unwrap() == (x - y)),
;

#[pbt]
pub assume_specification[ u8::checked_mul ](x: u8, y: u8) -> (r: Option<u8>)
    ensures
        ((x as u16) * (y as u16) > u8::MAX as u16) ==> r.is_none(),
        ((x as u16) * (y as u16) <= u8::MAX as u16) ==>
            (r.is_some() && r.unwrap() == ((x as u16) * (y as u16)) as u8),
;

#[pbt]
pub assume_specification[ u8::checked_div ](x: u8, y: u8) -> (r: Option<u8>)
    ensures
        (y == 0) ==> r.is_none(),
        (y != 0) ==> (r.is_some() && r.unwrap() == x / y),
;

#[pbt]
pub assume_specification[ u8::checked_rem ](x: u8, y: u8) -> (r: Option<u8>)
    ensures
        (y == 0) ==> r.is_none(),
        (y != 0) ==> (r.is_some() && r.unwrap() == x % y),
;

#[pbt]
pub assume_specification[ u16::checked_add ](x: u16, y: u16) -> (r: Option<u16>)
    ensures
        ((x as u32) + (y as u32) > u16::MAX as u32) ==> r.is_none(),
        ((x as u32) + (y as u32) <= u16::MAX as u32) ==>
            (r.is_some() && r.unwrap() == (x + y)),
;

#[pbt]
pub assume_specification[ u16::checked_sub ](x: u16, y: u16) -> (r: Option<u16>)
    ensures
        (x < y) ==> r.is_none(),
        (x >= y) ==> (r.is_some() && r.unwrap() == (x - y)),
;

#[pbt]
pub assume_specification[ u16::checked_mul ](x: u16, y: u16) -> (r: Option<u16>)
    ensures
        ((x as u32) * (y as u32) > u16::MAX as u32) ==> r.is_none(),
        ((x as u32) * (y as u32) <= u16::MAX as u32) ==>
            (r.is_some() && r.unwrap() == ((x as u32) * (y as u32)) as u16),
;

#[pbt]
pub assume_specification[ u16::checked_div ](x: u16, y: u16) -> (r: Option<u16>)
    ensures
        (y == 0) ==> r.is_none(),
        (y != 0) ==> (r.is_some() && r.unwrap() == x / y),
;

#[pbt]
pub assume_specification[ u16::checked_rem ](x: u16, y: u16) -> (r: Option<u16>)
    ensures
        (y == 0) ==> r.is_none(),
        (y != 0) ==> (r.is_some() && r.unwrap() == x % y),
;

#[pbt]
pub assume_specification[ u128::checked_add ](x: u128, y: u128) -> (r: Option<u128>)
    ensures
        (x > u128::MAX - y) ==> r.is_none(),
        (x <= u128::MAX - y) ==> (r.is_some() && r.unwrap() == x + y),
;

#[pbt]
pub assume_specification[ u128::checked_sub ](x: u128, y: u128) -> (r: Option<u128>)
    ensures
        (x < y) ==> r.is_none(),
        (x >= y) ==> (r.is_some() && r.unwrap() == (x - y)),
;

#[pbt]
pub assume_specification[ u128::checked_div ](x: u128, y: u128) -> (r: Option<u128>)
    ensures
        (y == 0) ==> r.is_none(),
        (y != 0) ==> (r.is_some() && r.unwrap() == x / y),
;

#[pbt]
pub assume_specification[ u128::checked_rem ](x: u128, y: u128) -> (r: Option<u128>)
    ensures
        (y == 0) ==> r.is_none(),
        (y != 0) ==> (r.is_some() && r.unwrap() == x % y),
;

// ---------------------------------------------------------------------------
// is_multiple_of — fill in the remaining widths.
// ---------------------------------------------------------------------------

#[pbt]
pub assume_specification[ u8::is_multiple_of ](x: u8, y: u8) -> (r: bool)
    ensures
        (y == 0) ==> (r == (x == 0)),
        (y != 0) ==> (r == (x % y == 0)),
;

#[pbt]
pub assume_specification[ u16::is_multiple_of ](x: u16, y: u16) -> (r: bool)
    ensures
        (y == 0) ==> (r == (x == 0)),
        (y != 0) ==> (r == (x % y == 0)),
;

#[pbt]
pub assume_specification[ u128::is_multiple_of ](x: u128, y: u128) -> (r: bool)
    ensures
        (y == 0) ==> (r == (x == 0)),
        (y != 0) ==> (r == (x % y == 0)),
;

// ---------------------------------------------------------------------------
// u128 wrapping add/sub — modular at 2^128. Avoid native `as u256`-style
// math (no such width); compare via `r + y == x` for wrapping_sub etc.
// ---------------------------------------------------------------------------

#[pbt]
pub assume_specification[ u128::wrapping_add ](x: u128, y: u128) -> (r: u128)
    ensures
        // either x+y stayed in range and r matches, or it overflowed and
        // x = MAX - r + y + 1 (i.e. r = x.wrapping_add(y) ↔ x + y ≡ r mod 2^128).
        (y == 0) ==> (r == x),
        (x <= u128::MAX - y) ==> (r == x + y),
        (x > u128::MAX - y) ==> (r < x),
;

#[pbt]
pub assume_specification[ u128::wrapping_sub ](x: u128, y: u128) -> (r: u128)
    ensures
        (y == 0) ==> (r == x),
        (x >= y) ==> (r == x - y),
        (x < y) ==> (r > x),
;

// ---------------------------------------------------------------------------
// Wrapping shifts — `wrapping_shl` masks the shift count with `bits-1`. The
// runtime spec mirrors that behaviour using the masked shift; PBT
// cross-checks against open-coded form.
// ---------------------------------------------------------------------------

#[pbt]
pub assume_specification[ u8::wrapping_shl ](x: u8, rhs: u32) -> (r: u8)
    ensures
        r == (x << (rhs & 7)),
;

#[pbt]
pub assume_specification[ u8::wrapping_shr ](x: u8, rhs: u32) -> (r: u8)
    ensures
        r == (x >> (rhs & 7)),
;

#[pbt]
pub assume_specification[ u16::wrapping_shl ](x: u16, rhs: u32) -> (r: u16)
    ensures
        r == (x << (rhs & 15)),
;

#[pbt]
pub assume_specification[ u16::wrapping_shr ](x: u16, rhs: u32) -> (r: u16)
    ensures
        r == (x >> (rhs & 15)),
;

#[pbt]
pub assume_specification[ u32::wrapping_shl ](x: u32, rhs: u32) -> (r: u32)
    ensures
        r == (x << (rhs & 31)),
;

#[pbt]
pub assume_specification[ u32::wrapping_shr ](x: u32, rhs: u32) -> (r: u32)
    ensures
        r == (x >> (rhs & 31)),
;

#[pbt]
pub assume_specification[ u64::wrapping_shl ](x: u64, rhs: u32) -> (r: u64)
    ensures
        r == (x << (rhs & 63)),
;

#[pbt]
pub assume_specification[ u64::wrapping_shr ](x: u64, rhs: u32) -> (r: u64)
    ensures
        r == (x >> (rhs & 63)),
;

// ---------------------------------------------------------------------------
// Signed integer arithmetic — proptest's primitive strategies cover i8/i16
// /i32/i64/i128 already, so we can drive these the same way as the unsigned
// variants. Edge cases for signed are MIN/MAX (overflow on negation) and
// the boundary between negative and non-negative.
// ---------------------------------------------------------------------------

#[pbt]
pub assume_specification[ i32::checked_add ](x: i32, y: i32) -> (r: Option<i32>)
    ensures
        ((x as i64) + (y as i64) > i32::MAX as i64) ==> r.is_none(),
        ((x as i64) + (y as i64) < i32::MIN as i64) ==> r.is_none(),
        ((x as i64) + (y as i64) >= i32::MIN as i64
            && (x as i64) + (y as i64) <= i32::MAX as i64) ==>
            (r.is_some() && r.unwrap() == (x + y)),
;

#[pbt]
pub assume_specification[ i32::checked_sub ](x: i32, y: i32) -> (r: Option<i32>)
    ensures
        ((x as i64) - (y as i64) > i32::MAX as i64) ==> r.is_none(),
        ((x as i64) - (y as i64) < i32::MIN as i64) ==> r.is_none(),
        ((x as i64) - (y as i64) >= i32::MIN as i64
            && (x as i64) - (y as i64) <= i32::MAX as i64) ==>
            (r.is_some() && r.unwrap() == (x - y)),
;

#[pbt]
pub assume_specification[ i32::checked_mul ](x: i32, y: i32) -> (r: Option<i32>)
    ensures
        ((x as i64) * (y as i64) > i32::MAX as i64) ==> r.is_none(),
        ((x as i64) * (y as i64) < i32::MIN as i64) ==> r.is_none(),
        ((x as i64) * (y as i64) >= i32::MIN as i64
            && (x as i64) * (y as i64) <= i32::MAX as i64) ==>
            (r.is_some() && r.unwrap() == ((x as i64) * (y as i64)) as i32),
;

#[pbt]
pub assume_specification[ i32::checked_div ](x: i32, y: i32) -> (r: Option<i32>)
    ensures
        (y == 0) ==> r.is_none(),
        // i32::MIN / -1 overflows; we explicitly reject this case.
        (x == i32::MIN && y == -1) ==> r.is_none(),
        (y != 0 && !(x == i32::MIN && y == -1)) ==>
            (r.is_some() && r.unwrap() == x / y),
;

#[pbt]
pub assume_specification[ i32::checked_rem ](x: i32, y: i32) -> (r: Option<i32>)
    ensures
        (y == 0) ==> r.is_none(),
        (x == i32::MIN && y == -1) ==> r.is_none(),
        (y != 0 && !(x == i32::MIN && y == -1)) ==>
            (r.is_some() && r.unwrap() == x % y),
;

#[pbt]
pub assume_specification[ i32::saturating_add ](x: i32, y: i32) -> (r: i32)
    ensures
        ((x as i64) + (y as i64) > i32::MAX as i64) ==> (r == i32::MAX),
        ((x as i64) + (y as i64) < i32::MIN as i64) ==> (r == i32::MIN),
        ((x as i64) + (y as i64) >= i32::MIN as i64
            && (x as i64) + (y as i64) <= i32::MAX as i64) ==>
            (r == (x + y)),
;

#[pbt]
pub assume_specification[ i32::saturating_sub ](x: i32, y: i32) -> (r: i32)
    ensures
        ((x as i64) - (y as i64) > i32::MAX as i64) ==> (r == i32::MAX),
        ((x as i64) - (y as i64) < i32::MIN as i64) ==> (r == i32::MIN),
        ((x as i64) - (y as i64) >= i32::MIN as i64
            && (x as i64) - (y as i64) <= i32::MAX as i64) ==>
            (r == (x - y)),
;

#[pbt]
pub assume_specification[ i32::saturating_mul ](x: i32, y: i32) -> (r: i32)
    ensures
        ((x as i64) * (y as i64) > i32::MAX as i64) ==> (r == i32::MAX),
        ((x as i64) * (y as i64) < i32::MIN as i64) ==> (r == i32::MIN),
        ((x as i64) * (y as i64) >= i32::MIN as i64
            && (x as i64) * (y as i64) <= i32::MAX as i64) ==>
            (r == ((x as i64) * (y as i64)) as i32),
;

#[pbt]
pub assume_specification[ i64::checked_add ](x: i64, y: i64) -> (r: Option<i64>)
    ensures
        ((x as i128) + (y as i128) > i64::MAX as i128) ==> r.is_none(),
        ((x as i128) + (y as i128) < i64::MIN as i128) ==> r.is_none(),
        ((x as i128) + (y as i128) >= i64::MIN as i128
            && (x as i128) + (y as i128) <= i64::MAX as i128) ==>
            (r.is_some() && r.unwrap() == (x + y)),
;

#[pbt]
pub assume_specification[ i64::checked_sub ](x: i64, y: i64) -> (r: Option<i64>)
    ensures
        ((x as i128) - (y as i128) > i64::MAX as i128) ==> r.is_none(),
        ((x as i128) - (y as i128) < i64::MIN as i128) ==> r.is_none(),
        ((x as i128) - (y as i128) >= i64::MIN as i128
            && (x as i128) - (y as i128) <= i64::MAX as i128) ==>
            (r.is_some() && r.unwrap() == (x - y)),
;

#[pbt]
pub assume_specification[ i64::checked_mul ](x: i64, y: i64) -> (r: Option<i64>)
    ensures
        ((x as i128) * (y as i128) > i64::MAX as i128) ==> r.is_none(),
        ((x as i128) * (y as i128) < i64::MIN as i128) ==> r.is_none(),
        ((x as i128) * (y as i128) >= i64::MIN as i128
            && (x as i128) * (y as i128) <= i64::MAX as i128) ==>
            (r.is_some() && r.unwrap() == ((x as i128) * (y as i128)) as i64),
;

#[pbt]
pub assume_specification[ i64::saturating_add ](x: i64, y: i64) -> (r: i64)
    ensures
        ((x as i128) + (y as i128) > i64::MAX as i128) ==> (r == i64::MAX),
        ((x as i128) + (y as i128) < i64::MIN as i128) ==> (r == i64::MIN),
        ((x as i128) + (y as i128) >= i64::MIN as i128
            && (x as i128) + (y as i128) <= i64::MAX as i128) ==>
            (r == (x + y)),
;

#[pbt]
pub assume_specification[ i64::saturating_sub ](x: i64, y: i64) -> (r: i64)
    ensures
        ((x as i128) - (y as i128) > i64::MAX as i128) ==> (r == i64::MAX),
        ((x as i128) - (y as i128) < i64::MIN as i128) ==> (r == i64::MIN),
        ((x as i128) - (y as i128) >= i64::MIN as i128
            && (x as i128) - (y as i128) <= i64::MAX as i128) ==>
            (r == (x - y)),
;

#[pbt]
pub assume_specification[ i8::checked_add ](x: i8, y: i8) -> (r: Option<i8>)
    ensures
        ((x as i16) + (y as i16) > i8::MAX as i16) ==> r.is_none(),
        ((x as i16) + (y as i16) < i8::MIN as i16) ==> r.is_none(),
        ((x as i16) + (y as i16) >= i8::MIN as i16
            && (x as i16) + (y as i16) <= i8::MAX as i16) ==>
            (r.is_some() && r.unwrap() == (x + y)),
;

#[pbt]
pub assume_specification[ i8::checked_sub ](x: i8, y: i8) -> (r: Option<i8>)
    ensures
        ((x as i16) - (y as i16) > i8::MAX as i16) ==> r.is_none(),
        ((x as i16) - (y as i16) < i8::MIN as i16) ==> r.is_none(),
        ((x as i16) - (y as i16) >= i8::MIN as i16
            && (x as i16) - (y as i16) <= i8::MAX as i16) ==>
            (r.is_some() && r.unwrap() == (x - y)),
;

#[pbt]
pub assume_specification[ i16::checked_add ](x: i16, y: i16) -> (r: Option<i16>)
    ensures
        ((x as i32) + (y as i32) > i16::MAX as i32) ==> r.is_none(),
        ((x as i32) + (y as i32) < i16::MIN as i32) ==> r.is_none(),
        ((x as i32) + (y as i32) >= i16::MIN as i32
            && (x as i32) + (y as i32) <= i16::MAX as i32) ==>
            (r.is_some() && r.unwrap() == (x + y)),
;

#[pbt]
pub assume_specification[ i16::checked_sub ](x: i16, y: i16) -> (r: Option<i16>)
    ensures
        ((x as i32) - (y as i32) > i16::MAX as i32) ==> r.is_none(),
        ((x as i32) - (y as i32) < i16::MIN as i32) ==> r.is_none(),
        ((x as i32) - (y as i32) >= i16::MIN as i32
            && (x as i32) - (y as i32) <= i16::MAX as i32) ==>
            (r.is_some() && r.unwrap() == (x - y)),
;

// ---------------------------------------------------------------------------
// u128 trailing/leading ones — symmetric to the zeros counts above.
// ---------------------------------------------------------------------------

#[pbt]
pub assume_specification[ u128::trailing_ones ](i: u128) -> (r: u32)
    ensures
        r <= 128,
        (i == u128::MAX) ==> (r == 128),
        (i & 1 == 0) ==> (r == 0),
;

#[pbt]
pub assume_specification[ u128::leading_ones ](i: u128) -> (r: u32)
    ensures
        r <= 128,
        (i == u128::MAX) ==> (r == 128),
        (i < 0x8000_0000_0000_0000_0000_0000_0000_0000u128) ==> (r == 0),
;

// ---------------------------------------------------------------------------
// u64 / u128 wrapping_add / wrapping_sub. Same flat-expression strategy as
// u128 above (no native wider type, so we cross-check via implications).
// ---------------------------------------------------------------------------

#[pbt]
pub assume_specification[ u64::wrapping_add ](x: u64, y: u64) -> (r: u64)
    ensures
        (y == 0) ==> (r == x),
        (x <= u64::MAX - y) ==> (r == x + y),
        (x > u64::MAX - y) ==> (r < x),
;

#[pbt]
pub assume_specification[ u64::wrapping_sub ](x: u64, y: u64) -> (r: u64)
    ensures
        (y == 0) ==> (r == x),
        (x >= y) ==> (r == x - y),
        (x < y) ==> (r > x),
;

#[pbt]
pub assume_specification[ u64::wrapping_mul ](x: u64, y: u64) -> (r: u64)
    ensures
        // r ≡ x * y (mod 2^64); we cross-check via (x as u128 * y as u128) modulo.
        r == ((x as u128) * (y as u128) % (1u128 << 64)) as u64,
;

// ---------------------------------------------------------------------------
// Signed wrapping arithmetic — `wrapping_add` and `wrapping_sub` on i32/i64.
// ---------------------------------------------------------------------------

#[pbt]
pub assume_specification[ i32::wrapping_add ](x: i32, y: i32) -> (r: i32)
    ensures
        // adding 0 is identity
        (y == 0) ==> (r == x),
        // when the sum stays in range, wrapping equals real
        ((x as i64) + (y as i64) >= i32::MIN as i64
            && (x as i64) + (y as i64) <= i32::MAX as i64) ==>
            (r == x + y),
;

#[pbt]
pub assume_specification[ i32::wrapping_sub ](x: i32, y: i32) -> (r: i32)
    ensures
        (y == 0) ==> (r == x),
        ((x as i64) - (y as i64) >= i32::MIN as i64
            && (x as i64) - (y as i64) <= i32::MAX as i64) ==>
            (r == x - y),
;

#[pbt]
pub assume_specification[ i32::wrapping_mul ](x: i32, y: i32) -> (r: i32)
    ensures
        ((x as i64) * (y as i64) >= i32::MIN as i64
            && (x as i64) * (y as i64) <= i32::MAX as i64) ==>
            (r == ((x as i64) * (y as i64)) as i32),
;

#[pbt]
pub assume_specification[ i64::wrapping_add ](x: i64, y: i64) -> (r: i64)
    ensures
        (y == 0) ==> (r == x),
        ((x as i128) + (y as i128) >= i64::MIN as i128
            && (x as i128) + (y as i128) <= i64::MAX as i128) ==>
            (r == x + y),
;

#[pbt]
pub assume_specification[ i64::wrapping_sub ](x: i64, y: i64) -> (r: i64)
    ensures
        (y == 0) ==> (r == x),
        ((x as i128) - (y as i128) >= i64::MIN as i128
            && (x as i128) - (y as i128) <= i64::MAX as i128) ==>
            (r == x - y),
;

#[pbt]
pub assume_specification[ i64::wrapping_mul ](x: i64, y: i64) -> (r: i64)
    ensures
        ((x as i128) * (y as i128) >= i64::MIN as i128
            && (x as i128) * (y as i128) <= i64::MAX as i128) ==>
            (r == ((x as i128) * (y as i128)) as i64),
;

// ---------------------------------------------------------------------------
// Signed wrapping shifts — analogous to the unsigned ones above.
// ---------------------------------------------------------------------------

#[pbt]
pub assume_specification[ i32::wrapping_shl ](x: i32, rhs: u32) -> (r: i32)
    ensures
        // shifting by zero is identity
        (rhs == 0) ==> (r == x),
;

#[pbt]
pub assume_specification[ i32::wrapping_shr ](x: i32, rhs: u32) -> (r: i32)
    ensures
        (rhs == 0) ==> (r == x),
        // arithmetic shift preserves sign for non-negative values
        (x >= 0 && rhs == 0) ==> (r >= 0),
;

#[pbt]
pub assume_specification[ i64::wrapping_shl ](x: i64, rhs: u32) -> (r: i64)
    ensures
        (rhs == 0) ==> (r == x),
;

#[pbt]
pub assume_specification[ i64::wrapping_shr ](x: i64, rhs: u32) -> (r: i64)
    ensures
        (rhs == 0) ==> (r == x),
;

// ---------------------------------------------------------------------------
// Option<T> — drive each method at concrete `T = u32`. The verifier-side
// `assume_specification<T>[ Option::<T>::... ]` uses generics; here we
// monomorphize per-target since proptest's `PbtStrategy` for `Option<T>`
// needs a concrete `T`. Contracts use flat boolean expressions.
// ---------------------------------------------------------------------------

#[pbt]
pub assume_specification[ Option::<u32>::is_some ](option: &Option<u32>) -> (b: bool)
    ensures
        b == option.is_some(),
;

#[pbt]
pub assume_specification[ Option::<u32>::is_none ](option: &Option<u32>) -> (b: bool)
    ensures
        b == option.is_none(),
;

#[pbt]
pub assume_specification[ Option::<u32>::unwrap_or ](option: Option<u32>, default: u32) -> (t: u32)
    ensures
        option.is_some() ==> (t == option.unwrap()),
        option.is_none() ==> (t == default),
;

#[pbt]
pub assume_specification[ Option::<u32>::unwrap_or_default ](option: Option<u32>) -> (t: u32)
    ensures
        option.is_some() ==> (t == option.unwrap()),
        option.is_none() ==> (t == 0u32),
;

#[pbt]
pub assume_specification[ Option::<u64>::is_some ](option: &Option<u64>) -> (b: bool)
    ensures
        b == option.is_some(),
;

#[pbt]
pub assume_specification[ Option::<u64>::is_none ](option: &Option<u64>) -> (b: bool)
    ensures
        b == option.is_none(),
;

#[pbt]
pub assume_specification[ Option::<u64>::unwrap_or ](option: Option<u64>, default: u64) -> (t: u64)
    ensures
        option.is_some() ==> (t == option.unwrap()),
        option.is_none() ==> (t == default),
;

#[pbt]
pub assume_specification[ Option::<u64>::unwrap_or_default ](option: Option<u64>) -> (t: u64)
    ensures
        option.is_some() ==> (t == option.unwrap()),
        option.is_none() ==> (t == 0u64),
;

#[pbt]
pub assume_specification[ Option::<bool>::is_some ](option: &Option<bool>) -> (b: bool)
    ensures
        b == option.is_some(),
;

#[pbt]
pub assume_specification[ Option::<bool>::unwrap_or ](option: Option<bool>, default: bool) -> (t: bool)
    ensures
        option.is_some() ==> (t == option.unwrap()),
        option.is_none() ==> (t == default),
;

#[pbt]
pub assume_specification[ Option::<i32>::is_some ](option: &Option<i32>) -> (b: bool)
    ensures
        b == option.is_some(),
;

#[pbt]
pub assume_specification[ Option::<i32>::unwrap_or ](option: Option<i32>, default: i32) -> (t: i32)
    ensures
        option.is_some() ==> (t == option.unwrap()),
        option.is_none() ==> (t == default),
;

// ---------------------------------------------------------------------------
// Vec<T> at concrete `T = u32` — the verifier-side `assume_specification`s
// use `v@` (view) and `Seq::<T>::empty()`. We rewrite contracts to
// `.is_empty()` / `.len()` calls so they're flat boolean expressions.
// ---------------------------------------------------------------------------

#[pbt]
pub assume_specification[ Vec::<u32>::new ]() -> (v: Vec<u32>)
    ensures
        v.is_empty(),
        v.len() == 0usize,
;

#[pbt]
pub assume_specification[ <Vec<u32> as core::default::Default>::default ]() -> (v: Vec<u32>)
    ensures
        v.is_empty(),
;

// `Vec::<u32>::with_capacity(usize)` is intentionally NOT included here:
// proptest's default `usize` strategy spans the whole `usize` range, and the
// PBT body allocates a buffer of that size before checking the contract.
// That randomly aborts the process with "memory allocation of N bytes failed"
// for large samples. A future custom-strategy attribute would let us bound
// the capacity sample range; until then we leave with_capacity unmarked.

#[pbt]
pub assume_specification[ <Vec<u32>>::is_empty ](v: &Vec<u32>) -> (res: bool)
    ensures
        res == (v.len() == 0),
;

#[pbt]
pub assume_specification[ Vec::<u32>::len ](vec: &Vec<u32>) -> (len: usize)
    ensures
        // tautological — we mirror the impl. The body already calls
        // `vec.len()`, so this exercises the runtime path on each sample.
        len == vec.len(),
        len <= vec.capacity(),
;

// `Vec::<u32>::as_slice` is intentionally NOT included here. The verifier-
// side spec returns `&[T]` borrowing from `&Vec<T>`; the harness wrapper
// would need an explicit lifetime annotation, which the engine doesn't
// emit for parameter-less synthesizing today.

#[pbt]
pub assume_specification[ Vec::<u8>::is_empty ](v: &Vec<u8>) -> (res: bool)
    ensures
        res == (v.len() == 0),
;

#[pbt]
pub assume_specification[ Vec::<u8>::len ](vec: &Vec<u8>) -> (len: usize)
    ensures
        len == vec.len(),
;

#[pbt]
pub assume_specification[ Vec::<bool>::is_empty ](v: &Vec<bool>) -> (res: bool)
    ensures
        res == (v.len() == 0),
;

// ---------------------------------------------------------------------------
// Trait-impl PartialOrd / PartialEq on primitives. The verifier-side specs
// have empty `requires` / `ensures` (they're "trust the impl") but the
// runtime impl is well-defined on every sample, so we add a
// tautological-but-useful contract that checks the ordering matches the
// natural integer order.
// ---------------------------------------------------------------------------

#[pbt]
pub assume_specification[ <u32 as PartialOrd<u32>>::lt ](x: &u32, y: &u32) -> (b: bool)
    ensures
        b == (x < y),
;

#[pbt]
pub assume_specification[ <u32 as PartialOrd<u32>>::le ](x: &u32, y: &u32) -> (b: bool)
    ensures
        b == (x <= y),
;

#[pbt]
pub assume_specification[ <u32 as PartialOrd<u32>>::gt ](x: &u32, y: &u32) -> (b: bool)
    ensures
        b == (x > y),
;

#[pbt]
pub assume_specification[ <u32 as PartialOrd<u32>>::ge ](x: &u32, y: &u32) -> (b: bool)
    ensures
        b == (x >= y),
;

#[pbt]
pub assume_specification[ <u32 as PartialEq<u32>>::eq ](x: &u32, y: &u32) -> (b: bool)
    ensures
        b == (x == y),
;

#[pbt]
pub assume_specification[ <u32 as PartialEq<u32>>::ne ](x: &u32, y: &u32) -> (b: bool)
    ensures
        b == (x != y),
;

#[pbt]
pub assume_specification[ <u64 as PartialOrd<u64>>::lt ](x: &u64, y: &u64) -> (b: bool)
    ensures
        b == (x < y),
;

#[pbt]
pub assume_specification[ <u64 as PartialOrd<u64>>::le ](x: &u64, y: &u64) -> (b: bool)
    ensures
        b == (x <= y),
;

#[pbt]
pub assume_specification[ <u64 as PartialEq<u64>>::eq ](x: &u64, y: &u64) -> (b: bool)
    ensures
        b == (x == y),
;

#[pbt]
pub assume_specification[ <i32 as PartialOrd<i32>>::lt ](x: &i32, y: &i32) -> (b: bool)
    ensures
        b == (x < y),
;

#[pbt]
pub assume_specification[ <i32 as PartialOrd<i32>>::le ](x: &i32, y: &i32) -> (b: bool)
    ensures
        b == (x <= y),
;

#[pbt]
pub assume_specification[ <i32 as PartialEq<i32>>::eq ](x: &i32, y: &i32) -> (b: bool)
    ensures
        b == (x == y),
;

#[pbt]
pub assume_specification[ <bool as PartialEq<bool>>::eq ](x: &bool, y: &bool) -> (b: bool)
    ensures
        b == (x == y),
;

#[pbt]
pub assume_specification[ <bool as PartialEq<bool>>::ne ](x: &bool, y: &bool) -> (b: bool)
    ensures
        b == (x != y),
;

// ---------------------------------------------------------------------------
// Result<T, E> at concrete (u32, u32) and (u32, String). Strategy builds an
// equal-weight pick between Ok and Err.
// ---------------------------------------------------------------------------

#[pbt]
pub assume_specification[ Result::<u32, u32>::is_ok ](r: &Result<u32, u32>) -> (b: bool)
    ensures
        b == r.is_ok(),
;

#[pbt]
pub assume_specification[ Result::<u32, u32>::is_err ](r: &Result<u32, u32>) -> (b: bool)
    ensures
        b == r.is_err(),
;

#[pbt]
pub assume_specification[ Result::<u32, u32>::ok ](result: Result<u32, u32>) -> (opt: Option<u32>)
    ensures
        result.is_ok() ==> (opt.is_some() && opt.unwrap() == result.clone().unwrap()),
        result.is_err() ==> opt.is_none(),
;

#[pbt]
pub assume_specification[ Result::<u32, u32>::err ](result: Result<u32, u32>) -> (opt: Option<u32>)
    ensures
        result.is_err() ==> (opt.is_some() && opt.unwrap() == result.clone().unwrap_err()),
        result.is_ok() ==> opt.is_none(),
;

#[pbt]
pub assume_specification[ Result::<u32, u32>::unwrap_or ](result: Result<u32, u32>, default: u32) -> (t: u32)
    ensures
        result.is_ok() ==> (t == result.clone().unwrap()),
        result.is_err() ==> (t == default),
;

#[pbt]
pub assume_specification[ Result::<u64, u64>::is_ok ](r: &Result<u64, u64>) -> (b: bool)
    ensures
        b == r.is_ok(),
;

#[pbt]
pub assume_specification[ Result::<u64, u64>::is_err ](r: &Result<u64, u64>) -> (b: bool)
    ensures
        b == r.is_err(),
;

#[pbt]
pub assume_specification[ Result::<u64, u64>::unwrap_or ](result: Result<u64, u64>, default: u64) -> (t: u64)
    ensures
        result.is_ok() ==> (t == result.clone().unwrap()),
        result.is_err() ==> (t == default),
;

#[pbt]
pub assume_specification[ Result::<i32, u32>::is_ok ](r: &Result<i32, u32>) -> (b: bool)
    ensures
        b == r.is_ok(),
;

// ---------------------------------------------------------------------------
// Vec<T> mutating ops via `&mut Vec<T>` parameters. The harness samples a
// Vec<T>, snapshots `__pbt_pre_<id>` before the call, then evaluates
// contracts against `old(<id>)` (the snapshot) and `<id>` (the post-call
// state) — all of this is supported by the engine's MutRef path. Engine
// does NOT need separate `final()` rewrite because the post-call value
// IS the harness binding's current value (mutated through the call).
// ---------------------------------------------------------------------------

#[pbt]
pub assume_specification[ Vec::<u32>::push ](vec: &mut Vec<u32>, value: u32)
    ensures
        vec.len() == old(vec).len() + 1,
;

#[pbt]
pub assume_specification[ Vec::<u32>::pop ](vec: &mut Vec<u32>) -> (value: Option<u32>)
    ensures
        old(vec).is_empty() ==> value.is_none(),
        !old(vec).is_empty() ==> (value.is_some() && vec.len() == old(vec).len() - 1),
;

#[pbt]
pub assume_specification[ Vec::<u32>::clear ](vec: &mut Vec<u32>)
    ensures
        vec.is_empty(),
;

#[pbt]
pub assume_specification[ Vec::<u8>::push ](vec: &mut Vec<u8>, value: u8)
    ensures
        vec.len() == old(vec).len() + 1,
;

#[pbt]
pub assume_specification[ Vec::<u8>::pop ](vec: &mut Vec<u8>) -> (value: Option<u8>)
    ensures
        old(vec).is_empty() ==> value.is_none(),
        !old(vec).is_empty() ==> (value.is_some() && vec.len() == old(vec).len() - 1),
;

#[pbt]
pub assume_specification[ Vec::<u8>::clear ](vec: &mut Vec<u8>)
    ensures
        vec.is_empty(),
;

#[pbt]
pub assume_specification[ Vec::<bool>::push ](vec: &mut Vec<bool>, value: bool)
    ensures
        vec.len() == old(vec).len() + 1,
;

// ---------------------------------------------------------------------------
// Option<T> mutating ops via `&mut Option<T>`.
// ---------------------------------------------------------------------------

#[pbt]
pub assume_specification[ Option::<u32>::take ](option: &mut Option<u32>) -> (t: Option<u32>)
    ensures
        t == old(option),
        option.is_none(),
;

#[pbt]
pub assume_specification[ Option::<u32>::replace ](option: &mut Option<u32>, value: u32) -> (old_val: Option<u32>)
    ensures
        old_val == old(option),
        option.is_some(),
        option.unwrap() == value,
;

// ---------------------------------------------------------------------------
// Trait-impl Ord::cmp / PartialOrd::partial_cmp on primitives — return Ordering.
// ---------------------------------------------------------------------------

#[pbt]
pub assume_specification[ <u32 as Ord>::cmp ](x: &u32, y: &u32) -> (o: ::core::cmp::Ordering)
    ensures
        (x < y) ==> (o == ::core::cmp::Ordering::Less),
        (x == y) ==> (o == ::core::cmp::Ordering::Equal),
        (x > y) ==> (o == ::core::cmp::Ordering::Greater),
;

#[pbt]
pub assume_specification[ <u64 as Ord>::cmp ](x: &u64, y: &u64) -> (o: ::core::cmp::Ordering)
    ensures
        (x < y) ==> (o == ::core::cmp::Ordering::Less),
        (x == y) ==> (o == ::core::cmp::Ordering::Equal),
        (x > y) ==> (o == ::core::cmp::Ordering::Greater),
;

#[pbt]
pub assume_specification[ <i32 as Ord>::cmp ](x: &i32, y: &i32) -> (o: ::core::cmp::Ordering)
    ensures
        (x < y) ==> (o == ::core::cmp::Ordering::Less),
        (x == y) ==> (o == ::core::cmp::Ordering::Equal),
        (x > y) ==> (o == ::core::cmp::Ordering::Greater),
;

#[pbt]
pub assume_specification[ <i64 as Ord>::cmp ](x: &i64, y: &i64) -> (o: ::core::cmp::Ordering)
    ensures
        (x < y) ==> (o == ::core::cmp::Ordering::Less),
        (x == y) ==> (o == ::core::cmp::Ordering::Equal),
        (x > y) ==> (o == ::core::cmp::Ordering::Greater),
;

#[pbt]
pub assume_specification[ <u8 as Ord>::cmp ](x: &u8, y: &u8) -> (o: ::core::cmp::Ordering)
    ensures
        (x < y) ==> (o == ::core::cmp::Ordering::Less),
        (x == y) ==> (o == ::core::cmp::Ordering::Equal),
        (x > y) ==> (o == ::core::cmp::Ordering::Greater),
;

// ---------------------------------------------------------------------------
// Slice / Vec accessors returning Option<&T>. The engine adapts to
// Option<T> via `.cloned()`. Contract uses `res.is_some()` etc. directly.
// ---------------------------------------------------------------------------

#[pbt]
pub assume_specification[ <[u32]>::first ](slice: &[u32]) -> (res: Option<&u32>)
    ensures
        slice.is_empty() ==> res.is_none(),
        !slice.is_empty() ==> res.is_some(),
;

#[pbt]
pub assume_specification[ <[u32]>::last ](slice: &[u32]) -> (res: Option<&u32>)
    ensures
        slice.is_empty() ==> res.is_none(),
        !slice.is_empty() ==> res.is_some(),
;

#[pbt]
pub assume_specification[ <[u8]>::first ](slice: &[u8]) -> (res: Option<&u8>)
    ensures
        slice.is_empty() ==> res.is_none(),
        !slice.is_empty() ==> res.is_some(),
;

#[pbt]
pub assume_specification[ <[u8]>::last ](slice: &[u8]) -> (res: Option<&u8>)
    ensures
        slice.is_empty() ==> res.is_none(),
        !slice.is_empty() ==> res.is_some(),
;

// ---------------------------------------------------------------------------
// More Vec mutating ops with `old()` snapshots.
// ---------------------------------------------------------------------------

#[pbt]
pub assume_specification[ Vec::<u32>::truncate ](vec: &mut Vec<u32>, len: usize)
    ensures
        // truncate to a length larger than current keeps the vec same;
        // truncate to smaller cuts to that length.
        (len >= old(vec).len()) ==> (vec.len() == old(vec).len()),
        (len < old(vec).len()) ==> (vec.len() == len),
;

#[pbt]
pub assume_specification[ Vec::<u8>::truncate ](vec: &mut Vec<u8>, len: usize)
    ensures
        (len >= old(vec).len()) ==> (vec.len() == old(vec).len()),
        (len < old(vec).len()) ==> (vec.len() == len),
;

// ---------------------------------------------------------------------------
// Tuple returns — `<[T]>::split_at` returns `(&[T], &[T])`.
// ---------------------------------------------------------------------------

#[pbt]
pub assume_specification[ <[u32]>::split_at ](slice: &[u32], mid: usize) -> (ret: (&[u32], &[u32]))
    requires
        mid <= slice.len(),
    ensures
        ret.0.len() + ret.1.len() == slice.len(),
        ret.0.len() == mid,
;

#[pbt]
pub assume_specification[ <[u8]>::split_at ](slice: &[u8], mid: usize) -> (ret: (&[u8], &[u8]))
    requires
        mid <= slice.len(),
    ensures
        ret.0.len() + ret.1.len() == slice.len(),
        ret.0.len() == mid,
;

} // verus!
