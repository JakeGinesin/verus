//! Re-exports for the [`verus_builtin_macros::verus_pbt_unverified`] and
//! [`verus_builtin_macros::verus_pbt_verified`] macros.
//!
//! The `verus_pbt_*` macros emit:
//!   1. The user's items unchanged (so Verus still verifies the spec layer).
//!   2. An `exec_spec_unverified!` (or `exec_spec_verified!`) block holding
//!      `Exec*` analogues of every spec fn / user type referenced from
//!      contracts, generated via the existing `contrib::exec_spec` engine.
//!   3. A `#[cfg(test)] #[verifier::external] mod __verus_pbt_<n> { ... }`
//!      with one `proptest!` harness per `exec` fn that has a contract.
//!
//! The runtime trait `PbtStrategy` and its impls for primitives and standard
//! collections live in the sibling `verus_pbt_runtime` crate. Consumers add
//! that crate as a `dev-dependency`; the macro-generated harness mod
//! references it as `::verus_pbt_runtime::*`.
#![cfg(all(feature = "alloc", feature = "std"))]

pub use verus_builtin_macros::verus_pbt_unverified;
pub use verus_builtin_macros::verus_pbt_verified;
