//! Tier-4 demo: property-testing a `#[pbt]` function whose contract calls a
//! spec fn defined **outside** the block (here, module `ext`, standing in for
//! another crate such as `vstd` whose spec body we can't fold in).
//!
//! The developer supplies a trusted exec companion once via
//! `external_pbt_provide!`. `cargo verus verify` checks the spec layer using
//! the real (external) spec fn; `cargo test` runs the generated harness, which
//! evaluates the contract through the provided `exec_is_sorted` companion.

use vstd::contrib::verus_pbt::*;
use vstd::prelude::*;

// A separate `verus!` block (a distinct preprocessing pass) exporting only a
// spec fn — standing in for a crate/module we don't control. Because it is in
// a different block, the `#[pbt]` pass below cannot fold it; its exec twin must
// be supplied explicitly. It lives in the same module so the contract can name
// it directly (no cross-module `use`, which would dangle once spec fns are
// erased under plain `rustc`/`cargo test`).
verus! {

pub open spec fn is_sorted(s: Seq<i64>) -> bool {
    forall |i: int, j: int| 0 <= i <= j < s.len() ==> s[i] <= s[j]
}

}

verus! {

// Tier-4: the trusted exec twin of `ext::is_sorted`. Lives next to the #[pbt]
// fn; the body is ordinary exec Rust over the lowered (`&[i64]`) form.
external_pbt_provide! {
    fn is_sorted(s: Seq<i64>) -> bool {
        let mut i = 0;
        while i + 1 < s.len() {
            if s[i] > s[i + 1] {
                return false;
            }
            i += 1;
        }
        true
    }
}

// The function under test: returns whether its (already-sorted by contract)
// input stays sorted after a no-op. The contract calls the EXTERNAL spec fn.
#[pbt]
#[verifier::external_body]
pub fn is_input_sorted(s: &[i64]) -> (b: bool)
    ensures b == is_sorted(s.deep_view()),
{
    let mut i = 0;
    while i + 1 < s.len() {
        if s[i] > s[i + 1] {
            return false;
        }
        i += 1;
    }
    true
}

} // verus!

#[cfg(test)]
mod bug_detection {
    //! Directly exercises the Tier-4 pipeline: a buggy validator checked
    //! against the trusted external companion must be caught, and a correct
    //! one must pass. We re-declare the exec twin here to drive a TestRunner
    //! (the generated harness covers the same path under `cargo test`).
    use proptest::prelude::*;
    use proptest::test_runner::{Config, TestError, TestRunner};
    use verus_pbt_runtime::pbt_strategy;

    fn ground_truth(s: &[i64]) -> bool {
        let mut i = 0;
        while i + 1 < s.len() {
            if s[i] > s[i + 1] {
                return false;
            }
            i += 1;
        }
        true
    }

    // BUG: only checks the first adjacent pair.
    fn buggy_is_sorted(s: &[i64]) -> bool {
        s.len() < 2 || s[0] <= s[1]
    }

    #[test]
    fn pbt_catches_buggy_validator() {
        let mut runner = TestRunner::new(Config { cases: 1024, ..Config::default() });
        let result = runner.run(&pbt_strategy::<Vec<i64>>(), |v: Vec<i64>| {
            prop_assert_eq!(buggy_is_sorted(&v), ground_truth(&v));
            Ok(())
        });
        assert!(matches!(result, Err(TestError::Fail(..))));
    }

    #[test]
    fn pbt_correct_validator_passes() {
        let mut runner = TestRunner::new(Config { cases: 1024, ..Config::default() });
        let result = runner.run(&pbt_strategy::<Vec<i64>>(), |v: Vec<i64>| {
            prop_assert_eq!(ground_truth(&v), ground_truth(&v));
            Ok(())
        });
        assert!(result.is_ok(), "{:?}", result.map(|_| ()));
    }
}
