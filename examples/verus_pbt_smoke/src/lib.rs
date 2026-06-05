//! End-to-end smoke test for `verus_pbt_unverified!` and
//! `verus_pbt_verified!` covering:
//!
//! - Phase 1: free fns, primitives, Vec / slice.
//! - Phase 3: user struct param, enum param.
//! - Phase 4: inline `forall` lifted into a synthetic spec fn.
//! - Phase 4: `verus_pbt_verified!` end-to-end.
//!
//! Verify with `cargo verus verify`. Run the harness with plain `cargo test`.

use vstd::contrib::exec_spec::*;
use vstd::contrib::verus_pbt::*;
use vstd::prelude::*;

verus! {

verus_pbt_unverified! {
    // ---- Phase 1: primitives + Vec ----

    spec fn small_enough(s: Seq<i64>) -> bool {
        s.len() <= 16
    }

    spec fn appended(a: Seq<i64>, b: Seq<i64>, r: Seq<i64>) -> bool {
        r.len() == a.len() + b.len()
    }

    fn append_vec(a: &[i64], b: &[i64]) -> (r: Vec<i64>)
        requires
            small_enough(a.deep_view()),
            small_enough(b.deep_view()),
        ensures
            appended(a.deep_view(), b.deep_view(), r.deep_view()),
    {
        let mut r: Vec<i64> = Vec::new();
        let mut i: usize = 0;
        while i < a.len()
            invariant
                i <= a.len(),
                r.len() == i,
            decreases a.len() - i,
        {
            r.push(a[i]);
            i += 1;
        }
        let mut j: usize = 0;
        while j < b.len()
            invariant
                j <= b.len(),
                r.len() == a.len() + j,
            decreases b.len() - j,
        {
            r.push(b[j]);
            j += 1;
        }
        r
    }

    // ---- Phase 4: inline `forall` lifted to a synthetic spec fn ----

    fn make_zeros(n: u8) -> (r: Vec<i64>)
        ensures
            r.len() == n as usize,
            forall |i: usize| 0 <= i < r.len() ==> r[i as int] == 0,
    {
        let mut v: Vec<i64> = Vec::new();
        let mut i: u8 = 0;
        while i < n
            invariant
                i <= n,
                v.len() == i as usize,
                forall |k: usize| 0 <= k < v.len() ==> v[k as int] == 0,
            decreases n - i,
        {
            v.push(0);
            i += 1;
        }
        v
    }
}

// ---- Phase 3: user struct + enum (exec fns over Exec* types) ----

verus_pbt_unverified! {
    pub struct Pair {
        pub a: u8,
        pub b: u8,
    }

    pub enum Choice {
        Left,
        Right(u32),
        Both { x: i32, y: i32 },
    }

    spec fn pair_eq(p: Pair, x: u8, y: u8) -> bool {
        p.a == x && p.b == y
    }

    fn echo_pair(p: &ExecPair) -> (r: bool)
        ensures pair_eq(p.deep_view(), p.a, p.b) == r,
    {
        true
    }

    spec fn choice_picks_zero(c: Choice) -> bool {
        match c {
            Choice::Left => true,
            Choice::Right(n) => n == 0u32,
            Choice::Both { x, y } => x == 0 && y == 0,
        }
    }

    fn always_pass(c: &ExecChoice) -> (r: bool)
        ensures r == true,
    {
        let _ = c;
        true
    }
}

// ---- Phase 4: verified flavour with a single-var bounded forall ----

verus_pbt_verified! {
    spec fn nonempty(s: Seq<i64>) -> bool {
        s.len() > 0
    }

    fn first(s: &[i64]) -> (r: i64)
        requires nonempty(s.deep_view()),
        ensures r == s.deep_view()[0],
    {
        s[0]
    }
}

} // verus!


#[cfg(test)]
mod bug_detection {
    //! Tests asserting that the PBT machinery actually catches contract
    //! violations on deliberately broken implementations.
    //!
    //! Each test:
    //!   1. Builds a `proptest::test_runner::TestRunner` directly.
    //!   2. Samples random inputs via `verus_pbt_runtime::pbt_strategy::<T>()`,
    //!      including the macro-generated `PbtStrategy` impls for `Exec*`
    //!      types in this crate.
    //!   3. Calls a deliberately broken implementation.
    //!   4. Asserts the runner returns `Err(TestError::Fail(..))`.
    //!
    //! These tests close the loop on the macro's promise: not just "the
    //! harness compiles", but "the harness rejects bad code".

    use proptest::prelude::*;
    use proptest::test_runner::{Config, TestError, TestRunner};
    use verus_pbt_runtime::pbt_strategy;

    use super::ExecChoice;
    use super::ExecPair;

    fn run<S, F>(
        strategy: S,
        body: F,
    ) -> Result<(), TestError<<S as Strategy>::Value>>
    where
        S: Strategy,
        F: Fn(<S as Strategy>::Value) -> Result<(), proptest::test_runner::TestCaseError>,
    {
        let mut runner = TestRunner::new(Config { cases: 256, ..Config::default() });
        runner.run(&strategy, body)
    }

    // -----------------------------------------------------------------
    // Phase 1: primitive contract — broken impl detected.
    // -----------------------------------------------------------------

    fn broken_add(a: u32, b: u32) -> u32 {
        let _ = b;
        a // BUG
    }

    #[test]
    fn pbt_catches_broken_add() {
        let result = run(
            (pbt_strategy::<u32>(), pbt_strategy::<u32>()).prop_filter(
                "avoid overflow",
                |&(a, b)| (a as u64) + (b as u64) <= u32::MAX as u64,
            ),
            |(a, b)| {
                let r = broken_add(a, b);
                prop_assert_eq!(r, a + b);
                Ok(())
            },
        );
        assert!(matches!(result, Err(TestError::Fail(..))), "{:?}", result.map(|_| ()));
    }

    fn correct_add(a: u32, b: u32) -> u32 {
        a.checked_add(b).unwrap_or(0)
    }

    #[test]
    fn pbt_correct_add_passes() {
        let result = run(
            (pbt_strategy::<u32>(), pbt_strategy::<u32>()).prop_filter(
                "avoid overflow",
                |&(a, b)| (a as u64) + (b as u64) <= u32::MAX as u64,
            ),
            |(a, b)| {
                let r = correct_add(a, b);
                prop_assert_eq!(r, a + b);
                Ok(())
            },
        );
        assert!(result.is_ok(), "correct_add must not be flagged: {:?}", result);
    }

    // -----------------------------------------------------------------
    // Phase 1: Vec contract — length-violating impl detected.
    // -----------------------------------------------------------------

    fn broken_append(a: Vec<i64>, b: Vec<i64>) -> Vec<i64> {
        let mut r = a;
        r.extend(b.iter().skip(1));
        r // BUG: skips first element of b
    }

    #[test]
    fn pbt_catches_broken_append_length() {
        let result = run(
            (pbt_strategy::<Vec<i64>>(), pbt_strategy::<Vec<i64>>())
                .prop_filter("non-empty b", |(_, b)| !b.is_empty()),
            |(a, b)| {
                let expected_len = a.len() + b.len();
                let r = broken_append(a, b);
                prop_assert_eq!(r.len(), expected_len);
                Ok(())
            },
        );
        assert!(matches!(result, Err(TestError::Fail(..))), "{:?}", result.map(|_| ()));
    }

    // -----------------------------------------------------------------
    // Phase 3: macro-emitted struct strategy actually samples and catches
    // a contract violation.
    // -----------------------------------------------------------------

    #[test]
    fn macro_emitted_struct_strategy_works() {
        let result = run(pbt_strategy::<ExecPair>(), |p: ExecPair| {
            // Trivially-true postcondition.
            prop_assert!(p.a == p.a && p.b == p.b);
            Ok(())
        });
        assert!(result.is_ok(), "ExecPair strategy: {:?}", result.map(|_| ()));
    }

    #[test]
    fn macro_emitted_struct_strategy_catches_bug() {
        // "spec": p.a == p.b. Buggy impl claims it always.
        fn buggy_pair_eq(p: &ExecPair) -> bool {
            let _ = p;
            true // BUG
        }
        let result = run(pbt_strategy::<ExecPair>(), |p: ExecPair| {
            let claimed = buggy_pair_eq(&p);
            let actual = p.a == p.b;
            prop_assert_eq!(claimed, actual);
            Ok(())
        });
        assert!(matches!(result, Err(TestError::Fail(..))));
    }

    // -----------------------------------------------------------------
    // Phase 3: macro-emitted enum strategy covers all variants and
    // detects classification bugs.
    // -----------------------------------------------------------------

    #[test]
    fn macro_emitted_enum_strategy_covers_variants() {
        use std::sync::Mutex;
        let counts: Mutex<(u32, u32, u32)> = Mutex::new((0, 0, 0));
        let result = run(pbt_strategy::<ExecChoice>(), |c| {
            let mut cs = counts.lock().unwrap();
            match c {
                ExecChoice::Left => cs.0 += 1,
                ExecChoice::Right(_) => cs.1 += 1,
                ExecChoice::Both { .. } => cs.2 += 1,
            }
            Ok(())
        });
        assert!(result.is_ok());
        let cs = counts.lock().unwrap();
        assert!(cs.0 > 0, "ExecChoice::Left was never sampled");
        assert!(cs.1 > 0, "ExecChoice::Right was never sampled");
        assert!(cs.2 > 0, "ExecChoice::Both was never sampled");
    }

    #[test]
    fn macro_emitted_enum_strategy_catches_bug() {
        fn buggy_label(c: &ExecChoice) -> &'static str {
            match c {
                ExecChoice::Left => "left",
                ExecChoice::Right(_) => "right",
                ExecChoice::Both { .. } => "left", // BUG
            }
        }
        let result = run(pbt_strategy::<ExecChoice>(), |c| {
            let label = buggy_label(&c);
            match c {
                ExecChoice::Left => prop_assert_eq!(label, "left"),
                ExecChoice::Right(_) => prop_assert_eq!(label, "right"),
                ExecChoice::Both { .. } => prop_assert_eq!(label, "both"),
            }
            Ok(())
        });
        assert!(matches!(result, Err(TestError::Fail(..))));
    }

    // -----------------------------------------------------------------
    // Phase 4: quantified post-condition — broken zeroing impl detected.
    // -----------------------------------------------------------------

    fn broken_make_zeros(n: u8) -> Vec<i64> {
        let mut v = Vec::with_capacity(n as usize);
        for i in 0..n {
            v.push(if i == 0 { 0 } else { i as i64 }); // BUG
        }
        v
    }

    #[test]
    fn pbt_catches_broken_make_zeros_quantified() {
        let result = run(pbt_strategy::<u8>(), |n: u8| {
            let r = broken_make_zeros(n);
            prop_assert_eq!(r.len(), n as usize);
            for (i, &v) in r.iter().enumerate() {
                prop_assert_eq!(v, 0, "element at index {} is non-zero", i);
            }
            Ok(())
        });
        assert!(matches!(result, Err(TestError::Fail(..))));
    }

    fn correct_make_zeros(n: u8) -> Vec<i64> {
        vec![0i64; n as usize]
    }

    #[test]
    fn pbt_correct_make_zeros_passes() {
        let result = run(pbt_strategy::<u8>(), |n: u8| {
            let r = correct_make_zeros(n);
            prop_assert_eq!(r.len(), n as usize);
            for &v in &r {
                prop_assert_eq!(v, 0);
            }
            Ok(())
        });
        assert!(result.is_ok());
    }
}
