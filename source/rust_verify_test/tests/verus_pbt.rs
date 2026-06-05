// Tests for the verus_pbt_unverified! and verus_pbt_verified! macros.
//
// These tests only exercise the Verus verification side of expansion: that
// the macro emits items the existing exec_spec engine accepts and that the
// resulting `verus!` block still verifies. The proptest harness mod is
// `#[cfg(test)] #[verifier::external]` so it is invisible to verification;
// running it requires `cargo verus test` against a downstream crate that
// pulls in the `verus_pbt_runtime` crate and is exercised separately.

#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

const IMPORTS: &str = code_str! {
    #[allow(unused_imports)] use vstd::prelude::*;
    #[allow(unused_imports)] use vstd::contrib::exec_spec::*;
};

test_verify_one_file! {
    // Phase 1 golden test: merge over &[i64] with a sorted predicate.
    #[test] test_verus_pbt_merge_unverified IMPORTS.to_string() + verus_code_str! {
        verus_pbt_unverified! {
            spec fn is_sorted(s: Seq<i64>) -> bool {
                forall |i: usize, j: usize|
                    0 <= i < s.len() && i <= j < s.len()
                    ==> s[i as int] <= s[j as int]
            }

            spec fn merge_post(a: Seq<i64>, b: Seq<i64>, r: Seq<i64>) -> bool {
                r.len() == a.len() + b.len()
            }

            fn merge(a: &[i64], b: &[i64]) -> (r: Vec<i64>)
                requires
                    is_sorted(a.deep_view()),
                    is_sorted(b.deep_view()),
                ensures
                    merge_post(a.deep_view(), b.deep_view(), r.deep_view()),
            {
                // Stub impl that satisfies merge_post (length-only postcondition).
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
        }
    } => Ok(())
}

test_verify_one_file! {
    // A function with no contract should not produce a harness, but should
    // still pass through cleanly for verification.
    #[test] test_verus_pbt_no_contract_passthrough IMPORTS.to_string() + verus_code_str! {
        verus_pbt_unverified! {
            spec fn always_true() -> bool { true }

            fn add_one(x: u32) -> u32 {
                if x < u32::MAX { x + 1 } else { x }
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    // Engine-side coverage: structs reachable from a contract get compiled
    // into Exec versions via the engine block, even when the user's exec
    // impls only use primitives in the contract.
    #[test] test_verus_pbt_struct_vec IMPORTS.to_string() + verus_code_str! {
        verus_pbt_unverified! {
            struct Pair {
                a: i64,
                b: i64,
            }

            spec fn pair_is_balanced(p: Pair) -> bool {
                p.a == p.b
            }

            fn count_at_most(p: &[i64], cap: u32) -> (r: u32)
                requires p.len() <= cap as usize,
                ensures r <= cap,
            {
                p.len() as u32
            }
        }
    } => Ok(())
}

// ---------------------------------------------------------------------------
// Phase 3: enums, nested types, Map/Set/Multiset, spec-only impl blocks.
// ---------------------------------------------------------------------------

test_verify_one_file! {
    // Enum used in a spec fn body. Verifies that an enum routes to the
    // engine and gets an `ExecKind` analogue.
    #[test] test_verus_pbt_enum_engine IMPORTS.to_string() + verus_code_str! {
        verus_pbt_unverified! {
            pub enum Kind {
                A,
                B(u8),
                C { x: u16, y: u16 },
            }

            spec fn kind_is_a(k: Kind) -> bool {
                match k {
                    Kind::A => true,
                    _ => false,
                }
            }

            fn pick_kind(b: bool) -> (r: u8)
                ensures r == (if b { 1u8 } else { 0u8 }),
            {
                if b { 1u8 } else { 0u8 }
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    // Vec<UserStruct> in a spec fn parameter — engine-side coverage. The
    // exec fn's parameters remain primitives so the harness can still
    // sample via runtime strategies.
    #[test] test_verus_pbt_vec_user_struct IMPORTS.to_string() + verus_code_str! {
        verus_pbt_unverified! {
            struct Pair {
                a: i64,
                b: i64,
            }

            spec fn pair_seq_balanced(s: Seq<Pair>) -> bool {
                forall |i: usize| 0 <= i < s.len() ==> s[i as int].a == s[i as int].b
            }

            fn cap(x: u32) -> (r: u32)
                ensures r <= x,
            {
                x
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    // Map / Set / Multiset references in spec fns. Engine-side path.
    #[test] test_verus_pbt_collections_engine IMPORTS.to_string() + verus_code_str! {
        use std::collections::HashMap;
        use std::collections::HashSet;

        verus_pbt_unverified! {
            spec fn map_has_zero(m: Map<u32, u32>) -> bool {
                m.dom().contains(0u32)
            }

            spec fn set_no_zero(s: Set<u32>) -> bool {
                !s.contains(0)
            }

            fn echo(x: u32) -> (r: u32)
                ensures r == x,
            {
                x
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    // Spec-only inherent impl block on a user struct. The engine emits
    // `exec_*` methods on `ExecPoint`; verification of the spec layer
    // proceeds from the original impl. We don't yet exercise an exec fn
    // calling these methods, but the impl routing alone is what this
    // verifies.
    #[test] test_verus_pbt_spec_only_impl IMPORTS.to_string() + verus_code_str! {
        verus_pbt_unverified! {
            pub struct Point {
                pub x: i64,
                pub y: i64,
            }

            impl Point {
                pub open spec fn is_origin(&self) -> bool {
                    self.x == 0 && self.y == 0
                }

                pub open spec fn under(&self, k: i64) -> bool {
                    self.x <= k && self.y <= k
                }
            }

            // A trivial exec fn so the harness has at least one entry to
            // emit; its contracts don't depend on the impl methods.
            fn add(a: u32, b: u32) -> (r: u32)
                requires a as u64 + b as u64 <= u32::MAX as u64,
                ensures r == a + b,
            {
                a + b
            }
        }
    } => Ok(())
}

// ---------------------------------------------------------------------------
// Phase 4: inline forall / exists in clauses.
// ---------------------------------------------------------------------------

test_verify_one_file! {
    // An inline `forall` in `requires`. The macro lifts the clause into a
    // synthetic spec fn `__pbt_clause_<fn>_<n>` so the engine handles the
    // bounded quantifier compilation.
    #[test] test_verus_pbt_inline_forall_requires IMPORTS.to_string() + verus_code_str! {
        verus_pbt_unverified! {
            fn all_zero(s: &[i64]) -> (r: bool)
                requires
                    forall |i: usize| 0 <= i < s.len() ==> s[i as int] == 0,
                ensures
                    r == true,
            {
                let _ = s;
                true
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    // Inline `forall` in `ensures` referencing the result.
    #[test] test_verus_pbt_inline_forall_ensures IMPORTS.to_string() + verus_code_str! {
        verus_pbt_unverified! {
            fn zeroed(n: u32) -> (r: Vec<i64>)
                requires n <= 16,
                ensures
                    r.len() == n,
                    forall |i: usize| 0 <= i < r.len() ==> r[i as int] == 0,
            {
                let mut v: Vec<i64> = Vec::new();
                let mut i: u32 = 0;
                while i < n
                    invariant
                        i <= n,
                        v.len() == i,
                        forall |k: usize| 0 <= k < v.len() ==> v[k as int] == 0,
                    decreases n - i,
                {
                    v.push(0);
                    i += 1;
                }
                v
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    // Inline `exists` in `requires`.
    #[test] test_verus_pbt_inline_exists_requires IMPORTS.to_string() + verus_code_str! {
        verus_pbt_unverified! {
            fn echo_if_has_zero(s: &[i64]) -> (r: i64)
                requires
                    exists |i: usize| 0 <= i < s.len() && s[i as int] == 0,
                ensures
                    r == 0,
            {
                let _ = s;
                0
            }
        }
    } => Ok(())
}

// ---------------------------------------------------------------------------
// Phase 4: verus_pbt_verified! end-to-end.
// ---------------------------------------------------------------------------

test_verify_one_file! {
    // The verified flavour: the engine PROVES spec ≡ exec via SMT, so the
    // spec must live within the verified-fragment (single-var bounded
    // forall over primitive integer types only).
    #[test] test_verus_pbt_verified_basic IMPORTS.to_string() + verus_code_str! {
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
    } => Ok(())
}

test_verify_one_file! {
    // Verified flavour with a single-var bounded forall — within the
    // engine's verified fragment.
    #[test] test_verus_pbt_verified_forall IMPORTS.to_string() + verus_code_str! {
        verus_pbt_verified! {
            spec fn all_under(s: Seq<u32>, k: u32) -> bool {
                forall |i: usize| 0 <= i < s.len() ==> s[i as int] <= k
            }

            fn under_check(s: &[u32], cap: u32) -> (r: u32)
                requires all_under(s.deep_view(), cap),
                ensures r <= cap,
            {
                cap
            }
        }
    } => Ok(())
}
