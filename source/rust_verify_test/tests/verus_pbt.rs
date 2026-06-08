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


// ---------------------------------------------------------------------------
// &self method support: contracts can live in `impl T` blocks, written
// against the user's OWN type (no Exec* anywhere).
// ---------------------------------------------------------------------------

test_verify_one_file! {
    // Fully idiomatic: spec fn + exec fn on the same user type `User`,
    // referencing each other via `self.is_valid_spec()`. No Exec* in sight.
    #[test] test_verus_pbt_idiomatic_self IMPORTS.to_string() + verus_code_str! {
        verus_pbt_unverified! {
            pub enum Permission { Read, Write, Admin, Revoked }

            pub struct User {
                pub name_len: usize,
                pub perm: Permission,
                pub quota: u64,
            }

            impl Permission {
                pub open spec fn is_revoked(&self) -> bool {
                    match self { Permission::Revoked => true, _ => false }
                }
            }

            impl User {
                pub open spec fn is_valid_spec(&self) -> bool {
                    self.name_len > 0 && !self.perm.is_revoked()
                }

                #[verifier::external_body]
                pub fn is_valid(&self) -> (b: bool)
                    ensures b == self.is_valid_spec(),
                {
                    self.name_len > 0
                }
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    // A method on `ExecUser` with a `&self` receiver should still be
    // harnessed (back-compat: explicit Exec* form is also accepted).
    #[test] test_verus_pbt_self_receiver IMPORTS.to_string() + verus_code_str! {
        verus_pbt_unverified! {
            pub struct User {
                pub name_len: usize,
                pub quota: u64,
            }

            pub open spec fn user_ok(u: User) -> bool {
                u.name_len > 0
            }

            impl ExecUser {
                #[verifier::external_body]
                pub fn is_valid(&self) -> (b: bool)
                    ensures b == user_ok(self.deep_view()),
                {
                    self.name_len > 0
                }
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    // Mixed impl block: spec methods routed to engine, exec methods kept
    // for passthrough + harness.
    #[test] test_verus_pbt_mixed_impl IMPORTS.to_string() + verus_code_str! {
        verus_pbt_unverified! {
            pub struct Counter {
                pub n: u32,
            }

            pub open spec fn small_spec(c: Counter) -> bool {
                c.n <= 100
            }

            impl ExecCounter {
                #[verifier::external_body]
                pub fn check(&self) -> (b: bool)
                    ensures b == small_spec(self.deep_view()),
                {
                    self.n <= 100
                }
            }
        }
    } => Ok(())
}

// ---------------------------------------------------------------------------
// Diagnostics for the split-across-files limitation. A verus_pbt block can
// only see items between its own braces; referencing out-of-block types or
// spec fns must produce a clear, actionable compile error.
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// Phase 1: #[pbt_provide] at the definition site (no separate macro block).
// ---------------------------------------------------------------------------

test_verify_one_file! {
    // A single #[pbt_provide] struct: the marker is stripped, the type is
    // folded into the engine block, and the spec layer still verifies.
    #[test] test_verus_pbt_provide_struct IMPORTS.to_string() + verus_code_str! {
        #[allow(unused_imports)] use vstd::contrib::verus_pbt::*;

        #[pbt_provide]
        pub struct Point {
            pub x: i64,
            pub y: i64,
        }

        impl Point {
            pub open spec fn on_diag(&self) -> bool { self.x == self.y }
        }
    } => Ok(())
}

test_verify_one_file! {
    // Two #[pbt_provide] types where one references the other as a field.
    // They must be folded into ONE engine block so the cross-type reference
    // (User.perm: Permission) compiles.
    #[test] test_verus_pbt_provide_cross_type IMPORTS.to_string() + verus_code_str! {
        #[allow(unused_imports)] use vstd::contrib::verus_pbt::*;

        #[pbt_provide]
        pub enum Permission { Read, Revoked }

        #[pbt_provide]
        pub struct User {
            pub name_len: usize,
            pub perm: Permission,
        }

        impl Permission {
            pub open spec fn is_revoked(&self) -> bool {
                match self { Permission::Revoked => true, _ => false }
            }
        }

        impl User {
            pub open spec fn is_valid_spec(&self) -> bool {
                self.name_len > 0 && !self.perm.is_revoked()
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    // #[pbt_provide] interleaved with ordinary (non-provided) items: the
    // ordinary items must pass through untouched. A spec fn the provided
    // type's method calls is itself marked #[pbt_provide] so its exec
    // companion is generated in the same block.
    #[test] test_verus_pbt_provide_interleaved IMPORTS.to_string() + verus_code_str! {
        #[allow(unused_imports)] use vstd::contrib::verus_pbt::*;

        #[pbt_provide]
        pub open spec fn helper(n: u64) -> bool { n > 0 }

        #[pbt_provide]
        pub struct Wrapper { pub n: u64 }

        impl Wrapper {
            pub open spec fn ok(&self) -> bool { helper(self.n) }
        }

        pub fn ordinary(n: u64) -> (r: u64)
            ensures r == n,
        { n }
    } => Ok(())
}

// ---------------------------------------------------------------------------
// Phase 2: #[pbt] on an exec fn, with sibling-closure analysis. The user adds
// only `#[pbt]`; the pass folds the reachable spec/type closure into one
// engine block and generates the harness.
// ---------------------------------------------------------------------------

test_verify_one_file! {
    // Method form: `#[pbt]` on `is_valid`, which references `is_valid_spec`,
    // which references `Permission::is_revoked`. The closure must pull in
    // `User`, `Permission`, and both spec methods — with no other annotation.
    #[test] test_verus_pbt_attr_method_closure IMPORTS.to_string() + verus_code_str! {
        #[allow(unused_imports)] use vstd::contrib::verus_pbt::*;

        pub enum Permission { Read, Revoked }

        pub struct User {
            pub name_len: usize,
            pub perm: Permission,
        }

        impl Permission {
            pub open spec fn is_revoked(&self) -> bool {
                match self { Permission::Revoked => true, _ => false }
            }
        }

        impl User {
            pub open spec fn is_valid_spec(&self) -> bool {
                self.name_len > 0 && !self.perm.is_revoked()
            }

            #[pbt]
            #[verifier::external_body]
            pub fn is_valid(&self) -> (b: bool)
                ensures b == self.is_valid_spec(),
            {
                self.name_len > 0 && !matches!(self.perm, Permission::Revoked)
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    // Free-fn form: `#[pbt]` on a free fn whose contract calls a sibling
    // spec fn. Closure pulls in the spec fn only.
    #[test] test_verus_pbt_attr_free_fn IMPORTS.to_string() + verus_code_str! {
        #[allow(unused_imports)] use vstd::contrib::verus_pbt::*;

        pub open spec fn is_small_spec(n: u32) -> bool { n <= 100 }

        #[pbt]
        fn clamp(n: u32) -> (r: u32)
            ensures is_small_spec(r),
        {
            if n <= 100 { n } else { 100 }
        }
    } => Ok(())
}

test_verify_one_file! {
    // Mixing `#[pbt]` with ordinary items the closure must NOT pull in. The
    // unrelated spec fn `unrelated` and exec fn `other` stay outside the
    // engine block (they aren't reachable from the contract).
    #[test] test_verus_pbt_attr_selective_closure IMPORTS.to_string() + verus_code_str! {
        #[allow(unused_imports)] use vstd::contrib::verus_pbt::*;

        pub open spec fn reachable_spec(n: u32) -> bool { n < 50 }
        pub open spec fn unrelated(n: u32) -> bool { n > 999 }

        #[pbt]
        fn capped(n: u32) -> (r: u32)
            ensures reachable_spec(r),
        {
            if n < 50 { n } else { 49 }
        }

        pub fn other(x: u32) -> (r: u32)
            ensures r == x,
        { x }
    } => Ok(())
}

// ---------------------------------------------------------------------------
// Phase 4: robustness — markers must never leak to rustc as unknown attrs.
// ---------------------------------------------------------------------------

test_verify_one_file! {
    // `#[pbt]` on a contract-less fn: no harness to generate, but the marker
    // must be stripped (not leak as an unknown attribute) and the fn must
    // still verify.
    #[test] test_verus_pbt_marker_no_contract IMPORTS.to_string() + verus_code_str! {
        #[allow(unused_imports)] use vstd::contrib::verus_pbt::*;

        #[pbt]
        pub fn identity(n: u32) -> (r: u32)
            ensures r == n,
        { n }
    } => Ok(())
}

test_verify_one_file! {
    // A `#[pbt_provide]` type with no contract-bearing exec fn anywhere:
    // marker stripped, companions generated, spec layer verifies.
    #[test] test_verus_pbt_provide_only IMPORTS.to_string() + verus_code_str! {
        #[allow(unused_imports)] use vstd::contrib::verus_pbt::*;

        #[pbt_provide]
        pub struct Gauge { pub level: u32 }

        impl Gauge {
            pub open spec fn in_range(&self) -> bool { self.level <= 1000 }
        }
    } => Ok(())
}

// ---------------------------------------------------------------------------
// Step 1: tier-aware diagnostic for external spec fns. A `#[pbt]` contract that
// calls a free spec fn defined OUTSIDE the block (no sibling, not built-in)
// cannot get an exec companion; the pass must emit an actionable error rather
// than letting the engine produce a broken `exec_<name>(..)` call.
// ---------------------------------------------------------------------------

test_verify_one_file! {
    // The contract calls `external_pred`, which is not defined in this block.
    // Expect the tier-aware diagnostic, not a raw "cannot find exec_external_pred".
    #[test] test_verus_pbt_external_spec_fn_diagnostic IMPORTS.to_string() + verus_code_str! {
        #[allow(unused_imports)] use vstd::contrib::verus_pbt::*;

        #[pbt]
        fn clamp(n: u32) -> (r: u32)
            ensures external_pred(r),
        {
            if n <= 100 { n } else { 100 }
        }
    } => Err(err) => assert_any_vir_error_msg(err, "is used in a `#[pbt]` contract but is")
}

test_verify_one_file! {
    // Path inference: a `use` brings `is_sorted` into scope from another
    // module; the diagnostic should mention the inferred path so the
    // `external_pbt_provide!`/`pbt-gen` suggestion points at the real location.
    #[test] test_verus_pbt_external_spec_fn_path_inferred IMPORTS.to_string() + verus_code_str! {
        #[allow(unused_imports)] use vstd::contrib::verus_pbt::*;
        use crate::seqlib::is_sorted;

        #[pbt]
        fn sort_it(s: &[i64]) -> (r: bool)
            ensures r == is_sorted(s.deep_view()),
        {
            let _ = s;
            true
        }
    } => Err(err) => assert_any_vir_error_msg(err, "crate::seqlib::is_sorted")
}

// ---------------------------------------------------------------------------
// Step 2: external_pbt_provide! (Tier 4 trusted stub). A `#[pbt]` contract may
// call a spec fn that is NOT defined in-block as long as a trusted exec stub is
// supplied via external_pbt_provide! in the same block. The Step-1 diagnostic
// must be suppressed and the spec layer must still verify.
// ---------------------------------------------------------------------------

test_verify_one_file! {
    // `is_small_ext` is provided as a trusted stub; the contract calls it.
    // No sibling spec fn defines it, yet the block verifies (no diagnostic).
    #[test] test_verus_pbt_external_provide_basic IMPORTS.to_string() + verus_code_str! {
        #[allow(unused_imports)] use vstd::contrib::verus_pbt::*;

        // The spec fn lives in another module (mimicking another crate). The
        // #[pbt] block imports it; its exec companion is supplied by
        // external_pbt_provide! rather than generated in-block.
        mod ext {
            use vstd::prelude::*;
            verus! {
                pub open spec fn is_small_ext(n: u32) -> bool { n <= 100 }
            }
        }

        use ext::is_small_ext;

        external_pbt_provide! {
            fn is_small_ext(n: u32) -> bool {
                n <= 100
            }
        }

        #[pbt]
        fn clamp(n: u32) -> (r: u32)
            ensures is_small_ext(r),
        {
            if n <= 100 { n } else { 100 }
        }
    } => Ok(())
}

test_verify_one_file! {
    // A provided stub over a Seq parameter (lowered to &[i64] in the
    // companion). Verifies the spec layer is untouched and the diagnostic is
    // suppressed.
    #[test] test_verus_pbt_external_provide_seq IMPORTS.to_string() + verus_code_str! {
        #[allow(unused_imports)] use vstd::contrib::verus_pbt::*;

        mod ext {
            use vstd::prelude::*;
            verus! {
                pub open spec fn nonempty_ext(s: Seq<i64>) -> bool { s.len() > 0 }
            }
        }

        use ext::nonempty_ext;

        external_pbt_provide! {
            fn nonempty_ext(s: Seq<i64>) -> bool {
                !s.is_empty()
            }
        }

        #[pbt]
        fn first_or_zero(s: &[i64]) -> (r: i64)
            requires nonempty_ext(s.deep_view()),
            ensures r == s.deep_view()[0],
        {
            s[0]
        }
    } => Ok(())
}

// ---------------------------------------------------------------------------
// Bug-fix coverage: uninterp specs, misplaced markers, `Self` returns, and
// `#[pbt_provide]` on a method inside an impl.
// ---------------------------------------------------------------------------

test_verify_one_file! {
    // An `uninterp spec fn` reached from a `#[pbt]` contract has no body the
    // engine can lower. The pass should surface a tier-aware diagnostic
    // pointing the user at the resolution options (rewrite as `open spec fn`
    // with a body, or supply an `external_pbt_provide!` stub).
    #[test] test_verus_pbt_uninterp_free_spec_diagnostic IMPORTS.to_string() + verus_code_str! {
        #[allow(unused_imports)] use vstd::contrib::verus_pbt::*;

        pub uninterp spec fn is_small_uninterp(n: u32) -> bool;

        #[pbt]
        fn clamp(n: u32) -> (r: u32)
            ensures is_small_uninterp(r),
        {
            if n <= 100 { n } else { 100 }
        }
    } => Err(err) => assert_any_vir_error_msg(err, "has no body")
}

test_verify_one_file! {
    // Same case but the uninterp spec fn lives on a user type as a method.
    // The closure pulls in `Permission` and its impl block; the diagnostic
    // must mention the qualified name.
    #[test] test_verus_pbt_uninterp_method_diagnostic IMPORTS.to_string() + verus_code_str! {
        #[allow(unused_imports)] use vstd::contrib::verus_pbt::*;

        pub enum Permission { Read, Revoked }

        impl Permission {
            pub uninterp spec fn is_revoked(&self) -> bool;
        }

        pub struct User {
            pub name_len: usize,
            pub perm: Permission,
        }

        impl User {
            pub open spec fn is_valid_spec(&self) -> bool {
                self.name_len > 0 && !self.perm.is_revoked()
            }

            #[pbt]
            #[verifier::external_body]
            pub fn is_valid(&self) -> (b: bool)
                ensures b == self.is_valid_spec(),
            {
                self.name_len > 0
            }
        }
    } => Err(err) => assert_any_vir_error_msg(err, "has no body")
}

test_verify_one_file! {
    // Even outside any `#[pbt]` contract, `#[pbt_provide]` directly on an
    // uninterp spec fn cannot be folded into a runnable companion. The
    // diagnostic must fire.
    #[test] test_verus_pbt_uninterp_pbt_provide_diagnostic IMPORTS.to_string() + verus_code_str! {
        #[allow(unused_imports)] use vstd::contrib::verus_pbt::*;

        #[pbt_provide]
        pub uninterp spec fn lonely_uninterp(n: u32) -> bool;
    } => Err(err) => assert_any_vir_error_msg(err, "has no body")
}

test_verify_one_file! {
    // `#[pbt_provide]` on an unsupported item kind (here, a `mod`) should
    // produce a clear placement error directing the user to a struct/enum/
    // free spec fn / impl method.
    #[test] test_verus_pbt_provide_on_mod IMPORTS.to_string() + verus_code_str! {
        #[allow(unused_imports)] use vstd::contrib::verus_pbt::*;

        #[pbt_provide]
        pub mod inside {
            pub fn x() {}
        }
    } => Err(err) => assert_any_vir_error_msg(err, "Move `#[pbt_provide]`")
}

test_verify_one_file! {
    // `#[pbt_provide]` on a `use` should also produce the placement error.
    #[test] test_verus_pbt_provide_on_use IMPORTS.to_string() + verus_code_str! {
        #[allow(unused_imports)] use vstd::contrib::verus_pbt::*;

        #[pbt_provide]
        pub use core::option::Option;
    } => Err(err) => assert_any_vir_error_msg(err, "Move `#[pbt_provide]`")
}

test_verify_one_file! {
    // `#[pbt_provide]` on a method inside an inherent impl: should fold the
    // surrounding impl into the engine block, giving the type companions and
    // a runnable spec method without the user having to mark the type itself.
    #[test] test_verus_pbt_provide_on_impl_method IMPORTS.to_string() + verus_code_str! {
        #[allow(unused_imports)] use vstd::contrib::verus_pbt::*;

        pub struct Counter { pub n: u32 }

        impl Counter {
            #[pbt_provide]
            pub open spec fn small(&self) -> bool { self.n <= 100 }
        }
    } => Ok(())
}

test_verify_one_file! {
    // A `#[pbt]` method whose return type is `Self` should be supported:
    // the harness must treat the return as `OwnedUserType(Counter)` and
    // generate the right strategy/converter, not bail with "unsupported
    // return type".
    #[test] test_verus_pbt_method_returns_self IMPORTS.to_string() + verus_code_str! {
        #[allow(unused_imports)] use vstd::contrib::verus_pbt::*;

        pub struct Counter { pub n: u32 }

        impl Counter {
            pub open spec fn n_spec(&self) -> u32 { self.n }

            #[pbt]
            #[verifier::external_body]
            pub fn copy(&self) -> (r: Self)
                ensures r.n == self.n_spec(),
            {
                Counter { n: self.n }
            }
        }
    } => Ok(())
}
