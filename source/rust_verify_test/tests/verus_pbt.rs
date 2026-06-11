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

// ---------------------------------------------------------------------------
// Generics support: instantiation via #[pbt(K = T, ...)], inheritance to
// downstream #[pbt_provide]s, and conflict diagnostics.
// ---------------------------------------------------------------------------

test_verify_one_file! {
    // A generic struct + spec method, inherited via a #[pbt(V = u64)] on the
    // exec method that uses it. The provider has no marker args; the
    // instantiation is derived from the call graph.
    #[test] test_verus_pbt_generic_struct_inherited IMPORTS.to_string() + verus_code_str! {
        #[allow(unused_imports)] use vstd::contrib::verus_pbt::*;

        #[pbt_provide]
        pub struct Cell<V> { pub value: V }

        impl<V> Cell<V> {
            pub open spec fn nonzero_spec(&self) -> bool
                where V: core::cmp::PartialEq<u64> + Copy,
            { true }
        }

        impl Cell<u64> {
            #[pbt(V = u64)]
            #[verifier::external_body]
            pub fn nonzero(&self) -> (b: bool)
                ensures b == self.nonzero_spec(),
            { self.value > 0 }
        }
    } => Ok(())
}

test_verify_one_file! {
    // A generic free `#[pbt]` fn with explicit instantiation. The function's
    // own type parameter gets substituted; rustc compiles the resulting
    // monomorphic harness.
    #[test] test_verus_pbt_generic_free_fn_explicit IMPORTS.to_string() + verus_code_str! {
        #[allow(unused_imports)] use vstd::contrib::verus_pbt::*;

        pub open spec fn nonzero<T>(_x: T) -> bool { true }

        #[pbt(T = u32)]
        fn check<T>(x: T) -> (r: bool)
            ensures r == nonzero(x),
        { let _ = x; true }
    } => Ok(())
}

test_verify_one_file! {
    // Generic `#[pbt]` fn with NO instantiation supplied: pass should emit
    // an actionable diagnostic suggesting a concrete type.
    #[test] test_verus_pbt_generic_unbound_diagnostic IMPORTS.to_string() + verus_code_str! {
        #[allow(unused_imports)] use vstd::contrib::verus_pbt::*;

        #[pbt]
        fn id<T>(x: T) -> (r: T)
            ensures true,
        { x }
    } => Err(err) => assert_any_vir_error_msg(err, "is generic in <T>")
}

test_verify_one_file! {
    // The unbound-instantiation diagnostic should always include a concrete
    // suggestion the user can paste back as a fix.
    #[test] test_verus_pbt_generic_unbound_suggests_input IMPORTS.to_string() + verus_code_str! {
        #[allow(unused_imports)] use vstd::contrib::verus_pbt::*;

        #[pbt]
        fn id<T>(x: T) -> (r: T)
            ensures true,
        { x }
    } => Err(err) => assert_any_vir_error_msg(err, "T = u32")
}

test_verify_one_file! {
    // Two #[pbt] callsites that both reach the same generic provider — at
    // *different* instantiations — must be rejected with a conflict
    // diagnostic naming the disagreement.
    #[test] test_verus_pbt_generic_conflict_diagnostic IMPORTS.to_string() + verus_code_str! {
        #[allow(unused_imports)] use vstd::contrib::verus_pbt::*;

        pub open spec fn id<T>(_x: T) -> bool { true }

        #[pbt(T = u32)]
        fn check_u32<T>(x: T) -> (r: bool) ensures r == id(x), { let _ = x; true }

        #[pbt(T = i64)]
        fn check_i64<T>(x: T) -> (r: bool) ensures r == id(x), { let _ = x; true }
    } => Err(err) => assert_any_vir_error_msg(err, "conflicting instantiations")
}

test_verify_one_file! {
    // Free fn with a lifetime parameter only (no type params): no
    // instantiation needed, should pass through cleanly.
    #[test] test_verus_pbt_lifetime_only IMPORTS.to_string() + verus_code_str! {
        #[allow(unused_imports)] use vstd::contrib::verus_pbt::*;

        #[pbt]
        fn first<'a>(s: &'a [u8]) -> (r: u8)
            requires s@.len() >= 1,
            ensures r == s[0],
        { s[0] }
    } => Ok(())
}

test_verify_one_file! {
    // Two #[pbt] callsites at the *same* instantiation reaching the same
    // generic provider: should fold into one engine block (no error).
    #[test] test_verus_pbt_generic_inheritance_dedup IMPORTS.to_string() + verus_code_str! {
        #[allow(unused_imports)] use vstd::contrib::verus_pbt::*;

        pub open spec fn id<T>(_x: T) -> bool { true }

        #[pbt(T = u32)]
        fn first<T>(x: T) -> (r: bool) ensures r == id(x), { let _ = x; true }

        #[pbt(T = u32)]
        fn second<T>(x: T) -> (r: bool) ensures r == id(x), { let _ = x; true }
    } => Ok(())
}

// ---------------------------------------------------------------------------
// Tracked / Ghost / Proof parameter detection.
// ---------------------------------------------------------------------------

test_verify_one_file! {
    // A `#[pbt]` on an exec fn that takes a `Tracked<&u64>` permission
    // parameter must be rejected with a clear actionable diagnostic.
    #[test] test_verus_pbt_tracked_param_diagnostic IMPORTS.to_string() + verus_code_str! {
        #[allow(unused_imports)] use vstd::contrib::verus_pbt::*;
        #[allow(unused_imports)] use vstd::prelude::Tracked;

        #[pbt]
        #[verifier::external_body]
        fn touch(x: u64, _t: Tracked<&u64>) -> (r: u64)
            ensures r == x,
        { x }
    } => Err(err) => assert_any_vir_error_msg(err, "ghost/permission state")
}

test_verify_one_file! {
    // Same for a Ghost-typed parameter.
    #[test] test_verus_pbt_ghost_param_diagnostic IMPORTS.to_string() + verus_code_str! {
        #[allow(unused_imports)] use vstd::contrib::verus_pbt::*;
        #[allow(unused_imports)] use vstd::prelude::Ghost;

        #[pbt]
        #[verifier::external_body]
        fn touch(x: u64, _g: Ghost<u64>) -> (r: u64)
            ensures r == x,
        { x }
    } => Err(err) => assert_any_vir_error_msg(err, "ghost/permission state")
}

test_verify_one_file! {
    // Tracked return type also rejected with the same diagnostic family.
    #[test] test_verus_pbt_tracked_return_diagnostic IMPORTS.to_string() + verus_code_str! {
        #[allow(unused_imports)] use vstd::contrib::verus_pbt::*;
        #[allow(unused_imports)] use vstd::prelude::Tracked;

        #[pbt]
        #[verifier::external_body]
        fn make() -> (r: Tracked<u64>)
            ensures true,
        { Tracked::assume_new() }
    } => Err(err) => assert_any_vir_error_msg(err, "ghost/permission state")
}

// ---------------------------------------------------------------------------
// `assume_specification` synthesis: a `#[pbt]` on an `assume_specification`
// item produces a synthetic exec wrapper that gets harnessed and verified.
// ---------------------------------------------------------------------------

test_verify_one_file! {
    // A `#[pbt]` on a free `assume_specification` over a primitive method.
    // The synthesized wrapper calls the path; the harness samples u32 and
    // checks the ensures clause against the wrapper's runtime call.
    #[test] test_verus_pbt_assume_spec_free_fn IMPORTS.to_string() + verus_code_str! {
        #[allow(unused_imports)] use vstd::contrib::verus_pbt::*;

        pub open spec fn small_spec(x: u32) -> bool { x <= 100 }

        // Standalone fn that wraps the spec path.
        #[verifier::external_body]
        pub fn small_via(x: u32) -> (r: bool) ensures r == small_spec(x), { x <= 100 }

        #[pbt]
        pub assume_specification[ small_via ](x: u32) -> (r: bool)
            ensures r == small_spec(x);
    } => Ok(())
}

test_verify_one_file! {
    // Generic assume_specification with `#[pbt(T = u32)]` instantiation:
    // the wrapper inherits the type-param substitution and gets harnessed.
    #[test] test_verus_pbt_assume_spec_generic IMPORTS.to_string() + verus_code_str! {
        #[allow(unused_imports)] use vstd::contrib::verus_pbt::*;

        #[verifier::external_body]
        pub fn pass<T>(x: T) -> (r: T) ensures true, { x }

        #[pbt(T = u32)]
        pub assume_specification<T>[ pass::<T> ](x: T) -> (r: T)
            ensures true;
    } => Ok(())
}

test_verify_one_file! {
    // assume_specification on a primitive method (closer to actual vstd).
    // The synthesized wrapper calls `<u8>::trailing_zeros` directly.
    #[test] test_verus_pbt_assume_spec_primitive_method IMPORTS.to_string() + verus_code_str! {
        #[allow(unused_imports)] use vstd::contrib::verus_pbt::*;

        pub open spec fn always(_i: u8) -> bool { true }

        // Stub free fn that the assume_spec proxies to. (We can't directly
        // assume_specification rust stdlib in a test, so use a local stand-in.)
        #[verifier::external_body]
        pub fn tz_local(i: u8) -> (r: u32) ensures always(i), { i.trailing_zeros() }

        #[pbt]
        pub assume_specification[ tz_local ](i: u8) -> (r: u32)
            ensures always(i);
    } => Ok(())
}

// ---------------------------------------------------------------------------
// `#[verifier::when_used_as_spec(spec_X)]` redirect: a `#[pbt]` contract
// that calls a runtime fn marked with `when_used_as_spec` should lower to
// the spec fn's `exec_*` companion, not the runtime fn's name.
// ---------------------------------------------------------------------------

test_verify_one_file! {
    // The free-fn case: `count_small(x)` redirects to `count_small_spec(x)`
    // when used in a spec context. The harness should call
    // `exec_count_small_spec`, not `exec_count_small` (which doesn't exist).
    #[test] test_verus_pbt_when_used_as_spec_free_fn IMPORTS.to_string() + verus_code_str! {
        #[allow(unused_imports)] use vstd::contrib::verus_pbt::*;

        pub open spec fn count_small_spec(x: u32) -> bool { x <= 100 }

        #[verifier::when_used_as_spec(count_small_spec)]
        #[verifier::external_body]
        pub fn count_small(x: u32) -> (r: bool)
            ensures r == count_small_spec(x),
        { x <= 100 }

        #[pbt]
        fn check(x: u32) -> (r: bool)
            ensures r == count_small(x),
        { count_small(x) }
    } => Ok(())
}

test_verify_one_file! {
    // Combined with assume_specification: the assume_spec carries
    // when_used_as_spec, and a `#[pbt]` contract that calls the runtime fn
    // gets correctly redirected.
    #[test] test_verus_pbt_when_used_as_spec_with_assume IMPORTS.to_string() + verus_code_str! {
        #[allow(unused_imports)] use vstd::contrib::verus_pbt::*;

        pub open spec fn always_le_100(x: u32) -> bool { x <= 100 }

        #[verifier::external]
        pub fn small_runtime(x: u32) -> bool { x <= 100 }

        #[verifier::when_used_as_spec(always_le_100)]
        #[pbt]
        pub assume_specification[ small_runtime ](x: u32) -> (r: bool)
            ensures r == always_le_100(x);
    } => Ok(())
}

// ---------------------------------------------------------------------------
// Trait-impl folding (monomorphized): `#[pbt_provide]` on an `impl Trait
// for X { ... }` block should pre-rewrite to an inherent impl with mangled
// method names, so the engine accepts it.
// ---------------------------------------------------------------------------

test_verify_one_file! {
    // A simple trait declaration + impl on a concrete type. The trait impl
    // gets folded after pre-rewrite; methods are renamed `Trait_method` to
    // avoid collisions if the type ever implements another trait.
    #[test] test_verus_pbt_trait_impl_concrete IMPORTS.to_string() + verus_code_str! {
        #[allow(unused_imports)] use vstd::contrib::verus_pbt::*;

        pub trait Sized2 {
            spec fn sized2(&self) -> bool;
        }

        #[pbt_provide]
        pub struct Wrap { pub n: u32 }

        #[pbt_provide]
        impl Sized2 for Wrap {
            spec fn sized2(&self) -> bool { self.n <= 100 }
        }
    } => Ok(())
}

test_verify_one_file! {
    // Generic trait impl with `#[pbt_provide(T = u32)]`: the impl is
    // monomorphized at the supplied instantiation, then the trait header
    // is dropped and methods are mangled.
    #[test] test_verus_pbt_trait_impl_generic IMPORTS.to_string() + verus_code_str! {
        #[allow(unused_imports)] use vstd::contrib::verus_pbt::*;

        pub trait IsSmall {
            spec fn is_small(&self) -> bool;
        }

        #[pbt_provide(T = u32)]
        pub struct Wrap<T> { pub n: T }

        #[pbt_provide(T = u32)]
        impl<T> IsSmall for Wrap<T> {
            spec fn is_small(&self) -> bool { true }
        }
    } => Ok(())
}

test_verify_one_file! {
    // A `#[pbt]` exec fn that exercises the trait-impl-folded spec method.
    // The trait method got renamed `IsSmall_is_small` after pre-rewrite, so
    // the contract uses the trait via the standard `<X as Trait>` form which
    // verus desugars to a direct method call.
    #[test] test_verus_pbt_trait_impl_pbt_callsite IMPORTS.to_string() + verus_code_str! {
        #[allow(unused_imports)] use vstd::contrib::verus_pbt::*;

        pub trait IsSmall {
            spec fn is_small(&self) -> bool;
        }

        #[pbt_provide]
        pub struct Wrap { pub n: u32 }

        #[pbt_provide]
        impl IsSmall for Wrap {
            spec fn is_small(&self) -> bool { self.n <= 100 }
        }

        impl Wrap {
            #[pbt]
            #[verifier::external_body]
            pub fn check(&self) -> (b: bool)
                ensures b == true,
            { self.n <= 100 }
        }
    } => Ok(())
}

// ---------------------------------------------------------------------------
// Phase 5: nat / int casts in contracts; &T / &[T] return shapes;
// Seq::index/subrange/update lowering in the harness rewriter; existential
// quantifiers via int-quantifier rewrite.
// ---------------------------------------------------------------------------

test_verify_one_file! {
    // `i as int` and `i as nat` casts in a contract should lower cleanly to
    // runtime integer arithmetic.
    #[test] test_verus_pbt_int_nat_casts IMPORTS.to_string() + verus_code_str! {
        #[allow(unused_imports)] use vstd::contrib::verus_pbt::*;

        pub open spec fn double_u64(x: u64) -> u64 { (x as int + x as int) as u64 }

        #[pbt]
        #[verifier::external_body]
        pub fn double_u32_to_u64(x: u32) -> (r: u64)
            requires (x as int) + (x as int) <= u64::MAX as int,
            ensures r == double_u64(x as u64),
        {
            x as u64 + x as u64
        }
    } => Ok(())
}

test_verify_one_file! {
    // `&T` return type — the harness adapts by dereferencing for value-side
    // contract checks.
    #[test] test_verus_pbt_ref_t_return IMPORTS.to_string() + verus_code_str! {
        #[allow(unused_imports)] use vstd::contrib::verus_pbt::*;

        pub open spec fn first_or_zero_spec(s: Seq<u8>) -> u8 {
            if s.len() > 0 { s[0] } else { 0 }
        }

        #[pbt]
        #[verifier::external_body]
        pub fn first_byte<'a>(s: &'a [u8]) -> (r: &'a u8)
            requires s@.len() > 0,
            ensures *r == s@.index(0),
        {
            &s[0]
        }
    } => Ok(())
}

test_verify_one_file! {
    // Existential quantifier with a runtime-typed bound variable. The
    // harness lifts the quantifier into a synthetic spec fn that the
    // engine compiles. (Note: `int`-bound quantifiers still aren't
    // supported because their use sites need spec-semantics help; runtime
    // primitive types are the recommended form.)
    #[test] test_verus_pbt_exists_runtime_quantifier IMPORTS.to_string() + verus_code_str! {
        #[allow(unused_imports)] use vstd::contrib::verus_pbt::*;

        pub open spec fn has_zero_byte(s: Seq<u8>) -> bool {
            exists |k: usize| 0 <= k < s.len() && s[k as int] == 0u8
        }

        #[pbt]
        #[verifier::external_body]
        pub fn vec_has_zero(v: Vec<u8>) -> (r: bool)
            ensures r == has_zero_byte(v.deep_view()),
        {
            v.contains(&0u8)
        }
    } => Ok(())
}

test_verify_one_file! {
    // Contract uses `s@.update(i as int, x)` — exercises the harness
    // rewriter's Seq::update lowering, the index_bound scan, and `int` cast
    // handling all in concert.
    #[test] test_verus_pbt_seq_update_lowering IMPORTS.to_string() + verus_code_str! {
        #[allow(unused_imports)] use vstd::contrib::verus_pbt::*;

        #[pbt]
        #[verifier::external_body]
        pub fn vec_set(v: Vec<u32>, i: usize, x: u32) -> (out: Vec<u32>)
            requires 0 <= i < v@.len(),
            ensures out@ == v@.update(i as int, x),
        {
            let mut out = v;
            out[i] = x;
            out
        }
    } => Ok(())
}

// ---------------------------------------------------------------------------
// Tier 1: const generics, &str, floats, vec_index path.
// ---------------------------------------------------------------------------

test_verify_one_file! {
    // `[T; N]` parameter via `#[pbt(T = u32, N = 4)]` — exercises the
    // const-generic substitution path and the OwnedArray strategy decl.
    #[test] test_verus_pbt_const_generic_array IMPORTS.to_string() + verus_code_str! {
        #[allow(unused_imports)] use vstd::contrib::verus_pbt::*;

        #[pbt(T = u32, N = 4)]
        #[verifier::external_body]
        pub fn array_index_get<T: Copy, const N: usize>(ar: &[T; N], i: usize) -> (out: T)
            requires
                i < N,
            ensures
                out == ar@.index(i as int),
        {
            ar[i]
        }
    } => Ok(())
}

test_verify_one_file! {
    // `[T; N]` returned by value. Exercises the Owned-array return shape
    // and the same `array::from_fn` pre-binding path on the input side.
    #[test] test_verus_pbt_const_generic_array_value_return
        IMPORTS.to_string() + verus_code_str! {
        #[allow(unused_imports)] use vstd::contrib::verus_pbt::*;

        #[pbt(T = i32, N = 3)]
        #[verifier::external_body]
        pub fn array_clone<T: Copy, const N: usize>(ar: [T; N]) -> (out: [T; N])
            ensures
                out@ == ar@,
        {
            ar
        }
    } => Ok(())
}

test_verify_one_file! {
    // `&str` param + `usize` index. The harness rewrites `s@` to a
    // `Vec<char>` slice via the runtime helper and checks the contract
    // `c == s@.index(i as int)` against the chars-projection.
    #[test] test_verus_pbt_str_param IMPORTS.to_string() + verus_code_str! {
        #[allow(unused_imports)] use vstd::contrib::verus_pbt::*;

        #[pbt]
        #[verifier::external_body]
        pub fn get_char(s: &str, i: usize) -> (c: char)
            requires
                i < s@.len(),
            ensures
                c == s@.index(i as int),
        {
            s.chars().nth(i).unwrap()
        }
    } => Ok(())
}

test_verify_one_file! {
    // `&str` return type. The harness lowers `out@` via `__pbt_str_chars`
    // for the post-call comparison.
    #[test] test_verus_pbt_str_return IMPORTS.to_string() + verus_code_str! {
        #[allow(unused_imports)] use vstd::contrib::verus_pbt::*;

        #[pbt]
        #[verifier::external_body]
        pub fn substring_char(s: &str, from: usize, to: usize) -> (ret: String)
            requires
                from <= to,
                to <= s@.len(),
            ensures
                ret@ == s@.subrange(from as int, to as int),
        {
            let mut iter = s.chars();
            let mut out = String::new();
            let mut k: usize = 0;
            while k < to
                invariant
                    k <= to,
                decreases (to - k),
            {
                let c = iter.next().unwrap();
                if k >= from {
                    out.push(c);
                }
                k += 1;
            }
            out
        }
    } => Ok(())
}

test_verify_one_file! {
    // `String` param + concat: exercises the `Seq + Seq` lowering through
    // `__pbt_seq_concat` after both operands rewrite to `&[char]`.
    #[test] test_verus_pbt_string_concat IMPORTS.to_string() + verus_code_str! {
        #[allow(unused_imports)] use vstd::contrib::verus_pbt::*;

        #[pbt]
        #[verifier::external_body]
        pub fn concat(a: String, b: &str) -> (ret: String)
            ensures
                ret@ == a@ + b@,
        {
            let mut out = a;
            out.push_str(b);
            out
        }
    } => Ok(())
}

test_verify_one_file! {
    // Float parameter: the `is_primitive_like` recogniser already accepts
    // `f32`/`f64`; the runtime crate adds `PbtStrategy` impls for both.
    // A trivial structural ensures clause is enough — Verus's float spec
    // support is limited but sampling/calling has to compile.
    #[test] test_verus_pbt_float_param IMPORTS.to_string() + verus_code_str! {
        #[allow(unused_imports)] use vstd::contrib::verus_pbt::*;

        #[pbt]
        #[verifier::external_body]
        pub fn double_f32(x: f32) -> (y: f32)
            ensures
                y == x + x,
        {
            x + x
        }
    } => Ok(())
}

test_verify_one_file! {
    // Vec by-value parameter pinned via `#[pbt(T = u64)]` — confirms the
    // generic-instantiation flow from the slice path also handles `Vec<T>`.
    #[test] test_verus_pbt_vec_by_value_indexed IMPORTS.to_string() + verus_code_str! {
        #[allow(unused_imports)] use vstd::contrib::verus_pbt::*;

        #[pbt(T = u64)]
        #[verifier::external_body]
        pub fn vec_index<T: Copy>(v: Vec<T>, i: usize) -> (element: T)
            requires
                i < v.view().len(),
            ensures
                element == v.view().index(i as int),
        {
            v[i]
        }
    } => Ok(())
}

// ---------------------------------------------------------------------------
// Tier 2a: `&mut <T>` parameters and `final()` / `old()` two-state contracts.
// ---------------------------------------------------------------------------

test_verify_one_file! {
    // `&mut Vec<T>`: the harness samples a Vec by value, snapshots the
    // pre-call deep_view, calls with `&mut <id>`, and evaluates the
    // contract using both `__pbt_pre_v` (for `old(v)`) and the post-call
    // `v` value (for `final(v)`).
    #[test] test_verus_pbt_mut_vec_push IMPORTS.to_string() + verus_code_str! {
        #[allow(unused_imports)] use vstd::contrib::verus_pbt::*;

        #[pbt(T = u32)]
        #[verifier::external_body]
        pub fn vec_push<T>(v: &mut Vec<T>, x: T)
            ensures
                final(v)@ == old(v)@.push(x),
        {
            v.push(x);
        }
    } => Ok(())
}

test_verify_one_file! {
    // Combined `requires old(...)` and `ensures final(...)`. Verifies the
    // pre-state snapshot is in scope for the requires clause too (it
    // needs to be, since `requires i < old(v)@.len()` references it).
    #[test] test_verus_pbt_mut_vec_set IMPORTS.to_string() + verus_code_str! {
        #[allow(unused_imports)] use vstd::contrib::verus_pbt::*;

        #[pbt(T = u32)]
        #[verifier::external_body]
        pub fn vec_set<T>(v: &mut Vec<T>, i: usize, x: T)
            requires
                i < old(v)@.len(),
            ensures
                final(v)@ == old(v)@.update(i as int, x),
        {
            v[i] = x;
        }
    } => Ok(())
}

test_verify_one_file! {
    // `&mut String`: exercises the `__pbt_pre_<id>` snapshot path with
    // string-shaped views. Contract uses `Seq<char>` concatenation.
    #[test] test_verus_pbt_mut_string_append IMPORTS.to_string() + verus_code_str! {
        #[allow(unused_imports)] use vstd::contrib::verus_pbt::*;

        #[pbt]
        #[verifier::external_body]
        pub fn string_append(s: &mut String, t: &str)
            ensures
                final(s)@ == old(s)@ + t@,
        {
            s.push_str(t);
        }
    } => Ok(())
}

test_verify_one_file! {
    // Pure `final(...)` with no `old(...)`: clearing the post-state.
    #[test] test_verus_pbt_mut_vec_clear IMPORTS.to_string() + verus_code_str! {
        #[allow(unused_imports)] use vstd::contrib::verus_pbt::*;

        #[pbt(T = u32)]
        #[verifier::external_body]
        pub fn vec_clear<T>(v: &mut Vec<T>)
            ensures
                final(v)@.len() == 0,
        {
            v.clear();
        }
    } => Ok(())
}

test_verify_one_file! {
    // `&mut HashMap`: the snapshot relies on `Clone`, which `HashMap`
    // implements. `final(m)` is referenced in the post-state and the
    // contract maps observable size growth to the pre-state.
    #[test] test_verus_pbt_mut_hashmap_insert IMPORTS.to_string() + verus_code_str! {
        #[allow(unused_imports)] use vstd::contrib::verus_pbt::*;
        use std::collections::HashMap;

        #[pbt(K = u32, V = u32)]
        #[verifier::external_body]
        pub fn map_insert<K: Eq + std::hash::Hash, V>(m: &mut HashMap<K, V>, k: K, v: V)
            ensures
                final(m)@.contains_key(k),
        {
            m.insert(k, v);
        }
    } => Ok(())
}

test_verify_one_file! {
    // `&mut self` on a user-defined struct. Exercises the receiver-side
    // path: harness samples `Counter` by value, snapshots, then mutates
    // through `&mut self_value`. Contract reads `old(self)` and `final(self)`
    // and routes through `value()` (a primitive-returning spec method).
    #[test] test_verus_pbt_mut_self_user_struct IMPORTS.to_string() + verus_code_str! {
        #[allow(unused_imports)] use vstd::contrib::verus_pbt::*;

        #[pbt_provide]
        pub struct Counter {
            pub n: u64,
        }

        #[pbt_provide]
        impl Counter {
            pub closed spec fn value(&self) -> u64 {
                self.n
            }
        }

        impl Counter {
            #[pbt]
            #[verifier::external_body]
            pub fn step(&mut self)
                requires
                    old(self).value() < u64::MAX - 1,
                ensures
                    final(self).value() == old(self).value() + 1,
            {
                self.n = self.n + 1;
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    // `&mut [E]` is rejected with a clean diagnostic — slices don't have
    // a clone-friendly snapshot path, so the macro pushes the user toward
    // a Vec<E> alternative.
    #[test] test_verus_pbt_mut_slice_rejected IMPORTS.to_string() + verus_code_str! {
        #[allow(unused_imports)] use vstd::contrib::verus_pbt::*;

        #[pbt]
        #[verifier::external_body]
        pub fn bad_set<T>(s: &mut [T], i: usize, x: T) {
            let _ = (s, i, x);
        }
    } => Err(e) => assert_eq!(e.errors.len(), 1)
}
