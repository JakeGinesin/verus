# Property-based testing of contracts with `#[pbt]`

Verus proves that an implementation meets its `requires`/`ensures` contract.
But when an exec function is marked `#[verifier::external_body]`, Verus
*trusts* the contract without checking the body — the proof is only as good as
your trust in that body. The `#[pbt]` attribute closes that gap: it generates a
[`proptest`](https://docs.rs/proptest) harness that samples random inputs,
runs the real (trusted) body, and checks the contract against a runnable
version of your spec. A bug in an `external_body` function that Verus happily
accepts is caught by `cargo test`.

`#[pbt]` builds on the [`exec_spec_unverified!`](exec_spec.html) engine: it
compiles the spec functions reachable from a contract into runnable `exec_*`
companions, generates `proptest` strategies for the types involved, and emits
the harness. You write ordinary Verus and add one attribute.

## Setup

Add the runtime crate (which carries the `proptest` strategies) and `proptest`
itself as dev-dependencies:

```toml
[dev-dependencies]
proptest = "1"
verus_pbt_runtime = "*"
```

The generated harness modules are gated on `#[cfg(test)]`, so neither
dependency affects a normal `cargo verus build`.

## The `#[pbt]` attribute

Mark a contract-bearing exec function with `#[pbt]`. Everything its contract
reaches — spec functions, the types they mention — is discovered automatically
among the items in the same `verus! { ... }` block:

```rust
use vstd::contrib::exec_spec::*;
use vstd::contrib::verus_pbt::*;
use vstd::prelude::*;

verus! {

pub enum Permission { Read, Write, Admin, Revoked }

pub struct User { pub name_len: usize, pub perm: Permission, pub quota: u64 }

impl Permission {
    pub open spec fn grants_write(&self) -> bool {
        matches!(self, Permission::Write | Permission::Admin)
    }
    pub open spec fn is_revoked(&self) -> bool {
        matches!(self, Permission::Revoked)
    }
}

impl User {
    pub open spec fn is_valid_spec(&self) -> bool {
        &&& self.name_len > 0
        &&& !self.perm.is_revoked()
        &&& (self.perm.grants_write() ==> self.quota > 0)
    }

    #[pbt]                       // <-- the only thing you add
    #[verifier::external_body]
    pub fn is_valid(&self) -> (b: bool)
        ensures b == self.is_valid_spec(),
    {
        // ... real implementation ...
    }
}

} // verus!
```

- `cargo verus verify` checks the spec layer as usual.
- `cargo test` runs the generated `pbt_User_is_valid` harness: it samples a
  random `User` (including its `Permission` field), calls `is_valid`, and
  asserts the result matches `is_valid_spec`. If the body lies, proptest finds
  and shrinks a counterexample.

No separate macro block, no manual strategies, no `Exec*` types in your code.

## Crossing files with `#[pbt_provide]`

A function-like macro can only see the items between its own braces, so
`#[pbt]` only discovers spec functions and types in the *same* `verus!` block.
When a type or spec function lives in another module/file, mark it with
`#[pbt_provide]` at its definition site:

```rust
// perms.rs
verus! {
    #[pbt_provide]
    pub enum Permission { Read, Revoked }
    impl Permission {
        pub open spec fn is_revoked(&self) -> bool { matches!(self, Permission::Revoked) }
    }
}
```

```rust
// users.rs
use crate::perms::Permission;
verus! {
    #[pbt_provide]
    pub struct User { pub name_len: usize, pub perm: Permission }
    impl User {
        pub open spec fn is_valid_spec(&self) -> bool {
            self.name_len > 0 && !self.perm.is_revoked()
        }
    }
}
```

```rust
// validate.rs
use crate::users::User;
verus! {
    impl User {
        #[pbt]
        #[verifier::external_body]
        pub fn is_valid(&self) -> (b: bool) ensures b == self.is_valid_spec() { /* ... */ }
    }
}
```

`#[pbt_provide]` emits, at the definition site, the runtime trait impls the
harness needs: `PbtStrategy` (how to sample the type), `ToExecModel` (how to
convert it to the engine's exec model), and the spec companions. These are
*traits*, so they resolve across files by ordinary `use` — `ToExecModel for
User` composes through `ToExecModel for Permission` without `users.rs` ever
seeing `Permission`'s definition.

If you forget `#[pbt_provide]` on a type a contract reaches, you get a
localized compiler error at `cargo test` time naming the type:

```text
error[E0277]: `users::User` is not set up for property-based testing
  --> src/validate.rs:...
   |   no `PbtStrategy` for `users::User`
   = note: add `#[pbt_provide]` to the definition of `users::User`
           (and its spec fns) ...
```

## Using specs you don't control (`external_pbt_provide!`)

`#[pbt_provide]` works when you can edit the definition. But a contract may call
a spec function from a crate you don't own — `vstd`, or a published library —
where adding `#[pbt_provide]` isn't an option. When `#[pbt]` finds a free spec
function in a contract that it can't resolve in-block, it stops with a
tier-aware diagnostic that walks you through the options, from least to most
effort:

```text
verus_pbt: the spec function `crate::seqlib::is_sorted` (resolved from a `use`
in this file) is used in a `#[pbt]` contract but is defined outside this
`verus!` block, so no exec companion can be generated for it.

Resolve it at the first applicable tier:
  1. If it is a container method (Seq/Map/Set/Multiset/Option), rewrite the
     contract to use the method form so the engine compiles it directly.
  2. If you own its definition, add `#[pbt_provide]` to it ...
  3. If it is a public-bodied spec fn in a crate you build with `cargo verus`,
     run `cargo verus pbt-gen` ...
  4. Otherwise, supply a trusted exec stub next to your `#[pbt]` fn:
       external_pbt_provide! { fn crate::seqlib::is_sorted(/* args */) -> /* ret */ { /* exec body */ } }
```

The diagnostic infers the spec function's path from the `use` statements in the
file, so the suggestion points at the real definition site.

Tier 4 — `external_pbt_provide!` — is the explicit escape hatch. You write a
**trusted** executable twin of the external spec function once, in the same
`verus!` block as the `#[pbt]` function:

```rust
use vstd::contrib::verus_pbt::*;
use vstd::prelude::*;

verus! {

// `is_sorted` is a spec fn defined elsewhere (e.g. another crate). Supply its
// exec twin once. The signature uses the SPEC types; the body is ordinary exec
// Rust over their lowered forms (`Seq<i64>` is sampled and handed in as
// `&[i64]`, `Map<K,V>` as `&HashMap<K,V>`, a `#[pbt_provide]`'d `User` as
// `&ExecUser`, and so on).
external_pbt_provide! {
    fn is_sorted(s: Seq<i64>) -> bool {
        let mut i = 0;
        while i + 1 < s.len() {
            if s[i] > s[i + 1] { return false; }
            i += 1;
        }
        true
    }
}

#[pbt]
#[verifier::external_body]
pub fn is_input_sorted(s: &[i64]) -> (b: bool)
    ensures b == is_sorted(s.deep_view()),
{ /* ... */ }

} // verus!
```

The provided body is emitted only into the generated `#[cfg(test)]` harness, so
it never participates in verification — Verus still checks the spec layer
against the *real* external spec function. The twin only affects what `cargo
test` evaluates the contract against, so its correctness is on you (hence
"trusted"). Use it as a last resort, when tiers 1–3 don't apply.

> Tiers 1 and 2 are handled automatically (container methods compile directly;
> `#[pbt_provide]` generates everything). Tier 3 (`cargo verus pbt-gen`,
> auto-lowering a public spec body from the exported `.vir`) is planned. Tier 4
> is available today.

## The rule of thumb

- Within one `verus!` block: just `#[pbt]` on the function. The closure of
  spec fns + types it reaches is folded in automatically.
- Across files: also `#[pbt_provide]` each spec type / spec fn at its
  definition site. Connect with normal `use`.

## Relationship to `verus_pbt_unverified!`

`#[pbt]` and `#[pbt_provide]` are the recommended surface. The underlying
`verus_pbt_unverified! { ... }` macro (which folds an explicit set of items
into one engine + harness block) is still available as the explicit,
no-inference form — `#[pbt]` is implemented by folding the computed closure
into exactly such a block.

## Limitations

`#[pbt]` inherits the [`exec_spec_unverified!` fragment](exec_spec.html):
spec constructs the engine cannot compile (e.g. `int`/`nat` in arithmetic
positions, closure-based `Seq::all`, `arbitrary()`) are unsupported wherever
they appear. Sampling a type requires its fields to be of supported types.
Tight `requires` preconditions are enforced via `prop_assume!`, so a
precondition satisfied by very few random inputs can exhaust proptest's
rejection budget; in that case, loosen the precondition for testing or provide
a custom strategy.

## Related

- [Automatic spec to exec functions](exec_spec.html) — the engine `#[pbt]`
  builds on.
- [Spec and proof attributes for exec functions](exec_attr.html).
