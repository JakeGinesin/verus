# verus_pbt_assert

Demo for `#[pbt]` on inline asserts inside `verus!` exec functions.

## What this demonstrates

Two forms of inline-assert testing:

### Path-form `#[pbt] assert(P)`

Drop the marker on a regular Verus assert inside a `#[pbt]`-marked exec
fn. The harness drives the enclosing fn with random params (using the
fn's own preconditions as `prop_assume!` filters), then panics at the
assert site if `P` is false. proptest catches the panic, shrinks, and
reports a counterexample.

```rust
#[pbt]
#[verifier::external_body]
pub exec fn safe_div(num: u32, den: u32) -> (r: u32)
    ensures r == spec_safe_div(num, den),
{
    let result = if den != 0u32 { num / den } else { 0u32 };
    #[pbt] assert(den == 0u32 || result <= num);
    result
}
```

This emits a `#[test] fn __pbt_assert_safe_div_at_lineN()` alongside the
ensures-clause harness `pbt_safe_div`. The two are independent:
`pbt_safe_div` checks the contract holistically, while
`__pbt_assert_safe_div_at_lineN` checks the inline invariant.

### Forall-form `#[pbt] assert forall |x: T| P(x) by { }`

Standalone universally-quantified property, sampled directly. The
harness samples `x: T` via the existing `pbt_strategy::<T>()` trait
and evaluates `P` for each sample.

```rust
#[pbt] assert forall |w: u32|
    w <= u32::MAX / 2u32 implies w + w == 2u32 * w by { };
```

`implies` form: the antecedent acts as `prop_assume!` (rejected
samples are discarded), the consequent acts as the assertion.

## Tier-1 limitations

- **Forall predicates aren't spec→exec lowered.** The expression must
  evaluate as exec code on the sampled binders. Predicates that
  reference spec-only constructs (`Seq`, `Map`, ghost projections,
  calls to `spec` fns) won't compile in tier 1.
- **No captured locals in forall-form.** Path-form picks up captured
  outer locals for free because the harness drives the enclosing fn.
- **`#[pbt] assert(P) by(prover)` and `assert(P) by { proof }` are
  rejected** with a clear diagnostic.
- **Untyped binders are rejected**: `#[pbt] assert forall |w| ...` is
  an error because we can't sample without a type.

## Running

```sh
cargo test --release
```

You'll see one test per inline assert plus the regular ensures-clause
harness for each `#[pbt]` fn.

## When to use which form

| your situation | use |
|---|---|
| testing a body invariant that uses outer locals | path-form |
| testing a free property of the spec, mid-fn | forall-form |
| testing the function's contract holistically | regular `#[pbt]` (no inline) |

For a more complex use case showing both forms in the same fn, see the
`triple` example in `src/lib.rs`.
