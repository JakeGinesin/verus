# `#[pbt_cov_mutate]` — ensures-clause coverage via in-process mutation

Drop the attribute on a `#[pbt]`-marked exec fn, run `cargo test`, and
see the report inline in your terminal.

## Setup

No setup needed. The mutator is in-process — pure Rust, no external
binary, no installation.

## Usage

```rust
#[pbt_cov_mutate]                    // <-- the only thing you add
#[pbt]
#[verifier::external_body]
pub exec fn double(x: u32) -> (y: u32)
    requires x <= u32::MAX / 2,
    ensures y == x + x,
{
    x + x
}
```

Then:

```bash
cargo test
```

The report writes directly to your controlling terminal, bypassing
cargo's per-test capture. You'll see something like this in the
output of plain `cargo test`:

```
mutation coverage report
────────────────────────
strong_double         ensures clause kills 1/1 body mutants  (100%)
weak_double           ensures clause kills 0/1 body mutants  (  0%)
  surviving:
    src/lib.rs:50  + → -
                  ensures clause did not detect

overall:  1 / 2  ( 50%)
```

## Reading the report

Each `#[pbt_cov_mutate]`-marked fn gets one line:

```
strong_double         ensures clause kills 1/1 body mutants  (100%)
```

- `1/1 body mutants` means **1 mutant generated, 1 caught by the ensures clause**.
- A 100% kill rate means every body change the mutator could produce was
  detected by the spec — your `ensures` clause is constraining the body
  on every observable axis the mutator tested.
- A non-100% rate lists the surviving mutants. Each survivor names the
  source location and the mutation that was applied. Either:
  - Your spec is too weak (a body change passes through unnoticed).
  - The mutation is **equivalent** — semantically identical to the
    original — and the survivor is a false positive.
- `(no mutation sites — body too small or only spec syntax)` means the
  body has nothing the operator surface can perturb (typically a single
  stdlib call). Coverage assessment doesn't apply to that fn.

## Options

```rust
#[pbt_cov_mutate(threshold = 90)]    // panic if kill rate < 90%
#[pbt_cov_mutate(skip)]              // record but don't run mutants
```

`threshold` is per-fn. When set and the per-fn kill rate falls below
the threshold, the report test panics with a violation message
(`cargo test` fails). The report still prints to the terminal.

## Mutation operators

The mutator applies these operator families:

- **arith-swap**: `+ ↔ -`, `* ↔ /`, `<< ↔ >>`, etc.
- **cmp-swap**: `< ↔ <=`, `== ↔ !=`, etc.
- **logic-swap**: `&& ↔ ||`, `!x → x`.
- **const-flip**: `0 ↔ 1`, `true ↔ false`, plus `v → 0`, `v → v±1`.
- **return-default**: `return e;` → `return Default::default();`.
- **stmt-delete**: drop a `v.push(...)` / `*p = ...` statement.
- **index-offset**: `s[i]` → `s[i+1]` / `s[i-1]`.
- **range-perturb**: `s[i..j]` → `s[j..i]` / `s[i..i]` / `s[i..(j+1)]`.
- **drop-`?`**: `expr?` → `expr`.

The set is deliberately small but covers the practical bug shapes that
slip past weak ensures clauses. Per-fn mutant count is capped at 30.

## Honest caveats

- **Equivalent mutants** sometimes survive — e.g. `x + 0 → x - 0` when
  `x = 0`. They show up as survivors and dilute the kill rate. Read the
  survivor list, not the score.
- **A 100% kill rate doesn't mean the spec is complete.** It means
  every mutation the mutator tried was caught. Mutation testing is one
  signal among many.
- **Bodies that are pure stdlib calls** (`u32::from_le_bytes(s.try_into().unwrap())`)
  contain nothing the v1 operator surface can mutate. The report says
  "no mutation sites" — accurate, but it means coverage assessment
  doesn't apply.
- **Compile time** scales linearly with mutant count. A fn with 30
  mutants emits 30 parallel fns plus 30 runners. The 30-cap keeps this
  bounded.
- **On Windows** the `/dev/tty` trick doesn't work; the report falls
  back to stderr, which `cargo test` captures by default. Use
  `cargo test -- --nocapture` to see it.
