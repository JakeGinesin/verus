# verus_pbt_smoke

Phase 1 smoke test for the in-tree `verus_pbt_unverified!` macro.

`src/lib.rs` defines a single contract-bearing exec fn (`append_vec`) wrapped
by `verus_pbt_unverified!`. Verifying the crate exercises the spec-layer
expansion; running its tests exercises the proptest harness the macro emits.

## Running

```sh
# Build the verus toolchain (once per source change)
cd ../../source && vargo build --release

# Verify the spec layer
cd ../examples/verus_pbt_smoke
PATH="$(git rev-parse --show-toplevel)/source/target-verus/release:$PATH" \
    cargo-verus verify

# Run the proptest harness (plain cargo; the harness mod is #[cfg(test)])
unset -f cargo
cargo test
```

Expected output:

```
verification results:: 3 verified, 0 errors
...
test __verus_pbt_0::pbt_append_vec ... ok
```

## What the macro emits

For `append_vec`, `verus_pbt_unverified!` produces:

1. The original spec fns (`small_enough`, `appended`) and the exec fn
   (`append_vec`) verbatim, wrapped in a `vstd::prelude::verus! { ... }`
   block so Verus still verifies the contract.
2. An `exec_spec_unverified!` block compiling the spec fns into runnable
   `exec_small_enough`, `exec_appended` analogues.
3. A `#[cfg(test)] mod __verus_pbt_0 { ... }` containing one
   `proptest!` harness named `pbt_append_vec`. The harness draws random
   `Vec<i64>` values via `verus_pbt_runtime::pbt_strategy::<Vec<i64>>()`,
   `prop_assume!`s the rewritten requires, calls `super::append_vec`, and
   `prop_assert!`s the rewritten ensures.
