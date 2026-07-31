// PBT in-place patch: std_specs as a whole is now compiled under
// regular `cargo build` (vstd.rs un-gated `pub mod std_specs`).
// Submodules that depend on nightly-only traits or APIs (Freeze,
// PointeeSized, Allocator, Step, FromResidual, atomic_internals,
// generic_atomic, etc.) stay gated on `verus_keep_ghost`. The rest
// are un-gated so `#[pbt]` annotations on `assume_specification`
// items inside can fire under regular `cargo test`.
#[cfg(all(feature = "alloc", verus_keep_ghost))]
pub mod alloc;

#[cfg(verus_keep_ghost)]
pub mod atomic;
pub mod bits;
pub mod borrow;
// char is un-gated for PBT (UTF-8 width and whitespace specs).
pub mod char;
// clone and cmp are un-gated for PBT (bool/char/array clone and bool
// comparison specs; needs feature(sized_hierarchy), enabled in vstd.rs).
pub mod clone;
pub mod cmp;
#[cfg(verus_keep_ghost)]
pub mod control_flow;
pub mod convert;
#[cfg(verus_keep_ghost)]
pub mod core;
#[cfg(verus_keep_ghost)]
pub mod default;
#[cfg(verus_keep_ghost)]
pub mod iter;
pub mod manually_drop;
pub mod maybe_uninit;
pub mod ops;

// btree is un-gated for PBT (same pattern as vec/vecdeque).
#[cfg(feature = "alloc")]
pub mod btree;
// hash is un-gated for PBT (same pattern as vec/vecdeque/btree).
#[cfg(all(feature = "alloc", feature = "std"))]
pub mod hash;

pub mod num;
pub mod option;
#[cfg(verus_keep_ghost)]
pub mod range;
pub mod result;

// slice is un-gated for PBT (same pattern as vec/vecdeque).
pub mod slice;

// vec is un-gated for PBT (needs the `allocator` cargo feature, on by
// default in this checkout, for its `A: Allocator` generics).
#[cfg(feature = "alloc")]
pub mod vec;

// vecdeque is un-gated for PBT (same pattern as vec).
#[cfg(feature = "alloc")]
pub mod vecdeque;

#[cfg(all(feature = "alloc", verus_keep_ghost))]
pub mod smart_ptrs;

#[cfg(feature = "nonzero_internals")]
pub mod nonzero;

// This struct is a hack that exists purely to create
// a rustdoc page dedicated to 'assume_specification' specs
pub struct VstdSpecsForRustStdLib;
