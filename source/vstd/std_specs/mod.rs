// PBT in-place patch: std_specs as a whole is now compiled under
// regular `cargo build` (vstd.rs un-gated `pub mod std_specs`).
// Submodules that depend on nightly-only traits or APIs (Freeze,
// PointeeSized, Allocator, Step, FromResidual, atomic_internals,
// generic_atomic, etc.) stay gated on `verus_keep_ghost`. The rest
// are un-gated so `#[pbt]` annotations on `assume_specification`
// items inside can fire under regular `cargo test`.
// alloc is un-gated for PBT (the liballoc-internal box-init specs;
// needs feature(liballoc_internals), enabled in vstd.rs).
#[cfg(feature = "alloc")]
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
// control_flow is un-gated for PBT (Result/Option branch and
// from_residual specs; needs feature(try_trait_v2), enabled in vstd.rs).
pub mod control_flow;
pub mod convert;
// core is un-gated for PBT (mem::swap, likely/unlikely specs; needs
// feature(freeze)/feature(ptr_metadata)/feature(core_intrinsics),
// enabled in vstd.rs).
pub mod core;
// default is un-gated for PBT (the per-primitive Default::default specs).
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
// range is un-gated for PBT (contains/next/RangeBounds specs and the
// trusted spec_range_next admits; needs feature(step_trait), enabled in
// vstd.rs). Items referencing the still-gated iter.rs spec traits
// (StepSpecImpl, IteratorSpecImpl) are gated per-item inside.
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

// smart_ptrs is un-gated for PBT (Box/Rc/Arc constructor and unwrap specs).
#[cfg(feature = "alloc")]
pub mod smart_ptrs;

#[cfg(feature = "nonzero_internals")]
pub mod nonzero;

// This struct is a hack that exists purely to create
// a rustdoc page dedicated to 'assume_specification' specs
pub struct VstdSpecsForRustStdLib;
