//! Runtime support for the `verus_pbt_unverified!` and `verus_pbt_verified!`
//! macros.
//!
//! The macros (defined in `verus_builtin_macros::contrib::verus_pbt`) generate
//! `proptest!` harness modules that call `pbt_strategy::<T>()` once per
//! function parameter. Implementations of [`PbtStrategy`] for primitives,
//! `Vec<T>`, `Option<T>`, `HashMap<K, V>` and `HashSet<T>` are provided here.
//! The macro additionally emits a `PbtStrategy` impl alongside every
//! user-defined `Exec*` struct/enum it generates.
//!
//! This crate is intentionally minimal: it depends only on `proptest` and is
//! meant to be added to the consumer's `[dev-dependencies]`. It contains no
//! Verus / vstd / `verus_builtin_macros` code and is therefore safe to compile
//! under plain rustc.

use std::collections::{HashMap, HashSet};
use std::fmt::Debug;
use std::hash::Hash;

use proptest::collection::{hash_map, hash_set, vec};
use proptest::prelude::any;
use proptest::strategy::{BoxedStrategy, Strategy};

/// Default upper bound on the size of generated collections (`Vec`, `HashMap`,
/// `HashSet`). Currently fixed; a future revision will accept this from the
/// `#![pbt(...)]` attribute on the macro invocation.
pub const DEFAULT_COLLECTION_MAX: usize = 16;

/// Bridge trait between `verus_pbt_*` harnesses and `proptest`. For every
/// parameter type appearing in a contract-bearing exec fn, the macro emits
/// `pbt_strategy::<T>()` and asks proptest to produce values of `T`.
pub trait PbtStrategy: Sized {
    /// Concrete strategy returned by [`PbtStrategy::pbt_strategy`].
    type Strategy: Strategy<Value = Self>;
    /// Build the strategy. Implementations should return a strategy that
    /// produces values respecting the generic `Arbitrary`-style defaults.
    fn pbt_strategy() -> Self::Strategy;
}

/// Convenience function used by the macro-generated harnesses.
pub fn pbt_strategy<T: PbtStrategy>() -> T::Strategy {
    T::pbt_strategy()
}

macro_rules! impl_primitive {
    ($($t:ty),* $(,)?) => {
        $(
            impl PbtStrategy for $t {
                type Strategy = BoxedStrategy<$t>;
                fn pbt_strategy() -> Self::Strategy { any::<$t>().boxed() }
            }
        )*
    };
}

impl_primitive!(
    bool, char, u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize,
);

impl<T: PbtStrategy + Debug + 'static> PbtStrategy for Vec<T>
where
    <T as PbtStrategy>::Strategy: 'static,
{
    type Strategy = BoxedStrategy<Vec<T>>;
    fn pbt_strategy() -> Self::Strategy {
        vec(T::pbt_strategy(), 0..=DEFAULT_COLLECTION_MAX).boxed()
    }
}

impl<T: PbtStrategy + Debug + 'static> PbtStrategy for Option<T>
where
    <T as PbtStrategy>::Strategy: 'static,
{
    type Strategy = BoxedStrategy<Option<T>>;
    fn pbt_strategy() -> Self::Strategy {
        proptest::option::of(T::pbt_strategy()).boxed()
    }
}

impl<K, V> PbtStrategy for HashMap<K, V>
where
    K: PbtStrategy + Eq + Hash + Debug + 'static,
    V: PbtStrategy + Debug + 'static,
    <K as PbtStrategy>::Strategy: 'static,
    <V as PbtStrategy>::Strategy: 'static,
{
    type Strategy = BoxedStrategy<HashMap<K, V>>;
    fn pbt_strategy() -> Self::Strategy {
        hash_map(K::pbt_strategy(), V::pbt_strategy(), 0..=DEFAULT_COLLECTION_MAX).boxed()
    }
}

impl<T> PbtStrategy for HashSet<T>
where
    T: PbtStrategy + Eq + Hash + Debug + 'static,
    <T as PbtStrategy>::Strategy: 'static,
{
    type Strategy = BoxedStrategy<HashSet<T>>;
    fn pbt_strategy() -> Self::Strategy {
        hash_set(T::pbt_strategy(), 0..=DEFAULT_COLLECTION_MAX).boxed()
    }
}

impl PbtStrategy for String {
    type Strategy = BoxedStrategy<String>;
    fn pbt_strategy() -> Self::Strategy {
        any::<String>().boxed()
    }
}

// ---------------------------------------------------------------------------
// vstd::contrib::exec_spec::ExecMultiset<T> strategy
//
// `ExecMultiset` is `pub struct ExecMultiset<T> { pub m: HashMap<T, usize> }`.
// We can't reference the type from this crate (it lives in `vstd`), so we
// keep this as a small helper module that consumers can opt into via a
// thin wrapper. The macro emits a manual `PbtStrategy` impl for
// `ExecMultiset<T>` whenever a contract uses `Multiset<T>` — see the macro
// for details. The helper here just exposes a strategy builder.

/// Build a strategy that produces an `ExecMultiset`-shaped value as a
/// `HashMap<T, usize>` whose values are bounded by `count_max`. The macro
/// uses this internally to bootstrap an `ExecMultiset<T>` from primitives
/// without the runtime crate having to know about `vstd` types.
pub fn multiset_inner_strategy<T>(count_max: u32) -> BoxedStrategy<HashMap<T, usize>>
where
    T: PbtStrategy + Eq + Hash + Debug + 'static,
    <T as PbtStrategy>::Strategy: 'static,
{
    hash_map(T::pbt_strategy(), 0usize..=count_max as usize, 0..=DEFAULT_COLLECTION_MAX).boxed()
}
