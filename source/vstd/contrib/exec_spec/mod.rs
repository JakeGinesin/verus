//! This module provides runtime utilities for the compiled
//! executable code of [`verus_builtin_macros::exec_spec_verified`]
//! and [`verus_builtin_macros::exec_spec_unverified`].
#![cfg(all(feature = "alloc", feature = "std"))]

use crate::multiset::*;
use crate::prelude::*;
use std::collections::HashMap;
use std::collections::HashSet;
pub use verus_builtin_macros::exec_spec_unverified;
pub use verus_builtin_macros::exec_spec_verified;

mod map;
pub use map::*;
mod multiset;
pub use multiset::*;
mod option;
pub use option::*;
mod seq;
pub use seq::*;
mod set;
pub use set::*;
mod string;
pub use string::*;

verus! {

/// [`ToRef`] and [`ToOwned`] are almost the same trait
/// but separated to avoid type inference ambiguities.
pub trait ToRef<T: Sized + DeepView>: Sized + DeepView<V = T::V> {
    fn get_ref(self) -> (res: T)
        ensures
            res.deep_view() == self.deep_view(),
    ;
}

pub trait ToOwned<T: Sized + DeepView>: Sized + DeepView<V = T::V> {
    fn get_owned(self) -> (res: T)
        ensures
            res.deep_view() == self.deep_view(),
    ;
}

/// Cloned objects have the same deep view
pub trait DeepViewClone: Sized + DeepView {
    fn deep_clone(&self) -> (res: Self)
        ensures
            res.deep_view() == self.deep_view(),
    ;
}

/// Any spec types used in [`exec_spec_verified`] or [`exec_spec_unverified`] macros
/// must implement this trait to indicate
/// the corresponding exec type (owned and borrowed versions).
pub trait ExecSpecType where
    for <'a>&'a Self::ExecOwnedType: ToRef<Self::ExecRefType<'a>>,
    for <'a>Self::ExecRefType<'a>: ToOwned<Self::ExecOwnedType>,
 {
    /// Owned version of the exec type.
    type ExecOwnedType: DeepView<V = Self>;

    /// Reference version of the exec type.
    type ExecRefType<'a>: DeepView<V = Self>;
}

/// Spec for the executable version of equality.
pub trait ExecSpecEq<'a>: DeepView + Sized {
    type Other: DeepView<V = Self::V>;

    fn exec_eq(this: Self, other: Self::Other) -> (res: bool)
        ensures
            res == (this.deep_view() =~~= other.deep_view()),
    ;
}

/// Spec for executable version of [`Seq`] and [`str`] indexing.
pub trait ExecSpecIndex<'a>: Sized + DeepView<V = Seq<<Self::Elem as DeepView>::V>> {
    type Elem: DeepView;

    fn exec_index(self, index: usize) -> Self::Elem
        requires
            0 <= index < self.deep_view().len(),
    ;
}

/// Spec for executable version of `len`.
pub trait ExecSpecLen {
    fn exec_len(self) -> usize;
}

/// A macro to implement various traits for primitive arithmetic types.
macro_rules! impl_primitives {
    ($(,)?) => {};
    ($t:ty $(,$rest:ty)* $(,)?) => {
        verus! {
            impl ExecSpecType for $t {
                type ExecOwnedType = $t;
                type ExecRefType<'a> = $t;
            }

            impl<'a> ToRef<$t> for &'a $t {
                #[inline(always)]
                fn get_ref(self) -> $t {
                    *self
                }
            }

            impl ToOwned<$t> for $t {
                #[inline(always)]
                fn get_owned(self) -> $t {
                    self
                }
            }

            impl DeepViewClone for $t {
                #[inline(always)]
                fn deep_clone(&self) -> Self {
                    *self
                }
            }

            impl<'a> ExecSpecEq<'a> for $t {
                type Other = $t;

                #[inline(always)]
                fn exec_eq(this: Self, other: Self::Other) -> bool {
                    this == other
                }
            }

            // For cases like comparing Seq<u32> and Seq<u32>
            impl<'a> ExecSpecEq<'a> for &'a $t {
                type Other = &'a $t;

                #[inline(always)]
                fn exec_eq(this: Self, other: Self::Other) -> bool {
                    this == other
                }
            }
        }

        impl_primitives!($($rest),*);
    };
}

impl_primitives! {
    u8, u16, u32, u64, u128, usize,
    i8, i16, i32, i64, i128, isize,
    bool, char,
}
// impl on tuples up to size 4, to match the impls of View in vstd


macro_rules! impl_exec_spec_tuple {
    ([$(
        ($T:ident, $n:tt)
    ),*])=> {
        verus! {

            impl<'a, $($T: Sized + DeepView),*> ToRef<&'a ($($T,)*)> for &'a ($($T,)*) {
                #[inline(always)]
                fn get_ref(self) -> &'a ($($T,)*) {
                    self
                }
            }

            impl<'a, $($T: DeepView + DeepViewClone),*> ToOwned<($($T,)*)> for &'a ($($T,)*) {
                #[inline(always)]
                fn get_owned(self) -> ($($T,)*) {
                    self.deep_clone()
                }
            }

            impl<$($T: DeepViewClone),*> DeepViewClone for ($($T,)*) {
                #[inline(always)]
                #[allow(non_snake_case)]
                fn deep_clone(&self) -> Self {
                    ($(self.$n.deep_clone(),)*)
                }
            }

            impl<'a, $($T: DeepView),*> ExecSpecEq<'a> for &'a ($($T,)*)
            where
                $( &'a $T: ExecSpecEq<'a, Other = &'a $T>, )*
            {
                type Other = &'a ($($T,)*);

                #[inline(always)]
                #[allow(non_snake_case)]
                fn exec_eq(this: Self, other: Self::Other) -> bool {
                    $( <&$T>::exec_eq(&this.$n, &other.$n) )&&*
                }
            }

        }
    };
}

impl_exec_spec_tuple!([(T0, 0)]);

impl_exec_spec_tuple!([(T0, 0), (T1, 1)]);

impl_exec_spec_tuple!([(T0, 0), (T1, 1), (T2, 2)]);

impl_exec_spec_tuple!([(T0, 0), (T1, 1), (T2, 2), (T3, 3)]);

} // verus!

// vcheck oracles for the trusted exec_spec implementations
#[cfg(not(any(verus_verify_core, verus_keep_ghost)))]
mod vcheck_oracles {
    use super::{
        ExecMultiset, ExecSpecEq, ExecSpecLen, ExecSpecMapDom, ExecSpecMapGet, ExecSpecMapIndex,
        ExecSpecMapInsert, ExecSpecMapRemove, ExecSpecMultisetAdd, ExecSpecMultisetCount,
        ExecSpecMultisetSub, ExecSpecSeqAdd, ExecSpecSeqContains, ExecSpecSeqIndexOf,
        ExecSpecSeqIndexOfFirst, ExecSpecSeqIndexOfLast, ExecSpecSeqPush, ExecSpecSeqSubrange,
        ExecSpecSeqToMultiset, ExecSpecSeqUpdate, ExecSpecSetContains, ExecSpecSetDifference,
        ExecSpecSetInsert, ExecSpecSetIntersect, ExecSpecSetRemove, ExecSpecSetUnion,
    };
    use crate::prelude::*;
    use std::collections::{HashMap, HashSet};

    verus! {

    /// ExecMultiset ops agree with the multiset specs, including zero-count entries
    #[verifier::external_body]
    #[vcheck]
    pub fn vcheck_exec_multiset_ops(a: HashMap<u32, u8>, b: HashMap<u32, u8>, same: bool, pad: u8, k: u32) -> (ret: bool)
        ensures
            ret,
    {
        let b = if same {
            a.clone()
        } else {
            b
        };
        let mk = |m: &HashMap<u32, u8>, z: bool| {
            let mut h: HashMap<u32, usize> = m.iter().map(|(x, c)| (*x, *c as usize)).collect();
            if z {
                h.entry(k).or_insert(0);
            }
            ExecMultiset { m: h }
        };
        let ma = mk(&a, pad % 3 == 1);
        let mb = mk(&b, pad % 3 == 2);
        let cnt = |m: &ExecMultiset<u32>, x: u32| m.m.get(&x).copied().unwrap_or(0);
        let keys: HashSet<u32> = ma.m.keys().chain(mb.m.keys()).copied().chain([k]).collect();
        let spec_eq = keys.iter().all(|x| cnt(&ma, *x) == cnt(&mb, *x));
        let eq_ok = <&ExecMultiset<u32> as ExecSpecEq>::exec_eq(&ma, &mb) == spec_eq;
        let len_ok = (&ma).exec_len() == ma.m.values().sum::<usize>();
        let count_ok = (&ma).exec_count(k) == cnt(&ma, k);
        let add = (&ma).exec_add(&mb);
        let sub = (&ma).exec_sub(&mb);
        let add_ok = keys.iter().all(|x| cnt(&add, *x) == cnt(&ma, *x) + cnt(&mb, *x));
        let sub_ok = keys.iter().all(|x| cnt(&sub, *x) == cnt(&ma, *x).saturating_sub(cnt(&mb, *x)));
        eq_ok && len_ok && count_ok && add_ok && sub_ok
    }

    /// ExecMultiset `exec_len` never returns a wrapped sum of counts
    #[verifier::external_body]
    #[vcheck]
    pub fn vcheck_exec_multiset_len_overflow(c1: u64, c2: u64) -> (ret: bool)
        ensures
            ret,
    {
        let mut h: HashMap<u32, usize> = HashMap::new();
        h.insert(1, (c1 | (1u64 << 63)) as usize);
        h.insert(2, (c2 | (1u64 << 63)) as usize);
        let ms = ExecMultiset { m: h };
        let total: u128 = ms.m.values().map(|c| *c as u128).sum();
        match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| (&ms).exec_len())) {
            Ok(r) => r as u128 == total,
            Err(_) => total > usize::MAX as u128,
        }
    }

    /// Vec-backed Seq exec ops agree with the Seq specs
    #[verifier::external_body]
    #[vcheck]
    pub fn vcheck_exec_seq_ops(v: Vec<u32>, w: Vec<u32>, i: u8, j: u8, x: u32, pick: bool) -> (ret: bool)
        ensures
            ret,
    {
        let s = v.as_slice();
        let t = w.as_slice();
        let len = v.len();
        let x = if pick && len > 0 {
            v[(i as usize) % len]
        } else {
            x
        };
        let eq_ok = <&[u32] as ExecSpecEq>::exec_eq(s, t) == (v == w);
        let eq_self = <&[u32] as ExecSpecEq>::exec_eq(s, s);
        let add_ok = s.exec_add(t) == [v.clone(), w.clone()].concat();
        let mut pv = v.clone();
        pv.push(x);
        let push_ok = s.exec_push(x) == pv;
        let upd_ok = if len > 0 {
            let k = (i as usize) % len;
            let mut u = v.clone();
            u[k] = x;
            s.exec_update(k, x) == u
        } else {
            true
        };
        let (lo, hi) = {
            let a = (i as usize) % (len + 1);
            let b = (j as usize) % (len + 1);
            if a <= b {
                (a, b)
            } else {
                (b, a)
            }
        };
        let sub_ok = s.exec_subrange(lo, hi) == &v[lo..hi];
        let ms = s.exec_to_multiset();
        let ms_ok = v.iter().all(|e| ms.m.get(e).copied().unwrap_or(0) == v.iter().filter(|f| *f == e).count())
            && ms.m.values().sum::<usize>() == len;
        let contains_ok = s.exec_contains(x) == v.contains(&x);
        let first = v.iter().position(|e| *e == x);
        let last = v.iter().rposition(|e| *e == x);
        let io = s.exec_index_of(x);
        let io_ok = match first {
            Some(_) => io < len && v[io] == x,
            None => io == len,
        };
        let iof_ok = s.exec_index_of_first(x) == first;
        let iol_ok = s.exec_index_of_last(x) == last;
        eq_ok && eq_self && add_ok && push_ok && upd_ok && sub_ok && ms_ok && contains_ok && io_ok && iof_ok && iol_ok
    }

    /// HashSet-backed Set exec ops agree with the Set specs
    #[verifier::external_body]
    #[vcheck]
    pub fn vcheck_exec_set_ops(a: HashSet<u32>, b: HashSet<u32>, x: u32, same: bool) -> (ret: bool)
        ensures
            ret,
    {
        let b = if same {
            a.clone()
        } else {
            b
        };
        let eq_ok = <&HashSet<u32> as ExecSpecEq>::exec_eq(&a, &b) == (a == b);
        let len_ok = (&a).exec_len() == a.len();
        let contains_ok = (&a).exec_contains(x) == a.contains(&x);
        let mut ins = a.clone();
        ins.insert(x);
        let mut rem = a.clone();
        rem.remove(&x);
        let ins_ok = (&a).exec_insert(x) == ins;
        let rem_ok = (&a).exec_remove(x) == rem;
        let int_ok = (&a).exec_intersect(&b) == a.intersection(&b).copied().collect::<HashSet<u32>>();
        let uni_ok = (&a).exec_union(&b) == a.union(&b).copied().collect::<HashSet<u32>>();
        let dif_ok = (&a).exec_difference(&b) == a.difference(&b).copied().collect::<HashSet<u32>>();
        eq_ok && len_ok && contains_ok && ins_ok && rem_ok && int_ok && uni_ok && dif_ok
    }

    /// HashMap-backed Map exec ops agree with the Map specs
    #[verifier::external_body]
    #[vcheck]
    pub fn vcheck_exec_map_ops(a: HashMap<u32, u32>, b: HashMap<u32, u32>, k: u32, v: u32, same: bool) -> (ret: bool)
        ensures
            ret,
    {
        let b = if same {
            a.clone()
        } else {
            b
        };
        let k = if same && !a.is_empty() {
            *a.keys().next().unwrap()
        } else {
            k
        };
        let eq_ok = <&HashMap<u32, u32> as ExecSpecEq>::exec_eq(&a, &b) == (a == b);
        let len_ok = (&a).exec_len() == a.len();
        let mut ins = a.clone();
        ins.insert(k, v);
        let mut rem = a.clone();
        rem.remove(&k);
        let ins_ok = (&a).exec_insert(k, v) == ins;
        let rem_ok = (&a).exec_remove(k) == rem;
        let dom_ok = (&a).exec_dom() == a.keys().copied().collect::<HashSet<u32>>();
        let get_ok = (&a).exec_get(k) == a.get(&k).copied();
        let idx_ok = match a.get(&k) {
            Some(x) => *(&a).exec_index(k) == *x,
            None => true,
        };
        eq_ok && len_ok && ins_ok && rem_ok && dom_ok && get_ok && idx_ok
    }

    } // verus!
}
