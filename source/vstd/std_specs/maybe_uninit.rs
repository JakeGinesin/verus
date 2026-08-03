use super::super::prelude::*;
use super::super::raw_ptr::MemContents;
use core::mem::MaybeUninit;

use verus as verus_;
verus_! {

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::accept_recursive_types(T)]
pub struct ExMaybeUninit<T>(MaybeUninit<T>);

pub trait MaybeUninitAdditionalSpecFns<T> {
    spec fn mem_contents(self) -> MemContents<T>;
    spec fn as_option(self) -> Option<T>;
}

impl<T> MaybeUninitAdditionalSpecFns<T> for MaybeUninit<T> {
    uninterp spec fn mem_contents(self) -> MemContents<T>;

    open spec fn as_option(self) -> Option<T> {
        match self.mem_contents() {
            MemContents::Init(v) => Some(v),
            MemContents::Uninit => None,
        }
    }
}

pub assume_specification<T>[ MaybeUninit::<T>::new ](val: T) -> (res: MaybeUninit<T>)
    ensures res.mem_contents() == MemContents::Init(val),
    opens_invariants none
    no_unwind;

pub assume_specification<T>[ MaybeUninit::<T>::uninit ]() -> (res: MaybeUninit<T>)
    ensures res.mem_contents() == MemContents::Uninit,
    opens_invariants none
    no_unwind;

pub assume_specification<T>[ MaybeUninit::<T>::assume_init ](m: MaybeUninit<T>) -> T
    requires m.mem_contents().is_init(),
    returns m.mem_contents().value(),
    opens_invariants none
    no_unwind;

pub assume_specification<T>[ MaybeUninit::<T>::assume_init_ref ](m: &MaybeUninit<T>) -> (ret: &T)
    requires m.mem_contents().is_init(),
    ensures ret == m.mem_contents().value(),
    opens_invariants none
    no_unwind;

pub assume_specification<T>[ MaybeUninit::<T>::assume_init_mut ](m: &mut MaybeUninit<T>) -> (ret: &mut T)
    requires m.mem_contents().is_init(),
    ensures *ret == old(m).mem_contents().value(),
        final(m).mem_contents().is_init(),
        final(m).mem_contents().value() == *final(ret),
    opens_invariants none
    no_unwind;

// ---------------------------------------------------------------------------
// PBT wrappers (direct #[pbt] blocked: MaybeUninit params/returns have no
// sampling strategy, and the contracts compare the uninterp mem_contents()
// against MemContents constructors). The ghost state is pinned through
// `new` (Init(val)) and observed via the assume_init family; `uninit`'s
// own Uninit claim is unobservable in exec (no wrapper can check it).
// ---------------------------------------------------------------------------

/// `new` + `assume_init`/`assume_init_ref` round-trips at u32.
#[cfg(not(verus_verify_core))]
#[verifier::external_body]
#[pbt]
pub fn pbt_maybe_uninit_new_assume_init(v: u32) -> (ret: bool)
    ensures
        ret,
{
    let m = MaybeUninit::new(v);
    let by_ref = *unsafe { m.assume_init_ref() };
    by_ref == v && unsafe { m.assume_init() } == v
}

/// `assume_init_mut`: reads the initialized value and writes through.
#[cfg(not(verus_verify_core))]
#[verifier::external_body]
#[pbt]
pub fn pbt_maybe_uninit_assume_init_mut(v: u32, v2: u32) -> (ret: bool)
    ensures
        ret,
{
    let mut m = MaybeUninit::new(v);
    let r = unsafe { m.assume_init_mut() };
    let read_ok = *r == v;
    *r = v2;
    read_ok && unsafe { m.assume_init() } == v2
}

}
