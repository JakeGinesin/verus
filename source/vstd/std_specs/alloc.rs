use super::super::prelude::*;
use super::super::raw_ptr::MemContents;

verus! {

// this is a bit of a hack; verus treats Global specially already,
// but putting this here helps Verus pick up all the trait impls for Global
#[cfg(feature = "alloc")]
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExGlobal(alloc::alloc::Global);

#[cfg(feature = "alloc")]
#[feature(liballoc_internals)]
pub assume_specification<T, const N: usize>[ alloc::boxed::box_assume_init_into_vec_unsafe ](
    vals: alloc::boxed::Box<core::mem::MaybeUninit<[T; N]>>,
) -> (result: alloc::vec::Vec<T>)
    requires
        vals.mem_contents() is Init,
    ensures
        vals.mem_contents() matches MemContents::Init(array) && result@ == array@,
;

#[cfg(feature = "alloc")]
#[feature(liballoc_internals)]
pub assume_specification<T>[ alloc::intrinsics::write_box_via_move ](
    _0: alloc::boxed::Box<core::mem::MaybeUninit<T>>,
    v: T,
) -> (result: alloc::boxed::Box<core::mem::MaybeUninit<T>>)
    ensures
        result.mem_contents() == MemContents::Init(v),
;

#[cfg(feature = "alloc")]
#[feature(liballoc_internals)]
pub assume_specification<T>[ alloc::boxed::Box::<T>::new_uninit ]() -> alloc::boxed::Box<
    core::mem::MaybeUninit<T>,
>
;

/// Composite replay for the liballoc-internal box-init specs:
/// `new_uninit` -> `write_box_via_move` (mem_contents becomes Init(v)) ->
/// `box_assume_init_into_vec_unsafe` (vec contents equal the array).
/// The ghost mem_contents state is pinned by the write and observed
/// through the final vec. (`new_uninit`'s own Uninit claim stays
/// unobservable.)
#[cfg(all(feature = "alloc", not(verus_verify_core)))]
#[verifier::external_body]
#[pbt]
pub fn pbt_box_init_into_vec(a: u32, b: u32, c: u32) -> (ret: bool)
    ensures
        ret,
{
    let boxed: alloc::boxed::Box<core::mem::MaybeUninit<[u32; 3]>> =
        alloc::boxed::Box::new_uninit();
    let boxed = alloc::intrinsics::write_box_via_move(boxed, [a, b, c]);
    let v: alloc::vec::Vec<u32> = alloc::boxed::box_assume_init_into_vec_unsafe(boxed);
    v == [a, b, c]
}

} // verus!
