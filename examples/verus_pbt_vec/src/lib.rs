//! PBT demo for `vstd::std_specs::vec::vec_index`. The contract is
//! structurally identical to `slice_index_get`, which is already PBT'd; this
//! demo shows the same harness shape works for `&Vec<T>` parameters once
//! generics are pinned via `#[pbt(T = u64)]`.

use vstd::prelude::*;
use vstd::contrib::verus_pbt::*;

verus! {

#[pbt(T = u64)]
#[verifier::external_body]
pub exec fn vec_index<T>(v: Vec<T>, i: usize) -> (element: T)
    requires
        i < v.view().len(),
    ensures
        element == v.view().index(i as int),
{
    let r = v[i];
    r
}

}
