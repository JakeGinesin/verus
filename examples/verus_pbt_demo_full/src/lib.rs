// PBT DEMO: verus_pbt macro, verus_pbt attribute support

#[allow(unused_imports)] use vstd::contrib::exec_spec::*;
#[allow(unused_imports)] use vstd::contrib::verus_pbt::*;
use vstd::prelude::*;

verus! {

    // verus_pbt_unverified/verified

    // activated at macro expansion time, i.e. triggered by 
    // `cargo test` as well as `cargo verus`

    // the macro works in steps:
    // 
    // 1. use the expanded exec_spec macro support to translate specs fns
    //    in macro scope to exec fns
    // 
    // 2. for each ensures clause on all exec fns in scope, translate the
    //    requires clause to proptest's `prop_assume` and the ensures clause to
    //    proptest's `prop_assert`
    // 
    // 3. populate the dependent verus_pbt_runtime
    // 
    // 4. execute the proptest under cargo test; populate proptest-regressions 
    //    with the shrunk failure

    verus_pbt_verified! {

    spec fn all_under(s: Seq<u32>, k: u32) -> bool {
        forall |i: usize| 0 <= i < s.len() ==> s[i as int] <= k
    }

    fn under_check(s: &[u32], cap: u32) -> (r: u32)
        requires all_under(s.deep_view(), cap),
        ensures r <= cap,
    {
        cap
    }
        
    }

    // problems with the macro approach:
    // 
    // 1. the user must preemptively wrap all dependent specs in verus_pbt macro,
    //    and the errors if we need a spec inside the macro are hard to deal with
    // 
    // 2. with the enum/struct impl pattern, do you wrap the entire impl or just 
    //    the stuff you need? e.g. verus has verus! and verus_impl! 
    //    
    // 3. cross verus! handling of specs is rough 

    // therefore..... a better pattern is using attributes to label things you want 
    // to run PBTs on

    #[pbt]
    fn under_check_attr(s: &[u32], cap: u32) -> (r: u32)
        requires all_under_attr(s.deep_view(), cap),
        ensures r <= cap,
    {
        cap
    }

    // the attribute support attempts to recursively run exec_spec on requisite specs
    spec fn all_under_attr(s: Seq<u32>, k: u32) -> bool {
        forall |i: usize| 0 <= i < s.len() ==> s[i as int] <= k
    }

    // from vstd:
    #[pbt]
    #[verifier::external_body]
    fn u64_from_le_bytes(s: &[u8]) -> (x: u64)
        requires s@.len() == 8,
        ensures x == spec_u64_from_le_bytes(s@),
    {
        use core::convert::TryInto;
        u64::from_le_bytes(s.try_into().unwrap())
    }

    // can provide #[pbt_provide] in explicitly when required; 
    // compiler _should_ prompt you for these when needed
    #[pbt_provide]
    pub closed spec fn spec_u64_from_le_bytes(s: Seq<u8>) -> u64
        recommends s.len() == 8,
    {
        (s[0] as u64) | (s[1] as u64) << 8 | (s[2] as u64) << 16 | (s[3] as u64) << 24
            | (s[4] as u64) << 32 | (s[5] as u64) << 40 | (s[6] as u64) << 48
            | (s[7] as u64) << 56
    }

    // verus_pbt_bytes (for more vstd examples), verus_pbt_num (for vstd examples with assume_specification)

} // verus!