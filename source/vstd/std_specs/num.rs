#![allow(unused_imports)]
// PBT in-place patch: spec fns are erased under a plain `cargo build` /
// `cargo test`, so this named import only resolves in verifier builds.
// PBT contracts that call `rust_div` / `rust_rem` evaluate against the
// `external_pbt_provide!` exec twins defined inside the signed macro
// module below.
#[cfg(verus_keep_ghost)]
use super::super::arithmetic::div_mod::{rust_div, rust_rem};
use super::super::prelude::*;
use super::super::wrapping::*;

use core::cmp::Ordering;

verus! {

/// The smallest multiple of `y` that is `>= x` (for `y > 0`), matching the value
/// std's `next_multiple_of` / `checked_next_multiple_of` compute.
pub open spec fn next_multiple_of(x: int, y: int) -> int
    recommends
        y > 0,
{
    if x % y == 0 {
        x
    } else {
        x + (y - x % y)
    }
}

} // verus!
macro_rules! num_specs {
    ($uN: ty, $iN: ty, $mod_u_tmp:ident, $mod_i_tmp:ident, $mod_u:ident, $mod_i:ident, $range:expr) => {
        verus! {

        // Unsigned ints (u8, u16, etc.)

        // Put in separate module to avoid name collisions.
        // Names don't matter - the user uses the stdlib functions.
        mod $mod_u_tmp {
            use super::*;

            #[pbt]
            pub assume_specification[<$uN as Clone>::clone](x: &$uN) -> (res: $uN)
                ensures res == x;

            #[cfg(verus_keep_ghost)]
            impl super::super::cmp::PartialEqSpecImpl for $uN {
                open spec fn obeys_eq_spec() -> bool {
                    true
                }

                open spec fn eq_spec(&self, other: &$uN) -> bool {
                    *self == *other
                }
            }

            #[cfg(verus_keep_ghost)]
            impl super::super::cmp::PartialOrdSpecImpl for $uN {
                open spec fn obeys_partial_cmp_spec() -> bool {
                    true
                }

                open spec fn partial_cmp_spec(&self, other: &$uN) -> Option<Ordering> {
                    if *self < *other {
                        Some(Ordering::Less)
                    } else if *self > *other {
                        Some(Ordering::Greater)
                    } else {
                        Some(Ordering::Equal)
                    }
                }
            }

            #[cfg(verus_keep_ghost)]
            impl super::super::cmp::OrdSpecImpl for $uN {
                open spec fn obeys_cmp_spec() -> bool {
                    true
                }

                open spec fn cmp_spec(&self, other: &$uN) -> Ordering {
                    if *self < *other {
                        Ordering::Less
                    } else if *self > *other {
                        Ordering::Greater
                    } else {
                        Ordering::Equal
                    }
                }
            }

            pub assume_specification[<$uN as PartialEq<$uN>>::eq](x: &$uN, y: &$uN) -> bool;

            pub assume_specification[<$uN as PartialEq<$uN>>::ne](x: &$uN, y: &$uN) -> bool;

            pub assume_specification[<$uN as Ord>::cmp](x: &$uN, y: &$uN) -> Ordering;

            pub assume_specification[<$uN as PartialOrd<$uN>>::partial_cmp](x: &$uN, y: &$uN) -> Option<Ordering>;

            pub assume_specification[<$uN as PartialOrd<$uN>>::lt](x: &$uN, y: &$uN) -> bool;

            pub assume_specification[<$uN as PartialOrd<$uN>>::le](x: &$uN, y: &$uN) -> bool;

            pub assume_specification[<$uN as PartialOrd<$uN>>::gt](x: &$uN, y: &$uN) -> bool;

            pub assume_specification[<$uN as PartialOrd<$uN>>::ge](x: &$uN, y: &$uN) -> bool;

            // PBT wrapper harnesses for the comparison-operator specs above.
            //
            // The bare `assume_specification`s carry no inline contract —
            // their meaning comes from the `PartialEqSpecImpl` /
            // `PartialOrdSpecImpl` / `OrdSpecImpl` trait impls (gated
            // `verus_keep_ghost`), so `#[pbt]` directly on them would have
            // nothing to check. Each wrapper restates the spec-impl
            // contract against the real trait method (convert.rs pattern).
            #[cfg(not(verus_verify_core))]
            #[verifier::external_body]
            #[pbt]
            pub fn pbt_cmp_eq(x: $uN, y: $uN) -> (ret: bool)
                ensures ret == (x == y),
            {
                <$uN as PartialEq<$uN>>::eq(&x, &y)
            }

            #[cfg(not(verus_verify_core))]
            #[verifier::external_body]
            #[pbt]
            pub fn pbt_cmp_ne(x: $uN, y: $uN) -> (ret: bool)
                ensures ret == (x != y),
            {
                <$uN as PartialEq<$uN>>::ne(&x, &y)
            }

            #[cfg(not(verus_verify_core))]
            #[verifier::external_body]
            #[pbt]
            pub fn pbt_cmp_lt(x: $uN, y: $uN) -> (ret: bool)
                ensures ret == (x < y),
            {
                <$uN as PartialOrd<$uN>>::lt(&x, &y)
            }

            #[cfg(not(verus_verify_core))]
            #[verifier::external_body]
            #[pbt]
            pub fn pbt_cmp_le(x: $uN, y: $uN) -> (ret: bool)
                ensures ret == (x <= y),
            {
                <$uN as PartialOrd<$uN>>::le(&x, &y)
            }

            #[cfg(not(verus_verify_core))]
            #[verifier::external_body]
            #[pbt]
            pub fn pbt_cmp_gt(x: $uN, y: $uN) -> (ret: bool)
                ensures ret == (x > y),
            {
                <$uN as PartialOrd<$uN>>::gt(&x, &y)
            }

            #[cfg(not(verus_verify_core))]
            #[verifier::external_body]
            #[pbt]
            pub fn pbt_cmp_ge(x: $uN, y: $uN) -> (ret: bool)
                ensures ret == (x >= y),
            {
                <$uN as PartialOrd<$uN>>::ge(&x, &y)
            }

            // Mirrors `PartialOrdSpecImpl::partial_cmp_spec` for $uN.
            #[cfg(not(verus_verify_core))]
            #[verifier::external_body]
            #[pbt]
            pub fn pbt_cmp_partial_cmp(x: $uN, y: $uN) -> (ret: Option<Ordering>)
                ensures
                    ret == (if x < y {
                        Some(Ordering::Less)
                    } else if x > y {
                        Some(Ordering::Greater)
                    } else {
                        Some(Ordering::Equal)
                    }),
            {
                <$uN as PartialOrd<$uN>>::partial_cmp(&x, &y)
            }

            // Mirrors `OrdSpecImpl::cmp_spec` for $uN.
            #[cfg(not(verus_verify_core))]
            #[verifier::external_body]
            #[pbt]
            pub fn pbt_cmp_cmp(x: $uN, y: $uN) -> (ret: Ordering)
                ensures
                    ret == (if x < y {
                        Ordering::Less
                    } else if x > y {
                        Ordering::Greater
                    } else {
                        Ordering::Equal
                    }),
            {
                <$uN as Ord>::cmp(&x, &y)
            }

            #[verifier::allow_in_spec]
            #[cfg(not(verus_verify_core))]
            #[pbt]
            pub assume_specification[<$uN>::wrapping_add](x: $uN, y: $uN) -> $uN
                returns $mod_u::wrapping_add(x, y)
                opens_invariants none
                no_unwind;

            #[verifier::allow_in_spec]
            #[cfg(not(verus_verify_core))]
            #[pbt]
            pub assume_specification[<$uN>::wrapping_add_signed](x: $uN, y: $iN) -> $uN
                returns $mod_u::wrapping_add_signed(x, y)
                opens_invariants none
                no_unwind;

            #[verifier::allow_in_spec]
            #[cfg(not(verus_verify_core))]
            #[pbt]
            pub assume_specification[<$uN>::wrapping_sub](x: $uN, y: $uN) -> $uN
                returns $mod_u::wrapping_sub(x, y)
                opens_invariants none
                no_unwind;

            #[verifier::allow_in_spec]
            #[cfg(not(verus_verify_core))]
            #[pbt]
            pub assume_specification[<$uN>::wrapping_mul](x: $uN, y: $uN) -> $uN
                returns $mod_u::wrapping_mul(x, y)
                opens_invariants none
                no_unwind;

            #[verifier::allow_in_spec]
            #[cfg(not(verus_verify_core))]
            #[pbt]
            pub assume_specification[<$uN>::wrapping_shl](x: $uN, rhs: u32) -> $uN
                returns $mod_u::wrapping_shl(x, rhs)
                opens_invariants none
                no_unwind;

            #[verifier::allow_in_spec]
            #[cfg(not(verus_verify_core))]
            #[pbt]
            pub assume_specification[<$uN>::wrapping_shr](x: $uN, rhs: u32) -> $uN
                returns $mod_u::wrapping_shr(x, rhs)
                opens_invariants none
                no_unwind;

            #[verifier::allow_in_spec]
            #[cfg(not(verus_verify_core))]
            #[pbt]
            pub assume_specification[<$uN>::checked_add](x: $uN, y: $uN) -> Option<$uN>
                returns (
                    if x + y > <$uN>::MAX {
                        None
                    } else {
                        Some((x + y) as $uN)
                    }
                );

            #[verifier::allow_in_spec]
            #[cfg(not(verus_verify_core))]
            #[pbt]
            pub assume_specification[<$uN>::checked_add_signed](x: $uN, y: $iN) -> Option<$uN>
                returns (
                    if x + y > <$uN>::MAX || x + y < 0 {
                        None
                    } else {
                        Some((x + y) as $uN)
                    }
                );

            #[verifier::allow_in_spec]
            #[cfg(not(verus_verify_core))]
            #[pbt]
            pub assume_specification[<$uN>::checked_sub](x: $uN, y: $uN) -> Option<$uN>
                returns (
                    if x - y < 0 {
                        None
                    } else {
                        Some((x - y) as $uN)
                    }
                );

            #[verifier::allow_in_spec]
            #[cfg(not(verus_verify_core))]
            #[pbt]
            pub assume_specification[<$uN>::checked_mul](x: $uN, y: $uN) -> Option<$uN>
                returns (
                    if x * y > <$uN>::MAX {
                        None
                    } else {
                        Some((x * y) as $uN)
                    }
                );


            #[verifier::allow_in_spec]
            #[cfg(not(verus_verify_core))]
            // Exec twin for `next_multiple_of` (defined in the file's
            // top-level verus! block — a different engine expansion, so
            // the sibling fold can't see it). Body mirrors the spec over
            // SpecInt (euclidean % matching Verus `int` semantics).
            #[cfg(not(verus_verify_core))]
            external_pbt_provide! {
                fn next_multiple_of(x: int, y: int) -> int {
                    use ::verus_pbt::__pbt_int as bi;
                    if bi::eq(bi::rem(x.clone(), y.clone()), 0u8) {
                        x
                    } else {
                        bi::add(x.clone(), bi::sub(y.clone(), bi::rem(x, y)))
                    }
                }
            }

            #[pbt]
            pub assume_specification[<$uN>::checked_next_multiple_of](x: $uN, rhs: $uN) -> Option<$uN>
                returns (
                    if rhs == 0 {
                        None
                    } else if next_multiple_of(x as int, rhs as int) > <$uN>::MAX {
                        None
                    } else {
                        Some(next_multiple_of(x as int, rhs as int) as $uN)
                    }
                );

            pub open spec fn checked_div(x: $uN, y: $uN) -> Option<$uN> {
                if y == 0 {
                    None
                } else {
                    Some(x / y)
                }
            }

            #[verifier::when_used_as_spec(checked_div)]
            #[cfg(not(verus_verify_core))]
            #[pbt]
            pub assume_specification[<$uN>::checked_div](lhs: $uN, rhs: $uN) -> (result: Option<$uN>)
                ensures
                    result == checked_div(lhs, rhs);

            #[verifier::when_used_as_spec(checked_div)]
            #[cfg(not(verus_verify_core))]
            #[pbt]
            pub assume_specification[<$uN>::checked_div_euclid](lhs: $uN, rhs: $uN) -> (result: Option<$uN>)
                ensures
                    // checked_div is the same as checked_div_euclid for unsigned ints
                    result == checked_div(lhs, rhs);

            #[verifier::allow_in_spec]
            #[cfg(not(verus_verify_core))]
            #[pbt]
            pub assume_specification[<$uN>::checked_rem](lhs: $uN, rhs: $uN) -> Option<$uN>
                returns (
                    if rhs == 0 {
                        None
                    }
                    else {
                        Some((lhs % rhs) as $uN)
                    }
                );

            #[verifier::allow_in_spec]
            #[cfg(not(verus_verify_core))]
            #[pbt]
            pub assume_specification[<$uN>::checked_rem_euclid](lhs: $uN, rhs: $uN) -> Option<$uN>
                returns (
                    if rhs == 0 {
                        None
                    }
                    else {
                        Some((lhs % rhs) as $uN)
                    }
                );

            #[verifier::allow_in_spec]
            #[cfg(not(verus_verify_core))]
            #[pbt]
            pub assume_specification[<$uN>::saturating_add](x: $uN, y: $uN) -> $uN
                returns (
                    if x + y > <$uN>::MAX {
                        <$uN>::MAX
                    } else {
                        (x + y) as $uN
                    }
                );

            #[verifier::allow_in_spec]
            #[cfg(not(verus_verify_core))]
            #[pbt]
            pub assume_specification[<$uN>::saturating_sub](x: $uN, y: $uN) -> $uN
                returns (
                    if x - y < <$uN>::MIN {
                        <$uN>::MIN
                    } else {
                        (x - y) as $uN
                    }
                );

            #[verifier::allow_in_spec]
            #[cfg(not(verus_verify_core))]
            #[pbt]
            pub assume_specification[<$uN>::is_multiple_of](x: $uN, y: $uN) -> bool
                returns (
                    if y == 0 { x == 0 } else { x % y == 0 }
                );
        }

        // Signed ints (i8, i16, etc.)

        mod $mod_i_tmp {
            use super::*;



            #[pbt]
            pub assume_specification[<$iN as Clone>::clone](x: &$iN) -> (res: $iN)
                ensures res == x;

            #[cfg(verus_keep_ghost)]
            impl super::super::cmp::PartialEqSpecImpl for $iN {
                open spec fn obeys_eq_spec() -> bool {
                    true
                }

                open spec fn eq_spec(&self, other: &$iN) -> bool {
                    *self == *other
                }
            }

            #[cfg(verus_keep_ghost)]
            impl super::super::cmp::PartialOrdSpecImpl for $iN {
                open spec fn obeys_partial_cmp_spec() -> bool {
                    true
                }

                open spec fn partial_cmp_spec(&self, other: &$iN) -> Option<Ordering> {
                    if *self < *other {
                        Some(Ordering::Less)
                    } else if *self > *other {
                        Some(Ordering::Greater)
                    } else {
                        Some(Ordering::Equal)
                    }
                }
            }

            #[cfg(verus_keep_ghost)]
            impl super::super::cmp::OrdSpecImpl for $iN {
                open spec fn obeys_cmp_spec() -> bool {
                    true
                }

                open spec fn cmp_spec(&self, other: &$iN) -> Ordering {
                    if *self < *other {
                        Ordering::Less
                    } else if *self > *other {
                        Ordering::Greater
                    } else {
                        Ordering::Equal
                    }
                }
            }

            pub assume_specification[<$iN as PartialEq<$iN>>::eq](x: &$iN, y: &$iN) -> bool;

            pub assume_specification[<$iN as PartialEq<$iN>>::ne](x: &$iN, y: &$iN) -> bool;

            pub assume_specification[<$iN as Ord>::cmp](x: &$iN, y: &$iN) -> Ordering;

            pub assume_specification[<$iN as PartialOrd<$iN>>::partial_cmp](x: &$iN, y: &$iN) -> Option<Ordering>;

            pub assume_specification[<$iN as PartialOrd<$iN>>::lt](x: &$iN, y: &$iN) -> bool;

            pub assume_specification[<$iN as PartialOrd<$iN>>::le](x: &$iN, y: &$iN) -> bool;

            pub assume_specification[<$iN as PartialOrd<$iN>>::gt](x: &$iN, y: &$iN) -> bool;

            pub assume_specification[<$iN as PartialOrd<$iN>>::ge](x: &$iN, y: &$iN) -> bool;

            // PBT wrapper harnesses for the signed comparison-operator
            // specs above. See the $uN arm for the rationale. Edge-biased
            // sampling makes `MIN` / `-1` / `0` boundary pairs frequent.
            #[cfg(not(verus_verify_core))]
            #[verifier::external_body]
            #[pbt]
            pub fn pbt_cmp_eq(x: $iN, y: $iN) -> (ret: bool)
                ensures ret == (x == y),
            {
                <$iN as PartialEq<$iN>>::eq(&x, &y)
            }

            #[cfg(not(verus_verify_core))]
            #[verifier::external_body]
            #[pbt]
            pub fn pbt_cmp_ne(x: $iN, y: $iN) -> (ret: bool)
                ensures ret == (x != y),
            {
                <$iN as PartialEq<$iN>>::ne(&x, &y)
            }

            #[cfg(not(verus_verify_core))]
            #[verifier::external_body]
            #[pbt]
            pub fn pbt_cmp_lt(x: $iN, y: $iN) -> (ret: bool)
                ensures ret == (x < y),
            {
                <$iN as PartialOrd<$iN>>::lt(&x, &y)
            }

            #[cfg(not(verus_verify_core))]
            #[verifier::external_body]
            #[pbt]
            pub fn pbt_cmp_le(x: $iN, y: $iN) -> (ret: bool)
                ensures ret == (x <= y),
            {
                <$iN as PartialOrd<$iN>>::le(&x, &y)
            }

            #[cfg(not(verus_verify_core))]
            #[verifier::external_body]
            #[pbt]
            pub fn pbt_cmp_gt(x: $iN, y: $iN) -> (ret: bool)
                ensures ret == (x > y),
            {
                <$iN as PartialOrd<$iN>>::gt(&x, &y)
            }

            #[cfg(not(verus_verify_core))]
            #[verifier::external_body]
            #[pbt]
            pub fn pbt_cmp_ge(x: $iN, y: $iN) -> (ret: bool)
                ensures ret == (x >= y),
            {
                <$iN as PartialOrd<$iN>>::ge(&x, &y)
            }

            // Mirrors `PartialOrdSpecImpl::partial_cmp_spec` for $iN.
            #[cfg(not(verus_verify_core))]
            #[verifier::external_body]
            #[pbt]
            pub fn pbt_cmp_partial_cmp(x: $iN, y: $iN) -> (ret: Option<Ordering>)
                ensures
                    ret == (if x < y {
                        Some(Ordering::Less)
                    } else if x > y {
                        Some(Ordering::Greater)
                    } else {
                        Some(Ordering::Equal)
                    }),
            {
                <$iN as PartialOrd<$iN>>::partial_cmp(&x, &y)
            }

            // Mirrors `OrdSpecImpl::cmp_spec` for $iN.
            #[cfg(not(verus_verify_core))]
            #[verifier::external_body]
            #[pbt]
            pub fn pbt_cmp_cmp(x: $iN, y: $iN) -> (ret: Ordering)
                ensures
                    ret == (if x < y {
                        Ordering::Less
                    } else if x > y {
                        Ordering::Greater
                    } else {
                        Ordering::Equal
                    }),
            {
                <$iN as Ord>::cmp(&x, &y)
            }

            #[verifier::allow_in_spec]
            #[cfg(not(verus_verify_core))]
            #[pbt]
            pub assume_specification[<$iN>::wrapping_add](x: $iN, y: $iN) -> $iN
                returns $mod_i::wrapping_add(x, y)
                opens_invariants none
                no_unwind;

            #[verifier::allow_in_spec]
            #[cfg(not(verus_verify_core))]
            #[pbt]
            pub assume_specification[<$iN>::wrapping_add_unsigned](x: $iN, y: $uN) -> $iN
                returns $mod_i::wrapping_add_unsigned(x, y)
                opens_invariants none
                no_unwind;

            #[verifier::allow_in_spec]
            #[cfg(not(verus_verify_core))]
            #[pbt]
            pub assume_specification[<$iN>::wrapping_sub](x: $iN, y: $iN) -> $iN
                returns $mod_i::wrapping_sub(x, y)
                opens_invariants none
                no_unwind;

            #[verifier::allow_in_spec]
            #[cfg(not(verus_verify_core))]
            #[pbt]
            pub assume_specification[<$iN>::wrapping_mul](x: $iN, y: $iN) -> $iN
                returns $mod_i::wrapping_mul(x, y)
                opens_invariants none
                no_unwind;

            #[verifier::allow_in_spec]
            #[cfg(not(verus_verify_core))]
            #[pbt]
            pub assume_specification[<$iN>::wrapping_shl](x: $iN, rhs: u32) -> $iN
                returns $mod_i::wrapping_shl(x, rhs)
                opens_invariants none
                no_unwind;

            #[verifier::allow_in_spec]
            #[cfg(not(verus_verify_core))]
            #[pbt]
            pub assume_specification[<$iN>::wrapping_shr](x: $iN, rhs: u32) -> $iN
                returns $mod_i::wrapping_shr(x, rhs)
                opens_invariants none
                no_unwind;

            #[verifier::allow_in_spec]
            #[cfg(not(verus_verify_core))]
            #[pbt]
            pub assume_specification[<$iN>::checked_add](x: $iN, y: $iN) -> Option<$iN>
                returns (
                    if x + y > <$iN>::MAX || x + y < <$iN>::MIN {
                        None
                    } else {
                        Some((x + y) as $iN)
                    }
                );

            #[verifier::allow_in_spec]
            #[cfg(not(verus_verify_core))]
            #[pbt]
            pub assume_specification[<$iN>::checked_add_unsigned](x: $iN, y: $uN) -> Option<$iN>
                returns (
                    if x + y > <$iN>::MAX {
                        None
                    } else {
                        Some((x + y) as $iN)
                    }
                );

            #[verifier::allow_in_spec]
            #[cfg(not(verus_verify_core))]
            #[pbt]
            pub assume_specification[<$iN>::checked_sub](x: $iN, y: $iN) -> Option<$iN>
                returns (
                    if x - y > <$iN>::MAX || x - y < <$iN>::MIN {
                        None
                    } else {
                        Some((x - y) as $iN)
                    }
                );

            #[verifier::allow_in_spec]
            #[cfg(not(verus_verify_core))]
            #[pbt]
            pub assume_specification[<$iN>::checked_sub_unsigned](x: $iN, y: $uN) -> Option<$iN>
                returns (
                    if x - y < <$iN>::MIN {
                        None
                    } else {
                        Some((x - y) as $iN)
                    }
                );

            #[verifier::allow_in_spec]
            #[cfg(not(verus_verify_core))]
            #[pbt]
            pub assume_specification[<$iN>::checked_mul](x: $iN, y: $iN) -> Option<$iN>
                returns (
                    if x * y > <$iN>::MAX || x * y < <$iN>::MIN {
                        None
                    } else {
                        Some((x * y) as $iN)
                    }
                );

            // Exec twins for the cross-module spec fns `rust_div` /
            // `rust_rem` (arithmetic/div_mod.rs): bodies mirror the spec
            // definitions exactly, over SpecInt (whose __pbt_int div/rem
            // are euclidean, matching Verus `int` semantics).
            #[cfg(not(verus_verify_core))]
            external_pbt_provide! {
                fn rust_div(a: int, b: int) -> int {
                    use ::verus_pbt::__pbt_int as bi;
                    if bi::eq(a.clone(), 0u8) {
                        bi::lift(0u8)
                    } else if bi::gt(a.clone(), 0u8) {
                        bi::div(a, b)
                    } else {
                        bi::neg(bi::div(bi::neg(a), b))
                    }
                }
            }

            #[cfg(not(verus_verify_core))]
            external_pbt_provide! {
                fn rust_rem(a: int, b: int) -> int {
                    use ::verus_pbt::__pbt_int as bi;
                    if bi::eq(a.clone(), 0u8) {
                        bi::lift(0u8)
                    } else if bi::gt(a.clone(), 0u8) {
                        bi::rem(a, b)
                    } else {
                        bi::neg(bi::rem(bi::neg(a), b))
                    }
                }
            }

            #[verifier::allow_in_spec]
            #[cfg(not(verus_verify_core))]
            #[pbt]
            pub assume_specification[<$iN>::checked_div](lhs: $iN, rhs: $iN) -> Option<$iN>
                returns (
                    if rhs == 0 || (lhs == <$iN>::MIN && rhs == -1) {
                        None
                    } else {
                        Some(rust_div(lhs as int, rhs as int) as $iN)
                    }
                );

            #[verifier::allow_in_spec]
            #[cfg(not(verus_verify_core))]
            #[pbt]
            pub assume_specification[<$iN>::checked_div_euclid](lhs: $iN, rhs: $iN) -> Option<$iN>
                returns (
                    if rhs == 0 || (lhs == <$iN>::MIN && rhs == -1) {
                        None
                    } else {
                        Some((lhs / rhs) as $iN)
                    }
                );

            #[verifier::allow_in_spec]
            #[cfg(not(verus_verify_core))]
            #[pbt]
            pub assume_specification[<$iN>::checked_rem](lhs: $iN, rhs: $iN) -> Option<$iN>
                returns (
                    if rhs == 0 || (lhs == <$iN>::MIN && rhs == -1) {
                        None
                    } else {
                        Some(rust_rem(lhs as int, rhs as int) as $iN)
                    }
                );

            #[verifier::allow_in_spec]
            #[cfg(not(verus_verify_core))]
            #[pbt]
            pub assume_specification[<$iN>::checked_rem_euclid](lhs: $iN, rhs: $iN) -> Option<$iN>
                returns (
                    if rhs == 0 || (lhs == <$iN>::MIN && rhs == -1) {
                        None
                    } else {
                        Some((lhs % rhs) as $iN)
                    }
                );
        }

        }
    };
}

num_specs!(u8, i8, u8_specs_tmp, i8_specs_tmp, u8_specs, i8_specs, 0x100);
num_specs!(u16, i16, u16_specs_tmp, i16_specs_tmp, u16_specs, i16_specs, 0x1_0000);
num_specs!(u32, i32, u32_specs_tmp, i32_specs_tmp, u32_specs, i32_specs, 0x1_0000_0000);
num_specs!(u64, i64, u64_specs_tmp, i64_specs_tmp, u64_specs, i64_specs, 0x1_0000_0000_0000_0000);
num_specs!(
    u128,
    i128,
    u128_specs_tmp,
    i128_specs_tmp,
    u128_specs,
    i128_specs,
    0x1_0000_0000_0000_0000_0000_0000_0000_0000
);
num_specs!(
    usize,
    isize,
    usize_specs_tmp,
    isize_specs_tmp,
    usize_specs,
    isize_specs,
    (usize::MAX - usize::MIN + 1)
);


