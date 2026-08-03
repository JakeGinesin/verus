use super::super::prelude::*;
use core::convert::Infallible;
use core::ops::ControlFlow;
use core::ops::FromResidual;
use core::ops::Try;

verus! {

#[verifier::external_type_specification]
#[verifier::accept_recursive_types(B)]
#[verifier::reject_recursive_types_in_ground_variants(C)]
pub struct ExControlFlow<B, C>(ControlFlow<B, C>);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExInfallible(Infallible);

pub assume_specification<T, E>[ Result::<T, E>::branch ](result: Result<T, E>) -> (cf: ControlFlow<
    <Result<T, E> as Try>::Residual,
    <Result<T, E> as Try>::Output,
>)
    ensures
        cf == match result {
            Ok(v) => ControlFlow::Continue(v),
            Err(e) => ControlFlow::Break(Err(e)),
        },
    no_unwind
;

pub assume_specification<T>[ Option::<T>::branch ](option: Option<T>) -> (cf: ControlFlow<
    <Option<T> as Try>::Residual,
    <Option<T> as Try>::Output,
>)
    ensures
        cf == match option {
            Some(v) => ControlFlow::Continue(v),
            None => ControlFlow::Break(None),
        },
    no_unwind
;

pub assume_specification<T>[ Option::<T>::from_residual ](option: Option<Infallible>) -> (option2:
    Option<T>)
    ensures
        option.is_none(),
        option2.is_none(),
    no_unwind
;

pub uninterp spec fn spec_from<S, T>(value: T, ret: S) -> bool;

pub broadcast proof fn spec_from_blanket_identity<T>(t: T, s: T)
    ensures
        #[trigger] spec_from::<T, T>(t, s) ==> t == s,
{
    admit();
}

pub assume_specification<T, E, F: From<E>>[ Result::<T, F>::from_residual ](
    result: Result<Infallible, E>,
) -> (result2: Result<T, F>)
    ensures
        match (result, result2) {
            (Err(e), Err(e2)) => spec_from::<F, E>(e, e2),
            _ => false,
        },
    no_unwind
;

pub broadcast group group_control_flow_axioms {
    spec_from_blanket_identity,
}

// ---------------------------------------------------------------------------
// Composite PBT wrappers. The branch/from_residual contracts can't take a
// direct #[pbt]: their signatures go through `Try` associated-type
// projections (not a supported return shape) and `from_residual`'s ensures
// routes through the uninterp `spec_from`. Each wrapper restates the
// checkable composite claim at concrete types.
// ---------------------------------------------------------------------------

/// `Result::branch`: Ok maps to Continue(v), Err maps to Break(Err(e)).
#[cfg(not(verus_verify_core))]
#[verifier::external_body]
#[pbt]
pub fn pbt_result_branch(result: Result<u32, u8>) -> (ret: bool)
    ensures
        ret,
{
    let cf = result.branch();
    match (result, cf) {
        (Ok(v), ControlFlow::Continue(v2)) => v == v2,
        (Err(e), ControlFlow::Break(Err(e2))) => e == e2,
        _ => false,
    }
}

/// `Option::branch`: Some maps to Continue(v), None maps to Break(None).
#[cfg(not(verus_verify_core))]
#[verifier::external_body]
#[pbt]
pub fn pbt_option_branch(option: Option<u32>) -> (ret: bool)
    ensures
        ret,
{
    let cf = option.branch();
    match (option, cf) {
        (Some(v), ControlFlow::Continue(v2)) => v == v2,
        (None, ControlFlow::Break(None)) => true,
        _ => false,
    }
}

/// `Option::from_residual`: the only residual is `None` (Infallible is
/// uninhabited, so the input can't be sampled — constructed directly), and
/// the output must be `None` too.
#[cfg(not(verus_verify_core))]
#[verifier::external_body]
#[pbt]
pub fn pbt_option_from_residual() -> (ret: bool)
    ensures
        ret,
{
    let out: Option<u32> = Option::from_residual(None::<Infallible>);
    out.is_none()
}

/// `Result::from_residual` at `F = E = u8` (identity `From`): composite of
/// the assume_specification (`spec_from(e, e2)` holds and the output is
/// `Err`) with the trusted blanket axiom `spec_from::<T, T>(t, s) ==> t == s`,
/// giving the checkable claim `from_residual(Err(e)) == Err(e)`.
#[cfg(not(verus_verify_core))]
#[verifier::external_body]
#[pbt]
pub fn pbt_result_from_residual(e: u8) -> (ret: bool)
    ensures
        ret,
{
    let out: Result<u32, u8> = Result::from_residual(Err(e));
    out == Err(e)
}

} // verus!
