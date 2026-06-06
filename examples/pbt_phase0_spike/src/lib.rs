//! Phase 0 spike: the cross-file glue traits and their `on_unimplemented`
//! diagnostics.
//!
//! KEY FINDING (drives Phase 1+ codegen): for `on_unimplemented` to fire,
//! the harness must call glue-trait items via FULLY-QUALIFIED TRAIT SYNTAX,
//! not method syntax. `x.to_exec_model()` yields a generic E0599
//! "no method found"; `<T as ToExecModel>::to_exec_model(&x)` yields the
//! custom "`{Self}` has no exec model ..." message. The macro therefore emits
//! the fully-qualified form.
//!
//! `check.rs` (compiled only under `--cfg pbt_spike_fail`) contains the
//! intentionally-failing references whose error text we verified renders as
//! the custom message:
//!
//! ```text
//! error[E0277]: `NotProvided` is not set up for property-based testing
//!   = note: add `#[pbt_provide]` to the definition of `NotProvided` ...
//! ```
//!
//! The positive path — a manually "provided" type implementing the three
//! glue traits — is exercised by the unit test below, confirming the traits
//! compose the way the macro will use them.

// `check.rs` is intentionally excluded (it does not compile). Build with
// `--cfg pbt_spike_fail` to reproduce the diagnostics manually.
#[cfg(pbt_spike_fail)]
pub mod check;

#[cfg(test)]
mod provided_path {
    use proptest::prelude::*;
    use proptest::strategy::BoxedStrategy;
    use verus_pbt_runtime::{PbtSpecCompanion, PbtStrategy, ToExecModel};

    // A user spec type...
    #[derive(Clone, Debug, PartialEq)]
    pub enum Permission {
        Read,
        Revoked,
    }

    // ...and the engine's exec model for it (hand-written here to mimic what
    // `#[pbt_provide]` will generate).
    #[derive(Clone, Debug, PartialEq)]
    pub enum ExecPermission {
        Read,
        Revoked,
    }

    impl PbtStrategy for Permission {
        type Strategy = BoxedStrategy<Permission>;
        fn pbt_strategy() -> Self::Strategy {
            prop_oneof![Just(Permission::Read), Just(Permission::Revoked)].boxed()
        }
    }

    impl ToExecModel for Permission {
        type Exec = ExecPermission;
        fn to_exec_model(&self) -> ExecPermission {
            match self {
                Permission::Read => ExecPermission::Read,
                Permission::Revoked => ExecPermission::Revoked,
            }
        }
    }

    impl PbtSpecCompanion for Permission {}

    impl ExecPermission {
        fn exec_is_revoked(&self) -> bool {
            matches!(self, ExecPermission::Revoked)
        }
    }

    // The spec companion as the macro will emit it: a runnable twin on the
    // user type that routes through ToExecModel.
    impl Permission {
        fn is_revoked_exec(&self) -> bool {
            self.to_exec_model().exec_is_revoked()
        }
    }

    #[test]
    fn provided_type_composes_through_all_three_traits() {
        // PROVIDED touch (forces PbtSpecCompanion bound when used in harness).
        let _: () = <Permission as PbtSpecCompanion>::PROVIDED;

        let mut runner = proptest::test_runner::TestRunner::default();
        let result = runner.run(&Permission::pbt_strategy(), |p| {
            // The exec companion agrees with a direct check.
            let via_companion = p.is_revoked_exec();
            let direct = matches!(p, Permission::Revoked);
            prop_assert_eq!(via_companion, direct);
            Ok(())
        });
        assert!(result.is_ok());
    }
}
