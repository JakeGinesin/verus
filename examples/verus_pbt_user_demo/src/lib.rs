//! Phase 2 demo: the true ideal — just `#[pbt]` on the exec fn.
//!
//! No `verus_pbt_unverified!` block, no `#[pbt_provide]`. The user writes
//! ordinary Verus and adds `#[pbt]` to the validator. The preprocessing pass
//! computes the closure of spec fns + types the contract reaches among
//! siblings (`is_valid_spec` -> `User` -> `Permission` -> `is_revoked`) and
//! folds them all into one engine block, generating the harness.
//!
//! `cargo verus verify` checks the spec layer; `cargo test` runs the
//! generated `pbt_User_is_valid` harness and catches the buggy body.

use vstd::contrib::exec_spec::*;
use vstd::contrib::verus_pbt::*;
use vstd::prelude::*;

verus! {

pub enum Permission {
    Read,
    Write,
    Admin,
    Revoked,
}

pub struct User {
    pub name_len: usize,
    pub perm: Permission,
    pub quota: u64,
}

impl Permission {
    pub open spec fn grants_write(&self) -> bool {
        match self {
            Permission::Write => true,
            Permission::Admin => true,
            _ => false,
        }
    }

    pub open spec fn is_revoked(&self) -> bool {
        match self {
            Permission::Revoked => true,
            _ => false,
        }
    }
}

impl User {
    pub open spec fn is_valid_spec(&self) -> bool {
        &&& self.name_len > 0
        &&& !self.perm.is_revoked()
        &&& (self.perm.grants_write() ==> self.quota > 0)
    }

    // The ONLY annotation the user adds. Correct impl; the bug_detection
    // test below exercises a deliberately-broken twin to prove PBT bites.
    #[pbt]
    #[verifier::external_body]
    pub fn is_valid(&self) -> (b: bool)
        ensures b == self.is_valid_spec(),
    {
        self.name_len > 0
            && !matches!(self.perm, Permission::Revoked)
            && (!matches!(self.perm, Permission::Write | Permission::Admin) || self.quota > 0)
    }
}

} // verus!

#[cfg(test)]
mod bug_detection {
    use super::*;
    use proptest::prelude::*;
    use proptest::test_runner::{Config, TestError, TestRunner};
    use verus_pbt_runtime::{pbt_strategy, ToExecModel};

    fn ground_truth(u: &User) -> bool {
        let revoked = matches!(u.perm, Permission::Revoked);
        let grants_write = matches!(u.perm, Permission::Write | Permission::Admin);
        u.name_len > 0 && !revoked && (!grants_write || u.quota > 0)
    }

    // A broken validator, checked against the closure-generated spec
    // companion, must be caught.
    fn buggy_is_valid(u: &User) -> bool {
        u.name_len > 0
    }

    #[test]
    fn pbt_catches_buggy_validator() {
        let mut runner = TestRunner::new(Config { cases: 512, ..Config::default() });
        let result = runner.run(&pbt_strategy::<User>(), |u: User| {
            let exec = <User as ToExecModel>::to_exec_model(&u);
            prop_assert_eq!(buggy_is_valid(&u), exec.exec_is_valid_spec());
            Ok(())
        });
        assert!(matches!(result, Err(TestError::Fail(..))));
    }

    #[test]
    fn pbt_correct_validator_passes() {
        let mut runner = TestRunner::new(Config { cases: 512, ..Config::default() });
        let result = runner.run(&pbt_strategy::<User>(), |u: User| {
            let exec = <User as ToExecModel>::to_exec_model(&u);
            prop_assert_eq!(u.is_valid(), exec.exec_is_valid_spec());
            prop_assert_eq!(exec.exec_is_valid_spec(), ground_truth(&u));
            Ok(())
        });
        assert!(result.is_ok(), "{:?}", result.map(|_| ()));
    }
}
