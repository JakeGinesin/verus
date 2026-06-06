//! File 3: `#[pbt]` on the exec fn, using `User` (file 2) which itself uses
//! `Permission` (file 1). Nothing is re-declared here. The harness resolves
//! `User`'s strategy, exec-model conversion, and spec companion across files
//! by trait/path.
use crate::perms::Permission;
use crate::users::User;
use vstd::contrib::exec_spec::*;
use vstd::contrib::verus_pbt::*;
use vstd::prelude::*;

verus! {

impl User {
    #[pbt]
    #[verifier::external_body]
    pub fn is_valid(&self) -> (b: bool)
        ensures b == self.is_valid_spec(),
    {
        self.name_len > 0 && !matches!(self.perm, Permission::Revoked)
    }
}

}

#[cfg(test)]
mod bug_detection {
    //! Cross-file PBT: `User`/`is_valid_spec` live in `users.rs`, `Permission`
    //! in `perms.rs`. These tests drive a TestRunner directly to assert the
    //! generated cross-file machinery catches a buggy validator.
    use crate::perms::Permission;
    use crate::users::User;
    use proptest::prelude::*;
    use proptest::test_runner::{Config, TestError, TestRunner};
    use verus_pbt_runtime::{pbt_strategy, ToExecModel};

    fn ground_truth(u: &User) -> bool {
        u.name_len > 0 && !matches!(u.perm, Permission::Revoked)
    }

    fn buggy_is_valid(u: &User) -> bool {
        u.name_len > 0 // ignores Revoked
    }

    #[test]
    fn cross_file_strategy_and_companion_catch_bug() {
        let mut runner = TestRunner::new(Config { cases: 512, ..Config::default() });
        let result = runner.run(&pbt_strategy::<User>(), |u: User| {
            // ToExecModel<User> composes through ToExecModel<Permission>
            // (defined in perms.rs) by trait resolution across files.
            let exec = <User as ToExecModel>::to_exec_model(&u);
            prop_assert_eq!(buggy_is_valid(&u), exec.exec_is_valid_spec());
            Ok(())
        });
        assert!(matches!(result, Err(TestError::Fail(..))));
    }

    #[test]
    fn cross_file_correct_validator_passes() {
        let mut runner = TestRunner::new(Config { cases: 512, ..Config::default() });
        let result = runner.run(&pbt_strategy::<User>(), |u: User| {
            let exec = <User as ToExecModel>::to_exec_model(&u);
            prop_assert_eq!(exec.exec_is_valid_spec(), ground_truth(&u));
            Ok(())
        });
        assert!(result.is_ok(), "{:?}", result.map(|_| ()));
    }
}
