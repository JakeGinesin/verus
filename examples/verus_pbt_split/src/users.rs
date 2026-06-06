//! File 2: provides `User` (with a `Permission` field from file 1) and its
//! spec predicate, via `#[pbt_provide]`. The generated `ToExecModel<User>`
//! composes through file 1's `ToExecModel<Permission>` by trait resolution.
use crate::perms::Permission;
use vstd::contrib::exec_spec::*;
use vstd::contrib::verus_pbt::*;
use vstd::prelude::*;

verus! {

#[pbt_provide]
pub struct User {
    pub name_len: usize,
    pub perm: Permission,
}

impl User {
    pub open spec fn is_valid_spec(&self) -> bool {
        self.name_len > 0 && !self.perm.is_revoked()
    }
}

}
