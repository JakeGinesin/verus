//! File 1: provides `Permission` (and its spec fn) via `#[pbt_provide]`.
use vstd::contrib::exec_spec::*;
use vstd::contrib::verus_pbt::*;
use vstd::prelude::*;

verus! {

#[pbt_provide]
pub enum Permission {
    Read,
    Revoked,
}

impl Permission {
    pub open spec fn is_revoked(&self) -> bool {
        match self {
            Permission::Revoked => true,
            _ => false,
        }
    }
}

}
