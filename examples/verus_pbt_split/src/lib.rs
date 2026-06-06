//! Phase 3 cross-file demo: spec types in `perms` + `users` (each
//! `#[pbt_provide]`'d), exec fn under test in `validate` (with `#[pbt]`).
//! The harness in `validate` reaches everything by trait/path resolution.
pub mod perms;
pub mod users;
pub mod validate;
