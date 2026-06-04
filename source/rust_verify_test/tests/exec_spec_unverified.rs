// Tests for additional features in the exec_spec_unverified! macro.
#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

const IMPORTS: &str = code_str! {
    #[allow(unused_imports)] use vstd::prelude::*;
    #[allow(unused_imports)] use vstd::contrib::exec_spec::*;
};

test_verify_one_file! {
    // Test quantifiers with multiple variables
    #[test] test_exec_spec_unverified_multivar_quant IMPORTS.to_string() + verus_code_str! {
        exec_spec_unverified! {
            spec fn spec_five(x1: u8, x2: u8, x3: u8, x4: u8, x5: u8) -> bool {
                x1 == x2 && x3 != x4 && x3 != x5 && x5 != x2
            }

            spec fn test_five_forall() -> bool {
                forall |x1: u8, x2: u8, x3: u8, x4: u8, x5: u8| 0 <= x1 < 10 && 0 <= x2 < 10 && 0 <= x3 < 10 && 0 <= x4 < 10 && 0 <= x5 < 10 ==> spec_five(x1, x2, x3, x4, x5)
            }

            spec fn test_five_exists() -> bool {
                exists |x1: u8, x2: u8, x3: u8, x4: u8, x5: u8| 0 <= x1 < 10 && 0 <= x2 < 10 && 0 <= x3 < 10 && 0 <= x4 < 10 && 0 <= x5 < 10 && spec_five(x1, x2, x3, x4, x5)
            }

            spec fn test_vec_vec_forall(v: Seq<Seq<u8>>) -> bool {
                forall |i: usize, j: usize| 0 <= i < v.len() && 0 <= j < v[i as int].len() ==> v[i as int][j as int] != 0
            }

            spec fn test_vec_vec_exists(v: Seq<Seq<u8>>) -> bool {
                exists |i: usize, j: usize| 0 <= i < v.len() && 0 <= j < v[i as int].len() && v[i as int][j as int] != 0
            }

            spec fn test_diff_bounds_forall() -> bool {
                forall |i: usize, j: usize| #![trigger i + j] 0 <= i < 2 && 5 <= j < 7 ==> i + j <= 2 * j
            }

            spec fn test_diff_bounds_exists() -> bool {
                exists |i: usize, j: usize| #![trigger i + j] 0 <= i < 2 && 5 <= j < 7 && 2 * j < i + j
            }

            spec fn test_diff_bounds_four_forall() -> bool {
                forall |i1: u8, i2: u8, i3: u8, i4: u8| #![trigger i1 + i2 + i3 + i4] 1 <= i1 < 2 && 2 <= i2 < 3 && 3 <= i3 < 4 && 4 <= i4 < 5 ==> i1 + i2 + i3 + i4 != 10
            }

            spec fn test_diff_bounds_four_exists() -> bool {
                exists |i1: u8, i2: u8, i3: u8, i4: u8| #![trigger i1 + i2 + i3 + i4] 1 <= i1 < 2 && 2 <= i2 < 3 && 3 <= i3 < 4 && 4 <= i4 < 5 && i1 + i2 + i3 + i4 == 10
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    // Test quantifiers over char
    #[test] test_exec_spec_unverified_char_quant IMPORTS.to_string() + verus_code_str! {
        exec_spec_unverified! {
            spec fn forall_char_le_le() -> bool {
                forall |c: char| #![trigger c as u32] 'A' <= c <= 'Z' ==> c != '!'
            }

            spec fn forall_char_lt_le() -> bool {
                forall |c: char| #![trigger c as u32] 'A' < c <= 'Z' ==> c != '!'
            }

            spec fn forall_char_le_lt() -> bool {
                forall |c: char| #![trigger c as u32] 'A' <= c < 'Z' ==> c != '!'
            }

            spec fn forall_char_lt_lt() -> bool {
                forall |c: char| #![trigger c as u32] 'A' < c < 'Z' ==> c != '!'
            }

            spec fn exists_char_le_le() -> bool {
                exists |c: char| #![trigger c as u32] 'A' <= c <= 'Z' && c == 'K'
            }

            spec fn exists_char_lt_le() -> bool {
                exists |c: char| #![trigger c as u32] 'A' < c <= 'Z' && c == 'K'
            }

            spec fn exists_char_le_lt() -> bool {
                exists |c: char| #![trigger c as u32] 'A' <= c < 'Z' && c == 'K'
            }

            spec fn exists_char_lt_lt() -> bool {
                exists |c: char| #![trigger c as u32] 'A' < c < 'Z' && c == 'K'
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    // Test using exec_spec_verified! and exec_spec_unverified! macros together
    #[test] test_exec_spec_mixed_modes IMPORTS.to_string() + verus_code_str! {
        exec_spec_verified! {
            struct X {
                a: u32,
                b: bool
            }

            spec fn x_test1(x1: X, x2: X) -> bool {
                x1 == x2 && !x1.b
            }
        }

        exec_spec_unverified! {
            spec fn forall_char_le_le() -> bool {
                forall |c: char| #![trigger c as u32] 'A' <= c <= 'Z' ==> c != '!'
            }

            spec fn x_test2(x: X) -> u32 {
                x.a
            }

            spec fn x_test3(x1: X, x2: X) -> bool {
                x_test1(x1, x2)
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    // Test ensuring that specification is generated on code compiled from exec_spec_unverified!
    #[test] test_exec_spec_unverified_spec IMPORTS.to_string() + verus_code_str! {
        exec_spec_verified! {
            spec fn test1() -> bool {
                true
            }
        }

        exec_spec_unverified! {
            spec fn test2() -> bool {
                true
            }
        }

        fn exc() {
            let res1 = exec_test1();
            assert(res1);

            let res2 = exec_test2();
            assert(res2);
        }
    } => Ok(())
}

// ---------------------------------------------------------------------------
// Auth-spec port (representative subset)
//
// Each test below ports a small slice of the AWS auth spec into a form that
// `exec_spec_unverified!` can compile today. Items that need user-side
// rewrites (e.g. `e is V` -> `match`, `ghost enum` -> `pub enum`) are noted
// in the comment for each test.
// ---------------------------------------------------------------------------

test_verify_one_file! {
    /// `OperationType` ghost enum -> plain enum + the top-level
    /// `is_tagging_operation` predicate.
    ///
    /// User-side rewrites:
    ///   - `pub ghost enum OperationType { ... }` -> `pub enum OperationType { ... }`
    ///   - `op is CreateResource || op is TagResource` -> `match op { ... }`
    #[test] test_exec_spec_authspec_operation_type IMPORTS.to_string() + verus_code_str! {
        exec_spec_unverified! {
            pub enum OperationType {
                Default,
                NonSpecificResourceOperation,
                CreateResource,
                DeleteResource,
                TagResource,
                UntagResource,
                ListTags,
            }

            pub open spec fn is_tagging_operation(op: OperationType) -> bool {
                match op {
                    OperationType::CreateResource => true,
                    OperationType::TagResource => true,
                    _ => false,
                }
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    /// `is_unsafe_coral_char` and `is_valid_coral_key_start` — pure char
    /// predicates. These compile as-is.
    #[test] test_exec_spec_authspec_coral_chars IMPORTS.to_string() + verus_code_str! {
        exec_spec_unverified! {
            pub open spec fn is_unsafe_coral_char(c: char) -> bool {
                c == '[' || c == ']' || c == '-' || c == ':' || c == '\\' || c == '.'
            }

            pub open spec fn is_valid_coral_key_start(c: char) -> bool {
                ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z') || c == '_'
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    /// `is_valid_coral_key` — uses an unbounded `forall` that the macro can
    /// only compile to an executable form when the quantifier is bounded.
    /// We rewrite it to a bounded quantifier over `key.len()`.
    ///
    /// User-side rewrites:
    ///   - `forall |c: char| key.contains(c) ==> !is_unsafe_coral_char(c)`
    ///     -> `forall |i: usize| 0 <= i < key.len() ==> !is_unsafe_coral_char(key[i as int])`
    #[test] test_exec_spec_authspec_coral_key IMPORTS.to_string() + verus_code_str! {
        exec_spec_unverified! {
            pub open spec fn is_unsafe_coral_char(c: char) -> bool {
                c == '[' || c == ']' || c == '-' || c == ':' || c == '\\' || c == '.'
            }

            pub open spec fn is_valid_coral_key_start(c: char) -> bool {
                ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z') || c == '_'
            }

            pub open spec fn is_valid_coral_key(key: SpecString) -> bool {
                key.len() > 0
                && is_valid_coral_key_start(key[0])
                && forall |i: usize|
                    #![trigger key[i as int]]
                    0 <= i < key.len() ==> !is_unsafe_coral_char(key[i as int])
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    /// Minimal `Path` enum + `is_valid` recursive impl method.
    ///
    /// User-side rewrites:
    ///   - `Box<Path>` -> a flat representation. We use a sequence of keys
    ///     (`Seq<SpecString>`) for the structure path instead of nesting,
    ///     since `Box` of a user type is not currently compilable.
    ///   - `Path::Value { key } => is_valid_coral_key(key)` works as-is on a
    ///     non-recursive variant.
    #[test] test_exec_spec_authspec_path IMPORTS.to_string() + verus_code_str! {
        exec_spec_unverified! {
            pub open spec fn is_unsafe_coral_char(c: char) -> bool {
                c == '[' || c == ']' || c == '-' || c == ':' || c == '\\' || c == '.'
            }

            pub open spec fn is_valid_coral_key_start(c: char) -> bool {
                ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z') || c == '_'
            }

            pub open spec fn is_valid_coral_key(key: SpecString) -> bool {
                key.len() > 0
                && is_valid_coral_key_start(key[0])
                && forall |i: usize|
                    #![trigger key[i as int]]
                    0 <= i < key.len() ==> !is_unsafe_coral_char(key[i as int])
            }

            // Flat representation of `Path` to avoid Box recursion.
            pub struct Path {
                pub segments: Seq<SpecString>,
            }

            impl Path {
                pub open spec fn is_valid(&self) -> bool {
                    self.segments.len() > 0
                    && forall |i: usize|
                        #![trigger self.segments[i as int]]
                        0 <= i < self.segments.len() ==> is_valid_coral_key(self.segments[i as int])
                }
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    /// Port of `Action::is_pass_role_action` and `Operation::is_tagging_operation`.
    ///
    /// User-side rewrites:
    ///   - `self.operation_type is UntagResource || self.operation_type is TagResource`
    ///     -> `match self.operation_type { ... }`
    ///   - `"PassRole"@` SpecString literal works as-is.
    #[test] test_exec_spec_authspec_action_predicates IMPORTS.to_string() + verus_code_str! {
        exec_spec_unverified! {
            pub enum OperationType {
                Default,
                CreateResource,
                TagResource,
                UntagResource,
                ListTags,
            }

            pub struct Action {
                pub name: SpecString,
            }

            impl Action {
                pub open spec fn is_pass_role_action(&self) -> bool {
                    self.name == "PassRole"@
                }
            }

            pub struct Operation {
                pub operation_type: OperationType,
            }

            impl Operation {
                pub open spec fn is_tagging_operation(&self) -> bool {
                    match self.operation_type {
                        OperationType::UntagResource => true,
                        OperationType::TagResource => true,
                        _ => false,
                    }
                }
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    /// `ContextKeyReference::get_id` and `is_required` ported as a method
    /// on a non-generic enum.
    ///
    /// User-side rewrites:
    ///   - `self !is PassRoleKey` recommends -> `match self { PassRoleKey => false, _ => true }`
    ///   - `arbitrary()` in spec fns is replaced with a concrete dummy value
    ///     in this port, since `arbitrary()` is a spec-only function with no
    ///     executable counterpart.
    ///   - The `PassRoleKey` variant in the original carries a
    ///     `ResourceReference`; we drop that field here for the port since
    ///     `ResourceReference` is itself non-trivial to port.
    #[test] test_exec_spec_authspec_context_key_ref IMPORTS.to_string() + verus_code_str! {
        exec_spec_unverified! {
            pub enum ContextKeyReference {
                ServiceSpecificKey { id: SpecString, is_required: bool },
                TagKeys,
                PassRoleKey { passed_to_service: SpecString },
            }

            impl ContextKeyReference {
                pub open spec fn is_required(&self) -> bool {
                    match self {
                        ContextKeyReference::ServiceSpecificKey { is_required, .. } => *is_required,
                        ContextKeyReference::TagKeys => true,
                        ContextKeyReference::PassRoleKey { .. } => true,
                    }
                }
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    /// `ResourceExceptionFlag` enum + `Resource::has_exception` and
    /// `is_taggable`. Tests that a method calls a `Seq::contains`-style
    /// builtin on a sequence of user-defined enum values.
    ///
    /// User-side rewrites:
    ///   - `ghost enum ResourceExceptionFlag` -> plain enum.
    ///   - `ghost struct Resource` simplified: only the field used here.
    #[test] test_exec_spec_authspec_resource_exceptions IMPORTS.to_string() + verus_code_str! {
        exec_spec_unverified! {
            pub enum ResourceExceptionFlag {
                NoRegionInArn,
                NotTaggable,
                NameNotInArn,
                AllowColonsInIdentifiers,
            }

            pub struct Resource {
                pub exceptions: Seq<ResourceExceptionFlag>,
            }

            impl Resource {
                pub open spec fn has_exception(&self, flag: ResourceExceptionFlag) -> bool {
                    self.exceptions.contains(flag)
                }

                pub open spec fn is_taggable(&self) -> bool {
                    !self.exceptions.contains(ResourceExceptionFlag::NotTaggable)
                }
            }
        }
    } => Ok(())
}
