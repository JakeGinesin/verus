/// Defines the specifications for operator traits.
///
/// This file specifies the behavior of operator traits for integers when the trait method is invoked.
/// Preconditions for some operator trait method are required to prevent overflow and underflow.
///
/// - For primitive integer types, the expression `lhs $op rhs` is directly handled by the verifier
///   without relying on trait specifications defined here, avoiding additional trigger costs.
///   However, calling `lhs.add(rhs)` or T::add(lhs, rhs) will trigger the corresponding trait method
/// - If an operator is overloaded for a custom type, both `lhs $op rhs` and `lhs.add(rhs)` invoke the
///   corresponding trait method for verification.
///   and its preconditions are enforced.
/// - Since this crate (vstd) defines the extension traits AddSpec, SubSpec, etc.,
///   this crate is also allowed to implement these extension traits for known std types
///   like u8, u16, etc.  Rust's coherence rules prevent other crates from implementing
///   these extension traits for std types.  If this is a problem, as a last-resort workaround,
///   other crates can assume axioms about the extension traits as an alternative to implementing
///   them directly.
use super::super::prelude::*;

macro_rules! def_un_ops_spec {
    ($trait:path, $extrait: ident, $spec_trait:ident, $impl_trait:ident, $fun:ident, $obeys:ident, $req:ident, $spec:ident) => {
        $crate::vstd::prelude::verus! {
            #[verifier::external_trait_specification]
            #[verifier::external_trait_extension($spec_trait via $impl_trait)]
            pub trait $extrait {
                type ExternalTraitSpecificationFor: $trait;

                type Output;

                spec fn $obeys() -> bool;

                spec fn $req(self) -> bool
                    where Self: Sized;

                spec fn $spec(self) -> Self::Output
                    where Self: Sized;

                fn $fun(self) -> (ret: Self::Output)
                    requires
                        self.$req(),
                    ensures
                        Self::$obeys() ==> ret == self.$spec();
            }
        }
};
}

macro_rules! def_bin_ops_spec {
    ($trait:path, $extrait: ident, $spec_trait:ident, $impl_trait:ident, $fun:ident, $obeys:ident, $req:ident, $spec:ident) => {
        $crate::vstd::prelude::verus! {
            #[verifier::external_trait_specification]
            #[verifier::external_trait_extension($spec_trait via $impl_trait)]
            pub trait $extrait<Rhs = Self> {
                type ExternalTraitSpecificationFor: $trait<Rhs>;

                type Output;

                spec fn $obeys() -> bool;

                spec fn $req(self, rhs: Rhs) -> bool
                    where Self: Sized;

                spec fn $spec(self, rhs: Rhs) -> Self::Output
                    where Self: Sized;

                fn $fun(self, rhs: Rhs) -> (ret: Self::Output)
                    requires
                        self.$req(rhs),
                    ensures
                        Self::$obeys() ==> ret == self.$spec(rhs);
            }
        }
};
}

macro_rules! def_bin_ops_assign_spec {
    ($trait:path, $extrait: ident, $spec_trait:ident, $impl_trait:ident, $fun:ident, $obeys:ident, $req:ident, $spec:ident) => {
        $crate::vstd::prelude::verus! {
            #[verifier::external_trait_specification]
            #[verifier::external_trait_extension($spec_trait via $impl_trait)]
            pub trait $extrait<Rhs = Self> {
                type ExternalTraitSpecificationFor: $trait<Rhs>;

                spec fn $obeys() -> bool;

                spec fn $req(&self, rhs: Rhs) -> bool;

                spec fn $spec(&self, rhs: Rhs) -> &Self;

                fn $fun(&mut self, rhs: Rhs)
                    requires
                        self.$req(rhs),
                    ensures
                        Self::$obeys() ==> &*final(self) == old(self).$spec(rhs);
            }
        }
};
}

def_un_ops_spec!(
    core::ops::Neg,
    ExNeg,
    NegSpec,
    NegSpecImpl,
    neg,
    obeys_neg_spec,
    neg_req,
    neg_spec
);

def_un_ops_spec!(
    core::ops::Not,
    ExNot,
    NotSpec,
    NotSpecImpl,
    not,
    obeys_not_spec,
    not_req,
    not_spec
);

def_bin_ops_spec!(
    core::ops::Add,
    ExAdd,
    AddSpec,
    AddSpecImpl,
    add,
    obeys_add_spec,
    add_req,
    add_spec
);

def_bin_ops_assign_spec!(
    core::ops::AddAssign,
    ExAddAssign,
    AddAssignSpec,
    AddAssignSpecImpl,
    add_assign,
    obeys_add_assign_spec,
    add_assign_req,
    add_assign_spec
);

def_bin_ops_spec!(
    core::ops::Sub,
    ExSub,
    SubSpec,
    SubSpecImpl,
    sub,
    obeys_sub_spec,
    sub_req,
    sub_spec
);

def_bin_ops_assign_spec!(
    core::ops::SubAssign,
    ExSubAssign,
    SubAssignSpec,
    SubAssignSpecImpl,
    sub_assign,
    obeys_sub_assign_spec,
    sub_assign_req,
    sub_assign_spec
);

def_bin_ops_spec!(
    core::ops::Mul,
    ExMul,
    MulSpec,
    MulSpecImpl,
    mul,
    obeys_mul_spec,
    mul_req,
    mul_spec
);

def_bin_ops_assign_spec!(
    core::ops::MulAssign,
    ExMulAssign,
    MulAssignSpec,
    MulAssignSpecImpl,
    mul_assign,
    obeys_mul_assign_spec,
    mul_assign_req,
    mul_assign_spec
);

def_bin_ops_spec!(
    core::ops::Div,
    ExDiv,
    DivSpec,
    DivSpecImpl,
    div,
    obeys_div_spec,
    div_req,
    div_spec
);

def_bin_ops_assign_spec!(
    core::ops::DivAssign,
    ExDivAssign,
    DivAssignSpec,
    DivAssignSpecImpl,
    div_assign,
    obeys_div_assign_spec,
    div_assign_req,
    div_assign_spec
);

def_bin_ops_spec!(
    core::ops::Rem,
    ExRem,
    RemSpec,
    RemSpecImpl,
    rem,
    obeys_rem_spec,
    rem_req,
    rem_spec
);

def_bin_ops_assign_spec!(
    core::ops::RemAssign,
    ExRemAssign,
    RemAssignSpec,
    RemAssignSpecImpl,
    rem_assign,
    obeys_rem_assign_spec,
    rem_assign_req,
    rem_assign_spec
);

def_bin_ops_spec!(
    core::ops::BitAnd,
    ExBitAnd,
    BitAndSpec,
    BitAndSpecImpl,
    bitand,
    obeys_bitand_spec,
    bitand_req,
    bitand_spec
);

def_bin_ops_assign_spec!(
    core::ops::BitAndAssign,
    ExBitAndAssign,
    BitAndAssignSpec,
    BitAndAssignSpecImpl,
    bitand_assign,
    obeys_bitand_assign_spec,
    bitand_assign_req,
    bitand_assign_spec
);

def_bin_ops_spec!(
    core::ops::BitOr,
    ExBitOr,
    BitOrSpec,
    BitOrSpecImpl,
    bitor,
    obeys_bitor_spec,
    bitor_req,
    bitor_spec
);

def_bin_ops_assign_spec!(
    core::ops::BitOrAssign,
    ExBitOrAssign,
    BitOrAssignSpec,
    BitOrAssignSpecImpl,
    bitor_assign,
    obeys_bitor_assign_spec,
    bitor_assign_req,
    bitor_assign_spec
);

def_bin_ops_spec!(
    core::ops::BitXor,
    ExBitXor,
    BitXorSpec,
    BitXorSpecImpl,
    bitxor,
    obeys_bitxor_spec,
    bitxor_req,
    bitxor_spec
);

def_bin_ops_assign_spec!(
    core::ops::BitXorAssign,
    ExBitXorAssign,
    BitXorAssignSpec,
    BitXorAssignSpecImpl,
    bitxor_assign,
    obeys_bitxor_assign_spec,
    bitxor_assign_req,
    bitxor_assign_spec
);

def_bin_ops_spec!(
    core::ops::Shl,
    ExShl,
    ShlSpec,
    ShlSpecImpl,
    shl,
    obeys_shl_spec,
    shl_req,
    shl_spec
);

def_bin_ops_assign_spec!(
    core::ops::ShlAssign,
    ExShlAssign,
    ShlAssignSpec,
    ShlAssignSpecImpl,
    shl_assign,
    obeys_shl_assign_spec,
    shl_assign_req,
    shl_assign_spec
);

def_bin_ops_spec!(
    core::ops::Shr,
    ExShr,
    ShrSpec,
    ShrSpecImpl,
    shr,
    obeys_shr_spec,
    shr_req,
    shr_spec
);

def_bin_ops_assign_spec!(
    core::ops::ShrAssign,
    ExShrAssign,
    ShrAssignSpec,
    ShrAssignSpecImpl,
    shr_assign,
    obeys_shr_assign_spec,
    shr_assign_req,
    shr_assign_spec
);

macro_rules! def_uop_impls {
    ($trait:path, $impl_trait:ident, $fun:ident, $obeys:ident, $req:ident, $spec:ident, $self:ident, [$(($typ:ty, $req_expr:expr, $spec_expr:expr))*]) => {
        $crate::vstd::prelude::verus! {
            $(
                impl $impl_trait for $typ {
                    open spec fn $obeys() -> bool {
                        true
                    }

                    open spec fn $req($self) -> bool {
                        $req_expr
                    }

                    open spec fn $spec($self) -> Self::Output {
                        $spec_expr
                    }
                }

                pub assume_specification[ <$typ as $trait>::$fun ](x: $typ) -> $typ;
            )*
        }
};
}

macro_rules! def_bop_impls {
    ($trait:path, $impl_trait:ident, $fun:ident, $obeys:ident, $req:ident, $spec:ident, $self:ident, $rhs:ident, [$(($typ:ty, $req_expr:expr, $spec_expr:expr))*]) => {
        $crate::vstd::prelude::verus! {
            $(
                impl $impl_trait for $typ {
                    open spec fn $obeys() -> bool {
                        true
                    }

                    open spec fn $req($self, $rhs: $typ) -> bool {
                        $req_expr
                    }

                    open spec fn $spec($self, $rhs: $typ) -> Self::Output {
                        $spec_expr
                    }
                }

                pub assume_specification[ <$typ as $trait>::$fun ](x: $typ, y: $typ) -> $typ;
            )*
        }
};
}

macro_rules! def_bop_assign_impls {
    ($trait:path, $impl_trait:ident, $fun:ident, $obeys:ident, $req:ident, $spec:ident, $self:ident, $rhs:ident, [$(($typ:ty, $req_expr:expr, $spec_expr:expr))*]) => {
        $crate::vstd::prelude::verus! {
            $(
                impl $impl_trait for $typ {
                    open spec fn $obeys() -> bool {
                        true
                    }

                    open spec fn $req(&$self, $rhs: $typ) -> bool {
                        $req_expr
                    }

                    open spec fn $spec(&$self, $rhs: $typ) -> &Self {
                        &$spec_expr
                    }
                }

                pub assume_specification[ <$typ as $trait>::$fun ](x: &mut $typ, y: $typ);
            )*
        }
};
}

macro_rules! def_uop_impls_no_check {
    ($trait:path, $impl_trait:ident, $fun:ident, $obeys:ident, $req:ident, $spec:ident, $self:ident, $op:tt, [$($typ:ty)*]) => {
        $crate::vstd::prelude::verus! {
            def_uop_impls!($trait, $impl_trait, $fun, $obeys, $req, $spec, $self, [
                $(
                    (
                        $typ,
                        true,
                        $op $self
                    )
                )*
            ]);
        }
};
}

macro_rules! def_uop_impls_check_overflow {
    ($trait:path, $impl_trait:ident, $fun:ident, $obeys:ident, $req:ident, $spec:ident, $self:ident, $op:tt, [$($typ:ty)*]) => {
        $crate::vstd::prelude::verus! {
            def_uop_impls!($trait, $impl_trait, $fun, $obeys, $req, $spec, $self, [
                $(
                    (
                        $typ,
                        ($op $self) as $typ == ($op $self),
                        ($op $self) as $typ
                    )
                )*
            ]);
        }
};
}

macro_rules! def_bop_impls_no_check {
    ($trait:path, $impl_trait:ident, $fun:ident, $obeys:ident, $req:ident, $spec:ident, $self:ident, $rhs:ident, $op:tt, [$($typ:ty)*]) => {
        $crate::vstd::prelude::verus! {
            def_bop_impls!($trait, $impl_trait, $fun, $obeys, $req, $spec, $self, $rhs, [
                $(
                    (
                        $typ,
                        true,
                        $self $op $rhs
                    )
                )*
            ]);
        }
};
}

macro_rules! def_bop_assign_impls_no_check {
    ($trait:path, $impl_trait:ident, $fun:ident, $obeys:ident, $req:ident, $spec:ident, $self:ident, $rhs:ident, $op:tt, [$($typ:ty)*]) => {
        $crate::vstd::prelude::verus! {
            def_bop_assign_impls!($trait, $impl_trait, $fun, $obeys, $req, $spec, $self, $rhs, [
                $(
                    (
                        $typ,
                        true,
                        $self $op $rhs
                    )
                )*
            ]);
        }
};
}

macro_rules! def_bop_impls_check_overflow {
    ($trait:path, $impl_trait:ident, $fun:ident, $obeys:ident, $req:ident, $spec:ident, $self:ident, $rhs:ident, $op:tt, [$($typ:ty)*]) => {
        $crate::vstd::prelude::verus! {
            def_bop_impls!($trait, $impl_trait, $fun, $obeys, $req, $spec, $self, $rhs, [
                $(
                    (
                        $typ,
                        ($self $op $rhs) as $typ == ($self $op $rhs),
                        ($self $op $rhs) as $typ
                    )
                )*
            ]);
        }
};
}

macro_rules! def_bop_assign_impls_check_overflow {
    ($trait:path, $impl_trait:ident, $fun:ident, $obeys:ident, $req:ident, $spec:ident, $self:ident, $rhs:ident, $op:tt, [$($typ:ty)*]) => {
        $crate::vstd::prelude::verus! {
            def_bop_assign_impls!($trait, $impl_trait, $fun, $obeys, $req, $spec, $self, $rhs, [
                $(
                    (
                        $typ,
                        ($self $op $rhs) as $typ == ($self $op $rhs),
                        ($self $op $rhs) as $typ
                    )
                )*
            ]);
        }
};
}

macro_rules! def_bop_impls_unsigned_div_rem {
    ($trait:path, $impl_trait:ident, $fun:ident, $obeys:ident, $req:ident, $spec:ident, $self:ident, $rhs:ident, $op:tt, [$($typ:ty)*]) => {
        $crate::vstd::prelude::verus! {
            def_bop_impls!($trait, $impl_trait, $fun, $obeys, $req, $spec, $self, $rhs, [
                $(
                    (
                        $typ,
                        $rhs != 0,
                        $self $op $rhs
                    )
                )*
            ]);
        }
};
}

macro_rules! def_bop_assign_impls_unsigned_div_rem {
    ($trait:path, $impl_trait:ident, $fun:ident, $obeys:ident, $req:ident, $spec:ident, $self:ident, $rhs:ident, $op:tt, [$($typ:ty)*]) => {
        $crate::vstd::prelude::verus! {
            def_bop_assign_impls!($trait, $impl_trait, $fun, $obeys, $req, $spec, $self, $rhs, [
                $(
                    (
                        $typ,
                        $rhs != 0,
                        $self $op $rhs
                    )
                )*
            ]);
        }
};
}

// Signed div/rem needs to:
// - check for overflow (e.g. (-128i8) / (-1im))
// - express truncating div, rem in terms of euclidean /, %
macro_rules! def_bop_impls_signed_div_rem {
    ($trait:path, $impl_trait:ident, $fun:ident, $obeys:ident, $req:ident, $spec:ident, $self:ident, $rhs:ident, $op:path, [$($typ:ty)*]) => {
        $crate::vstd::prelude::verus! {
            def_bop_impls!($trait, $impl_trait, $fun, $obeys, $req, $spec, $self, $rhs, [
                $(
                    (
                        $typ,
                        $rhs != 0 && !($self == $typ::MIN && $rhs == -1),
                        $op($self as int, $rhs as int) as $typ
                    )
                )*
            ]);
        }
};
}

macro_rules! def_bop_assign_impls_signed_div_rem {
    ($trait:path, $impl_trait:ident, $fun:ident, $obeys:ident, $req:ident, $spec:ident, $self:ident, $rhs:ident, $op:path, [$($typ:ty)*]) => {
        $crate::vstd::prelude::verus! {
            def_bop_assign_impls!($trait, $impl_trait, $fun, $obeys, $req, $spec, $self, $rhs, [
                $(
                    (
                        $typ,
                        $rhs != 0 && !($self == $typ::MIN && $rhs == -1),
                        $op($self as int, $rhs as int) as $typ
                    )
                )*
            ]);
        }
};
}

// TODO: there are many more combinations of primitive integer types supported by Shl and Shr,
// such as (Self = u8, Rhs = u64)
macro_rules! def_bop_impls_shift {
    ($trait:path, $impl_trait:ident, $fun:ident, $obeys:ident, $req:ident, $spec:ident, $self:ident, $rhs:ident, $op:tt, [$($typ:ty)*]) => {
        $crate::vstd::prelude::verus! {
            def_bop_impls!($trait, $impl_trait, $fun, $obeys, $req, $spec, $self, $rhs, [
                $(
                    (
                        $typ,
                        $rhs < $typ::BITS,
                        $self $op $rhs
                    )
                )*
            ]);
        }
};
}

macro_rules! def_bop_assign_impls_shift {
    ($trait:path, $impl_trait:ident, $fun:ident, $obeys:ident, $req:ident, $spec:ident, $self:ident, $rhs:ident, $op:tt, [$($typ:ty)*]) => {
        $crate::vstd::prelude::verus! {
            def_bop_assign_impls!($trait, $impl_trait, $fun, $obeys, $req, $spec, $self, $rhs, [
                $(
                    (
                        $typ,
                        $rhs < $typ::BITS,
                        $self $op $rhs
                    )
                )*
            ]);
        }
};
}

def_uop_impls_check_overflow!(core::ops::Neg, NegSpecImpl, neg, obeys_neg_spec, neg_req, neg_spec, self, -, [
    isize i8 i16 i32 i64 i128
]);

def_uop_impls_no_check!(core::ops::Not, NotSpecImpl, not, obeys_not_spec, not_req, not_spec, self, !, [
    bool
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
]);

def_bop_impls_check_overflow!(core::ops::Add, AddSpecImpl, add, obeys_add_spec, add_req, add_spec, self, rhs, +, [
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
]);

def_bop_assign_impls_check_overflow!(core::ops::AddAssign, AddAssignSpecImpl, add_assign, obeys_add_assign_spec, add_assign_req, add_assign_spec, self, rhs, +, [
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
]);

def_bop_impls_check_overflow!(core::ops::Sub, SubSpecImpl, sub, obeys_sub_spec, sub_req, sub_spec, self, rhs, -, [
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
]);

def_bop_assign_impls_check_overflow!(core::ops::SubAssign, SubAssignSpecImpl, sub_assign, obeys_sub_assign_spec, sub_assign_req, sub_assign_spec, self, rhs, -, [
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
]);

def_bop_impls_check_overflow!(core::ops::Mul, MulSpecImpl, mul, obeys_mul_spec, mul_req, mul_spec, self, rhs, *, [
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
]);

def_bop_assign_impls_check_overflow!(core::ops::MulAssign, MulAssignSpecImpl, mul_assign, obeys_mul_assign_spec, mul_assign_req, mul_assign_spec, self, rhs, *, [
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
]);

def_bop_impls_unsigned_div_rem!(core::ops::Div, DivSpecImpl, div, obeys_div_spec, div_req, div_spec, self, rhs, /, [
    usize u8 u16 u32 u64 u128
]);

def_bop_assign_impls_unsigned_div_rem!(core::ops::DivAssign, DivAssignSpecImpl, div_assign, obeys_div_assign_spec, div_assign_req, div_assign_spec, self, rhs, /, [
    usize u8 u16 u32 u64 u128
]);

def_bop_impls_signed_div_rem!(core::ops::Div, DivSpecImpl, div, obeys_div_spec, div_req, div_spec, self, rhs, super::super::arithmetic::div_mod::rust_div, [
    isize i8 i16 i32 i64 i128
]);

def_bop_assign_impls_signed_div_rem!(core::ops::DivAssign, DivAssignSpecImpl, div_assign, obeys_div_assign_spec, div_assign_req, div_assign_spec, self, rhs, super::super::arithmetic::div_mod::rust_div, [
    isize i8 i16 i32 i64 i128
]);

def_bop_impls_unsigned_div_rem!(core::ops::Rem, RemSpecImpl, rem, obeys_rem_spec, rem_req, rem_spec, self, rhs, %, [
    usize u8 u16 u32 u64 u128
]);

def_bop_assign_impls_unsigned_div_rem!(core::ops::RemAssign, RemAssignSpecImpl, rem_assign, obeys_rem_assign_spec, rem_assign_req, rem_assign_spec, self, rhs, %, [
    usize u8 u16 u32 u64 u128
]);

def_bop_impls_signed_div_rem!(core::ops::Rem, RemSpecImpl, rem, obeys_rem_spec, rem_req, rem_spec, self, rhs, super::super::arithmetic::div_mod::rust_rem, [
    isize i8 i16 i32 i64 i128
]);

def_bop_assign_impls_signed_div_rem!(core::ops::RemAssign, RemAssignSpecImpl, rem_assign, obeys_rem_assign_spec, rem_assign_req, rem_assign_spec, self, rhs, super::super::arithmetic::div_mod::rust_rem, [
    isize i8 i16 i32 i64 i128
]);

def_bop_impls_no_check!(core::ops::BitAnd, BitAndSpecImpl, bitand, obeys_bitand_spec, bitand_req, bitand_spec, self, rhs, &, [
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
]);

def_bop_assign_impls_no_check!(core::ops::BitAndAssign, BitAndAssignSpecImpl, bitand_assign, obeys_bitand_assign_spec, bitand_assign_req, bitand_assign_spec, self, rhs, &, [
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
]);

def_bop_impls_no_check!(core::ops::BitOr, BitOrSpecImpl, bitor, obeys_bitor_spec, bitor_req, bitor_spec, self, rhs, |, [
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
]);

def_bop_assign_impls_no_check!(core::ops::BitOrAssign, BitOrAssignSpecImpl, bitor_assign, obeys_bitor_assign_spec, bitor_assign_req, bitor_assign_spec, self, rhs, |, [
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
]);

def_bop_impls_no_check!(core::ops::BitXor, BitXorSpecImpl, bitxor, obeys_bitxor_spec, bitxor_req, bitxor_spec, self, rhs, ^, [
    bool
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
]);

def_bop_assign_impls_no_check!(core::ops::BitXorAssign, BitXorAssignSpecImpl, bitxor_assign, obeys_bitxor_assign_spec, bitxor_assign_req, bitxor_assign_spec, self, rhs, ^, [
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
]);

def_bop_impls_shift!(core::ops::Shl, ShlSpecImpl, shl, obeys_shl_spec, shl_req, shl_spec, self, rhs, <<, [
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
]);

def_bop_assign_impls_shift!(core::ops::ShlAssign, ShlAssignSpecImpl, shl_assign, obeys_shl_assign_spec, shl_assign_req, shl_assign_spec, self, rhs, <<, [
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
]);

def_bop_impls_shift!(core::ops::Shr, ShrSpecImpl, shr, obeys_shr_spec, shr_req, shr_spec, self, rhs, >>, [
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
]);

def_bop_assign_impls_shift!(core::ops::ShrAssign, ShrAssignSpecImpl, shr_assign, obeys_shr_assign_spec, shr_assign_req, shr_assign_spec, self, rhs, >>, [
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
]);

verus! {

#[verusfmt::skip]
// Note: we do not assume that floating point types have obeys_*_spec() == true
// because Rust floating point operations are not guaranteed to be deterministic.
// (See https://github.com/rust-lang/rfcs/blob/master/text/3514-float-semantics.md )
// Instead, we ensure an uninterpreted function about the result,
// which can be used to trigger user-supplied axioms.
#[verusfmt::skip]

pub uninterp spec fn neg_ensures<A>(x: A, o: A) -> bool;

pub uninterp spec fn add_ensures<A>(x: A, y: A, o: A) -> bool;

pub uninterp spec fn sub_ensures<A>(x: A, y: A, o: A) -> bool;

pub uninterp spec fn mul_ensures<A>(x: A, y: A, o: A) -> bool;

pub uninterp spec fn div_ensures<A>(x: A, y: A, o: A) -> bool;

pub assume_specification[ <f32 as core::ops::Neg>::neg ](x: f32) -> (o: f32)
    ensures
        neg_ensures::<f32>(x, o),
;

pub assume_specification[ <f32 as core::ops::Add>::add ](x: f32, y: f32) -> (o: f32)
    ensures
        add_ensures::<f32>(x, y, o),
;

pub assume_specification[ <f32 as core::ops::Sub>::sub ](x: f32, y: f32) -> (o: f32)
    ensures
        sub_ensures::<f32>(x, y, o),
;

pub assume_specification[ <f32 as core::ops::Mul>::mul ](x: f32, y: f32) -> (o: f32)
    ensures
        mul_ensures::<f32>(x, y, o),
;

pub assume_specification[ <f32 as core::ops::Div>::div ](x: f32, y: f32) -> (o: f32)
    ensures
        div_ensures::<f32>(x, y, o),
;

pub assume_specification[ <f64 as core::ops::Neg>::neg ](x: f64) -> (o: f64)
    ensures
        neg_ensures::<f64>(x, o),
;

pub assume_specification[ <f64 as core::ops::Add>::add ](x: f64, y: f64) -> (o: f64)
    ensures
        add_ensures::<f64>(x, y, o),
;

pub assume_specification[ <f64 as core::ops::Sub>::sub ](x: f64, y: f64) -> (o: f64)
    ensures
        sub_ensures::<f64>(x, y, o),
;

pub assume_specification[ <f64 as core::ops::Mul>::mul ](x: f64, y: f64) -> (o: f64)
    ensures
        mul_ensures::<f64>(x, y, o),
;

pub assume_specification[ <f64 as core::ops::Div>::div ](x: f64, y: f64) -> (o: f64)
    ensures
        div_ensures::<f64>(x, y, o),
;

} // verus!

// ---------------------------------------------------------------------------
// PBT wrappers for the bare integer-op assume_specs emitted by the
// def_uop_impls!/def_bop_impls!/def_bop_assign_impls! macros above. Those
// specs carry no inline contract (the claims live in the *SpecImpl trait
// impls: in-range req guards + exact int-domain results), so each per-width
// harness restates them against independent oracles: i128 arithmetic for
// Add/Sub/Mul/Div/Rem/Neg (widths <= 64), a per-bit loop for the bit ops
// and shifts, and op == op_assign consistency. u128/i128 arithmetic has no
// wider oracle; the macro-site coverage at the other ten widths is what the
// classifier counts.
// ---------------------------------------------------------------------------
macro_rules! pbt_int_op_specs {
    ($t:ty, $f:ident) => {
        verus! {
        #[cfg(not(verus_verify_core))]
        #[verifier::external_body]
        #[pbt]
        pub fn $f(x: $t, y: $t, s: u8) -> (ret: bool)
            ensures
                ret,
        {
            let big = |v: $t| v as i128;
            // guarded arithmetic vs the i128 oracle (checked_* encodes
            // exactly the specs' req guards, incl. y != 0 / MIN,-1)
            let add_ok = match x.checked_add(y) { Some(r) => big(r) == big(x) + big(y), None => true };
            let sub_ok = match x.checked_sub(y) { Some(r) => big(r) == big(x) - big(y), None => true };
            let mul_ok = match x.checked_mul(y) { Some(r) => big(r) == big(x) * big(y), None => true };
            let div_ok = match x.checked_div(y) { Some(r) => big(r) == big(x) / big(y), None => true };
            let rem_ok = match x.checked_rem(y) { Some(r) => big(r) == big(x) % big(y), None => true };
            let neg_ok = match x.checked_neg() { Some(r) => big(r) == -big(x), None => true };
            // Not: complement identity
            let not_ok = (!x) == (x ^ !0);
            // bit ops: per-bit oracle
            let bits = <$t>::BITS;
            let mut bit_ok = true;
            let mut i = 0u32;
            while i < bits {
                let (xa, ya) = (((x >> i) & 1), ((y >> i) & 1));
                bit_ok = bit_ok
                    && ((x & y) >> i) & 1 == (xa & ya)
                    && ((x | y) >> i) & 1 == (xa | ya)
                    && ((x ^ y) >> i) & 1 == (xa ^ ya);
                i += 1;
            }
            // shifts (guarded s < BITS): per-bit oracle; >> replicates the
            // top bit for signed types (clamp handles both)
            let s32 = (s as u32) % bits;  // sample inside the req guard
            let mut shift_ok = true;
            let mut i = 0u32;
            while i < bits {
                let shl_bit = if i >= s32 { (x >> (i - s32)) & 1 } else { 0 };
                let src = if i + s32 < bits { i + s32 } else { bits - 1 };
                let shr_bit = if i + s32 < bits || (<$t>::MIN != 0) { (x >> src) & 1 } else { 0 };
                shift_ok = shift_ok
                    && ((x << s32) >> i) & 1 == shl_bit
                    && ((x >> s32) >> i) & 1 == shr_bit;
                i += 1;
            }
            // op_assign forms agree with the ops
            let mut a = x;
            let assign_arith_ok = match x.checked_add(y) {
                Some(r) => { a = x; a += y; a == r },
                None => true,
            } && match x.checked_sub(y) {
                Some(r) => { a = x; a -= y; a == r },
                None => true,
            } && match x.checked_mul(y) {
                Some(r) => { a = x; a *= y; a == r },
                None => true,
            } && match x.checked_div(y) {
                Some(r) => { a = x; a /= y; a == r },
                None => true,
            } && match x.checked_rem(y) {
                Some(r) => { a = x; a %= y; a == r },
                None => true,
            };
            let assign_bit_ok = {
                let (mut b1, mut b2, mut b3, mut b4, mut b5) = (x, x, x, x, x);
                b1 &= y;
                b2 |= y;
                b3 ^= y;
                b4 <<= s32;
                b5 >>= s32;
                b1 == (x & y) && b2 == (x | y) && b3 == (x ^ y)
                    && b4 == (x << s32) && b5 == (x >> s32)
            };
            add_ok && sub_ok && mul_ok && div_ok && rem_ok && neg_ok && not_ok
                && bit_ok && shift_ok && assign_arith_ok && assign_bit_ok
        }
        } // verus!
    };
}

pbt_int_op_specs!(u8, pbt_int_ops_u8);
pbt_int_op_specs!(u16, pbt_int_ops_u16);
pbt_int_op_specs!(u32, pbt_int_ops_u32);
pbt_int_op_specs!(u64, pbt_int_ops_u64);
pbt_int_op_specs!(usize, pbt_int_ops_usize);
pbt_int_op_specs!(i8, pbt_int_ops_i8);
pbt_int_op_specs!(i16, pbt_int_ops_i16);
pbt_int_op_specs!(i32, pbt_int_ops_i32);
pbt_int_op_specs!(i64, pbt_int_ops_i64);
pbt_int_op_specs!(isize, pbt_int_ops_isize);
