//! Implementation of `verus_pbt_unverified!` and `verus_pbt_verified!`.
//!
//! These macros sit alongside `exec_spec_unverified!` / `exec_spec_verified!`
//! in the contrib tree. Given a body of items containing `spec` functions,
//! user-defined `struct` / `enum`s, and exec functions with `requires` /
//! `ensures` clauses, they emit:
//!
//! 1. A `verus! { ... }` block holding the user's items unchanged so Verus
//!    still verifies the spec layer.
//! 2. An engine block (`exec_spec_unverified!` or `exec_spec_verified!`)
//!    compiling every spec fn and user type reachable from a contract into
//!    its `Exec*` counterpart. This block also includes any synthetic spec
//!    fns the macro lifts inline `forall`/`exists` into.
//! 3. A `PbtStrategy` impl per user-defined struct/enum so the harness can
//!    sample values of `Exec*` types directly.
//! 4. A `#[cfg(test)] mod __verus_pbt_<id>` containing one `proptest!`
//!    harness per contract-bearing exec fn. The harness asks the runtime
//!    crate (`::verus_pbt_runtime`) for a strategy per parameter,
//!    `prop_assume!`s the requires, calls the real exec fn, and
//!    `prop_assert!`s the ensures.
//!
//! Phase coverage:
//!   - Phase 1: free fns over primitives, `Vec<T>`, `&[T]`, user structs.
//!   - Phase 3: enums, nested types (`Vec<UserT>`, `Option<UserT>`, etc.),
//!     `HashMap`/`HashSet`/`Multiset`, spec-only `impl` blocks.
//!   - Phase 4: inline `forall`/`exists` in clauses are lifted into synthetic
//!     spec fns; `verus_pbt_verified!` is exercised end-to-end.

use std::collections::{HashMap, HashSet};
use std::sync::atomic::{AtomicU64, Ordering};

use proc_macro::TokenStream;
use proc_macro2::{Span, TokenStream as TokenStream2};
use quote::{format_ident, quote, quote_spanned};
use verus_syn::parse::{Parse, ParseStream};
use verus_syn::visit::Visit;
use verus_syn::visit_mut::VisitMut;
use verus_syn::{
    Error, Expr, ExprMethodCall, ExprPath, ExprUnary, Fields, FnArgKind, FnMode, GenericArgument,
    Ident, Item, ItemEnum, ItemFn, ItemImpl, ItemStruct, Pat, PatType, PathArguments, ReturnType,
    Type, UnOp, parse_macro_input,
};

// ---------------------------------------------------------------------------
// Item parsing & classification
// ---------------------------------------------------------------------------

/// Custom parser for a list of items.
struct PbtItems(Vec<Item>);

impl Parse for PbtItems {
    fn parse(input: ParseStream) -> verus_syn::parse::Result<PbtItems> {
        let mut items = Vec::new();
        while !input.is_empty() {
            items.push(input.parse()?);
        }
        Ok(PbtItems(items))
    }
}

/// Either or enum the user defined; carried with us so we can emit
/// strategy impls.
#[derive(Clone)]
enum UserType {
    Struct(ItemStruct),
    Enum(ItemEnum),
}

impl UserType {
    #[allow(dead_code)]
    fn name(&self) -> &Ident {
        match self {
            UserType::Struct(s) => &s.ident,
            UserType::Enum(e) => &e.ident,
        }
    }
}

/// A contract-bearing function we need to emit a harness for. Free fns and
/// `&self`-receiver methods on user-defined `Exec*` types are both supported.
#[derive(Clone)]
enum ContractTarget {
    /// A free `fn` with at least one of `requires` / `ensures`.
    FreeFn(ItemFn),
    /// A method on an `Exec*` type with at least one of `requires` /
    /// `ensures`. Carries the impl's Self ident (e.g. `ExecUser`) so the
    /// harness can call `super::ExecUser::method(&u, ...)`.
    Method { self_ty: Ident, method: verus_syn::ImplItemFn },
}

/// Result of classifying the macro's input items.
struct Classified {
    /// Items the user wrote, passed through verus! verbatim.
    passthrough_items: Vec<Item>,
    /// Items the engine compiles (spec fn / struct / enum / spec-only impl).
    engine_items: Vec<Item>,
    /// Names of spec fns (for the contract rewriter's call-site renaming).
    spec_fn_names: HashSet<String>,
    /// Definitions of user-defined types (for strategy emission).
    user_types: Vec<UserType>,
    /// Set of user-defined type names (faster lookups during type analysis).
    user_type_names: HashSet<String>,
    /// Contract-bearing fns / methods that need a harness.
    contract_targets: Vec<ContractTarget>,
    /// Token bodies of `external_pbt_provide!` invocations (Tier 4 trusted
    /// stubs). Their `exec_<name>` companions are emitted into the harness
    /// module so harness calls `exec_<name>(..)` resolve.
    external_provide_bodies: Vec<TokenStream2>,
}

/// Lenient match for the `external_pbt_provide` macro path: bare,
/// `contrib::`-, or `vstd::contrib::`-qualified.
fn macro_path_is_external_provide(path: &verus_syn::Path) -> bool {
    if path.leading_colon.is_some() {
        return false;
    }
    let segs: Vec<String> = path.segments.iter().map(|s| s.ident.to_string()).collect();
    let segs: Vec<&str> = segs.iter().map(|s| s.as_str()).collect();
    matches!(
        &segs[..],
        ["external_pbt_provide"]
            | ["contrib", "external_pbt_provide"]
            | ["vstd", "contrib", "external_pbt_provide"]
    )
}

fn classify(items: Vec<Item>) -> Classified {
    let mut passthrough_items = Vec::new();
    let mut engine_items = Vec::new();
    let mut spec_fn_names = HashSet::new();
    let mut user_types = Vec::new();
    let mut user_type_names = HashSet::new();
    let mut contract_targets: Vec<ContractTarget> = Vec::new();
    let mut external_provide_bodies: Vec<TokenStream2> = Vec::new();

    for item in items {
        match &item {
            Item::Fn(item_fn) => match &item_fn.sig.mode {
                FnMode::Spec(..) => {
                    spec_fn_names.insert(item_fn.sig.ident.to_string());
                    engine_items.push(item.clone());
                }
                FnMode::Default => {
                    let has_contract = item_fn.sig.spec.requires.is_some()
                        || item_fn.sig.spec.ensures.is_some();
                    if has_contract {
                        contract_targets.push(ContractTarget::FreeFn(item_fn.clone()));
                    }
                    passthrough_items.push(item);
                }
                _ => {
                    passthrough_items.push(item);
                }
            },
            Item::Struct(item_struct) => {
                user_type_names.insert(item_struct.ident.to_string());
                user_types.push(UserType::Struct(item_struct.clone()));
                engine_items.push(item);
            }
            Item::Enum(item_enum) => {
                user_type_names.insert(item_enum.ident.to_string());
                user_types.push(UserType::Enum(item_enum.clone()));
                engine_items.push(item);
            }
            Item::Impl(item_impl) => {
                // Three cases:
                //   1. All spec methods → route the whole impl to the engine.
                //   2. All exec methods → passthrough; harvest contracts.
                //   3. Mixed → split into two impl blocks.
                let self_ty_ident = impl_self_ty_ident(item_impl);
                let mut spec_methods: Vec<verus_syn::ImplItem> = Vec::new();
                let mut exec_methods: Vec<verus_syn::ImplItem> = Vec::new();
                let mut other_items: Vec<verus_syn::ImplItem> = Vec::new();
                for ii in &item_impl.items {
                    match ii {
                        verus_syn::ImplItem::Fn(impl_fn) => {
                            if matches!(impl_fn.sig.mode, FnMode::Spec(..)) {
                                spec_fn_names.insert(impl_fn.sig.ident.to_string());
                                spec_methods.push(ii.clone());
                            } else if matches!(impl_fn.sig.mode, FnMode::Default) {
                                exec_methods.push(ii.clone());
                                let has_contract = impl_fn.sig.spec.requires.is_some()
                                    || impl_fn.sig.spec.ensures.is_some();
                                if has_contract {
                                    if let Some(self_ty) = self_ty_ident.clone() {
                                        contract_targets.push(ContractTarget::Method {
                                            self_ty,
                                            method: impl_fn.clone(),
                                        });
                                    }
                                    // If we can't resolve Self type, the
                                    // method still goes into passthrough but
                                    // isn't harnessed (we lack a strategy).
                                }
                            } else {
                                other_items.push(ii.clone());
                            }
                        }
                        _ => other_items.push(ii.clone()),
                    }
                }

                let make_impl_with = |items: Vec<verus_syn::ImplItem>| -> ItemImpl {
                    let mut new_impl = item_impl.clone();
                    new_impl.items = items;
                    new_impl
                };

                if !spec_methods.is_empty() && exec_methods.is_empty() && other_items.is_empty() {
                    // Pure spec impl → engine.
                    engine_items.push(item);
                } else if spec_methods.is_empty() {
                    // Pure exec / other impl → passthrough.
                    passthrough_items.push(item);
                } else {
                    // Mixed: split.
                    let spec_only = make_impl_with(spec_methods);
                    let mut others = exec_methods;
                    others.extend(other_items);
                    let exec_only = make_impl_with(others);
                    engine_items.push(Item::Impl(spec_only));
                    passthrough_items.push(Item::Impl(exec_only));
                }
            }
            _ => {
                // external_pbt_provide! { ... }: register the provided names
                // as spec fns (so contract calls `f(..)` rename to
                // `exec_f(..)`) and stash the body for companion emission. The
                // macro item itself does not pass through to verus!.
                if let Item::Macro(m) = &item {
                    if macro_path_is_external_provide(&m.mac.path) {
                        for n in
                            crate::contrib::external_pbt_provide::provided_names(m.mac.tokens.clone())
                        {
                            spec_fn_names.insert(n);
                        }
                        external_provide_bodies.push(m.mac.tokens.clone());
                        continue;
                    }
                }
                passthrough_items.push(item);
            }
        }
    }

    Classified {
        passthrough_items,
        engine_items,
        spec_fn_names,
        user_types,
        user_type_names,
        contract_targets,
        external_provide_bodies,
    }
}

fn impl_self_ty_ident(item_impl: &ItemImpl) -> Option<Ident> {    if item_impl.trait_.is_some() {
        return None;
    }
    if let Type::Path(tp) = item_impl.self_ty.as_ref() {
        if tp.qself.is_none() && tp.path.segments.len() == 1 {
            let seg = &tp.path.segments[0];
            if matches!(seg.arguments, PathArguments::None) {
                return Some(seg.ident.clone());
            }
        }
    }
    None
}

// ---------------------------------------------------------------------------
// Param / return type analysis
// ---------------------------------------------------------------------------

/// Categorisation of a parameter's type for harness-side strategy / call
/// adaptation.
#[derive(Clone, Debug)]
enum ParamShape {
    /// `i64`, `u8`, `bool`, `char`, ...: harness gets a `T`, call site uses
    /// `x` directly.
    Primitive(Type),
    /// `Vec<E>` where `E` is a ParamElem (primitive or user-type Exec*).
    OwnedVec(ParamElem),
    /// `&[E]`.
    Slice(ParamElem),
    /// `Option<E>`.
    OwnedOption(ParamElem),
    /// `HashMap<K, V>`. Both K and V are `ParamElem`.
    OwnedHashMap(ParamElem, ParamElem),
    /// `HashSet<E>`.
    OwnedHashSet(ParamElem),
    /// `Multiset<E>` — compiles to ExecMultiset<exec(E)>.
    OwnedMultiset(ParamElem),
    /// `&UserType`.
    RefUserType(Ident),
    /// `UserType` (owned).
    OwnedUserType(Ident),
}

/// Element type used inside a parametrised collection (`Vec<E>`, `&[E]`,
/// `Option<E>`, etc.). Splitting this from `ParamShape` lets us reuse the
/// representation cleanly and enforce a single level of nesting (we don't
/// today support `Vec<Vec<T>>` because the engine's `exec_spec_unverified!`
/// is fine with that but proptest strategies are easier with single-level
/// recursion limits in this initial round).
#[derive(Clone, Debug)]
enum ParamElem {
    Primitive(Type),
    UserType(Ident),
}

impl ParamElem {
    /// The type the harness samples for this element. For user types we
    /// sample the user's OWN type (e.g. `User`), not the engine's `ExecUser`,
    /// so the user never has to mention `Exec*`.
    fn harness_type(&self) -> TokenStream2 {
        match self {
            ParamElem::Primitive(ty) => quote! { #ty },
            ParamElem::UserType(name) => quote! { #name },
        }
    }
}

impl ParamShape {
    fn harness_type(&self) -> TokenStream2 {
        match self {
            ParamShape::Primitive(ty) => quote! { #ty },
            ParamShape::OwnedVec(e) | ParamShape::Slice(e) => {
                let inner = e.harness_type();
                quote! { ::std::vec::Vec<#inner> }
            }
            ParamShape::OwnedOption(e) => {
                let inner = e.harness_type();
                quote! { ::std::option::Option<#inner> }
            }
            ParamShape::OwnedHashMap(k, v) => {
                let kt = k.harness_type();
                let vt = v.harness_type();
                quote! { ::std::collections::HashMap<#kt, #vt> }
            }
            ParamShape::OwnedHashSet(e) => {
                let inner = e.harness_type();
                quote! { ::std::collections::HashSet<#inner> }
            }
            // For `Multiset<T>` the engine compiles to `ExecMultiset<T>`; the
            // proptest harness gets a `HashMap<T, usize>` and wraps it in
            // `ExecMultiset { m: ... }` at the call site.
            ParamShape::OwnedMultiset(e) => {
                let inner = e.harness_type();
                quote! { ::std::collections::HashMap<#inner, usize> }
            }
            ParamShape::RefUserType(name) | ParamShape::OwnedUserType(name) => {
                // Sample the user's OWN type, not Exec*.
                quote! { #name }
            }
        }
    }

    /// What to put in the call to `super::<fn>(...)` at the harness site.
    fn arg_for_real_call(&self, harness_ident: &Ident) -> TokenStream2 {
        match self {
            ParamShape::Primitive(_) => quote! { #harness_ident },
            ParamShape::OwnedVec(_) => quote! { #harness_ident.clone() },
            ParamShape::Slice(_) => quote! { #harness_ident.as_slice() },
            ParamShape::OwnedOption(_) => quote! { #harness_ident.clone() },
            ParamShape::OwnedHashMap(_, _) => quote! { #harness_ident.clone() },
            ParamShape::OwnedHashSet(_) => quote! { #harness_ident.clone() },
            ParamShape::OwnedMultiset(_) => quote! {
                ::vstd::contrib::exec_spec::ExecMultiset { m: #harness_ident.clone() }
            },
            // The user's exec fn takes their OWN type (`&User` / `User`).
            ParamShape::RefUserType(_) => quote! { &#harness_ident },
            ParamShape::OwnedUserType(_) => quote! { #harness_ident.clone() },
        }
    }

    /// What does `<param>.deep_view()` (or `*self` for a method receiver)
    /// become in a contract clause? The result is the `Exec*` value the
    /// `exec_*` spec fns expect. For user types we convert via the generated
    /// `__pbt_to_exec_*` fn.
    fn call_form_for_deep_view(&self, harness_ident: &Ident) -> TokenStream2 {
        match self {
            ParamShape::Primitive(_) => quote! { #harness_ident },
            ParamShape::OwnedVec(_) => quote! { #harness_ident.as_slice() },
            ParamShape::Slice(_) => quote! { #harness_ident.as_slice() },
            ParamShape::OwnedOption(_) => quote! { &#harness_ident },
            ParamShape::OwnedHashMap(_, _) => quote! { &#harness_ident },
            ParamShape::OwnedHashSet(_) => quote! { &#harness_ident },
            ParamShape::OwnedMultiset(_) => quote! {
                &::vstd::contrib::exec_spec::ExecMultiset { m: #harness_ident.clone() }
            },
            ParamShape::RefUserType(name) | ParamShape::OwnedUserType(name) => {
                // Fully-qualified trait call so it (a) resolves across files
                // by trait lookup and (b) triggers the ToExecModel
                // `on_unimplemented` diagnostic if the type was never
                // `#[pbt_provide]`'d. (Method syntax `x.to_exec_model()`
                // would yield a generic E0599 instead.)
                quote! {
                    &<#name as ::verus_pbt_runtime::ToExecModel>::to_exec_model(&#harness_ident)
                }
            }
        }
    }

    /// The spec-side type the original parameter ends up viewed as, for the
    /// purposes of synthesising helper spec fns (Phase 4 quantifier lifting).
    /// Returned as an UNQUALIFIED type path because the engine recognises
    /// `Seq<T>`, `Map<K,V>`, etc. only when written without a leading path.
    fn spec_type(&self) -> TokenStream2 {
        match self {
            ParamShape::Primitive(ty) => quote! { #ty },
            ParamShape::OwnedVec(e) | ParamShape::Slice(e) => {
                let inner = match e {
                    ParamElem::Primitive(t) => quote! { #t },
                    ParamElem::UserType(n) => quote! { #n },
                };
                quote! { Seq<#inner> }
            }
            ParamShape::OwnedOption(e) => {
                let inner = match e {
                    ParamElem::Primitive(t) => quote! { #t },
                    ParamElem::UserType(n) => quote! { #n },
                };
                quote! { Option<#inner> }
            }
            ParamShape::OwnedHashMap(k, v) => {
                let kt = match k {
                    ParamElem::Primitive(t) => quote! { #t },
                    ParamElem::UserType(n) => quote! { #n },
                };
                let vt = match v {
                    ParamElem::Primitive(t) => quote! { #t },
                    ParamElem::UserType(n) => quote! { #n },
                };
                quote! { Map<#kt, #vt> }
            }
            ParamShape::OwnedHashSet(e) => {
                let inner = match e {
                    ParamElem::Primitive(t) => quote! { #t },
                    ParamElem::UserType(n) => quote! { #n },
                };
                quote! { Set<#inner> }
            }
            ParamShape::OwnedMultiset(e) => {
                let inner = match e {
                    ParamElem::Primitive(t) => quote! { #t },
                    ParamElem::UserType(n) => quote! { #n },
                };
                quote! { Multiset<#inner> }
            }
            ParamShape::RefUserType(n) | ParamShape::OwnedUserType(n) => quote! { #n },
        }
    }
}

/// Name of the generated `User -> ExecUser` converter fn for a user type.
fn to_exec_fn_name(user_ty: &Ident) -> Ident {
    format_ident!("__pbt_to_exec_{}", user_ty)
}

/// Strip a leading `Exec` from a name. Returns the original name if the
/// stripped name corresponds to a user-defined type. Used by the classifier
/// to recognise `&ExecPair` / `ExecPair` parameter types and route them
/// through the user-type code paths (which sample `ExecPair`).
fn strip_exec_prefix<'a>(name: &'a str, user_types: &HashSet<String>) -> Option<&'a str> {
    if let Some(rest) = name.strip_prefix("Exec") {
        if user_types.contains(rest) {
            return Some(rest);
        }
    }
    None
}

fn classify_param_elem(ty: &Type, user_types: &HashSet<String>) -> Result<ParamElem, Error> {
    if let Type::Path(tp) = ty {
        if tp.qself.is_none() && tp.path.segments.len() == 1 {
            let seg = &tp.path.segments[0];
            let name = seg.ident.to_string();
            if user_types.contains(&name) && matches!(seg.arguments, PathArguments::None) {
                return Ok(ParamElem::UserType(seg.ident.clone()));
            }
            // Recognise `ExecFoo` as the user's `Foo` for nested elements.
            if let Some(stripped) = strip_exec_prefix(&name, user_types) {
                if matches!(seg.arguments, PathArguments::None) {
                    return Ok(ParamElem::UserType(Ident::new(stripped, seg.ident.span())));
                }
            }
            if is_primitive_like(&name) {
                return Ok(ParamElem::Primitive(ty.clone()));
            }
            // A capitalized single-segment name we don't recognise is treated
            // as an EXTERNAL user type: one defined (and `#[pbt_provide]`'d) in
            // another module/file. We don't need its definition here — the
            // generated strategy uses `<Name as PbtStrategy>` and the
            // converter uses `<Name as ToExecModel>`, both resolved by trait
            // lookup across files. If the type was never provided, the
            // `on_unimplemented` diagnostic fires at the harness.
            if matches!(seg.arguments, PathArguments::None)
                && name.chars().next().is_some_and(|c| c.is_uppercase())
            {
                return Ok(ParamElem::UserType(seg.ident.clone()));
            }
        }
    }
    Err(Error::new_spanned(
        ty,
        "verus_pbt: nested element must be a primitive or a user-defined struct/enum",
    ))
}

fn classify_param_type(ty: &Type, user_types: &HashSet<String>) -> Result<ParamShape, Error> {
    match ty {
        Type::Reference(type_ref) => {
            // `&[E]`
            if let Type::Slice(slice) = type_ref.elem.as_ref() {
                let elem = classify_param_elem(&slice.elem, user_types)?;
                return Ok(ParamShape::Slice(elem));
            }
            // `&UserType` or `&ExecUserType`
            if let Type::Path(tp) = type_ref.elem.as_ref() {
                if tp.qself.is_none() && tp.path.segments.len() == 1 {
                    let seg = &tp.path.segments[0];
                    let name = seg.ident.to_string();
                    if user_types.contains(&name)
                        && matches!(seg.arguments, PathArguments::None)
                    {
                        return Ok(ParamShape::RefUserType(seg.ident.clone()));
                    }
                    if let Some(stripped) = strip_exec_prefix(&name, user_types) {
                        if matches!(seg.arguments, PathArguments::None) {
                            return Ok(ParamShape::RefUserType(Ident::new(
                                stripped,
                                seg.ident.span(),
                            )));
                        }
                    }
                }
            }
            // A capitalized single-segment ref type that we don't recognise
            // is most likely a user-defined type living in another module.
            if let Type::Path(tp) = type_ref.elem.as_ref() {
                if tp.qself.is_none() && tp.path.segments.len() == 1 {
                    let seg = &tp.path.segments[0];
                    let name = seg.ident.to_string();
                    if name.chars().next().is_some_and(|c| c.is_uppercase()) {
                        return Err(Error::new_spanned(
                            ty,
                            format!(
                                "verus_pbt: `&{name}` refers to a type that is not defined \
                                 inside this verus_pbt_unverified! block.\n\n\
                                 The macro can only build a proptest strategy for types it can \
                                 see between its own braces; it cannot reach a `struct`/`enum` \
                                 declared in another module or file. Move `{name}` (and the \
                                 spec fns its contract uses) into this block to test against it.",
                                name = name
                            ),
                        ));
                    }
                }
            }
            Err(Error::new_spanned(
                ty,
                "verus_pbt: unsupported reference parameter type. Supported: `&[E]` and \
                 `&UserType` (or `&ExecUserType`).",
            ))
        }
        Type::Path(tp) if tp.qself.is_none() && tp.path.segments.len() == 1 => {
            let seg = &tp.path.segments[0];
            let name = seg.ident.to_string();
            match name.as_str() {
                "Vec" => {
                    let inner = first_type_arg(&seg.arguments).ok_or_else(|| {
                        Error::new_spanned(ty, "verus_pbt: expected Vec<T> with a type argument")
                    })?;
                    Ok(ParamShape::OwnedVec(classify_param_elem(inner, user_types)?))
                }
                "Option" => {
                    let inner = first_type_arg(&seg.arguments).ok_or_else(|| {
                        Error::new_spanned(ty, "verus_pbt: expected Option<T> with a type argument")
                    })?;
                    Ok(ParamShape::OwnedOption(classify_param_elem(inner, user_types)?))
                }
                "HashMap" => {
                    let (k, v) = first_two_type_args(&seg.arguments).ok_or_else(|| {
                        Error::new_spanned(
                            ty,
                            "verus_pbt: expected HashMap<K, V> with two type arguments",
                        )
                    })?;
                    Ok(ParamShape::OwnedHashMap(
                        classify_param_elem(k, user_types)?,
                        classify_param_elem(v, user_types)?,
                    ))
                }
                "HashSet" => {
                    let inner = first_type_arg(&seg.arguments).ok_or_else(|| {
                        Error::new_spanned(
                            ty,
                            "verus_pbt: expected HashSet<T> with a type argument",
                        )
                    })?;
                    Ok(ParamShape::OwnedHashSet(classify_param_elem(inner, user_types)?))
                }
                "Multiset" => {
                    let inner = first_type_arg(&seg.arguments).ok_or_else(|| {
                        Error::new_spanned(
                            ty,
                            "verus_pbt: expected Multiset<T> with a type argument",
                        )
                    })?;
                    Ok(ParamShape::OwnedMultiset(classify_param_elem(inner, user_types)?))
                }
                _ => {
                    if user_types.contains(&name)
                        && matches!(seg.arguments, PathArguments::None)
                    {
                        return Ok(ParamShape::OwnedUserType(seg.ident.clone()));
                    }
                    if let Some(stripped) = strip_exec_prefix(&name, user_types) {
                        if matches!(seg.arguments, PathArguments::None) {
                            return Ok(ParamShape::OwnedUserType(Ident::new(
                                stripped,
                                seg.ident.span(),
                            )));
                        }
                    }
                    if is_primitive_like(&name) {
                        return Ok(ParamShape::Primitive(ty.clone()));
                    }
                    Err(Error::new_spanned(
                        ty,
                        format!(
                            "verus_pbt: unsupported parameter type `{}`. Supported: primitives, \
                             `Vec<E>`, `&[E]`, `Option<E>`, `HashMap<K, V>`, `HashSet<E>`, \
                             `Multiset<E>`, `&UserType`, and user-defined types.",
                            name
                        ),
                    ))
                }
            }
        }
        _ => Err(Error::new_spanned(
            ty,
            "verus_pbt: unsupported parameter type.",
        )),
    }
}

fn first_type_arg(args: &PathArguments) -> Option<&Type> {
    if let PathArguments::AngleBracketed(ab) = args {
        for a in &ab.args {
            if let GenericArgument::Type(t) = a {
                return Some(t);
            }
        }
    }
    None
}

fn first_two_type_args(args: &PathArguments) -> Option<(&Type, &Type)> {
    if let PathArguments::AngleBracketed(ab) = args {
        let mut tys = ab.args.iter().filter_map(|a| match a {
            GenericArgument::Type(t) => Some(t),
            _ => None,
        });
        let a = tys.next()?;
        let b = tys.next()?;
        return Some((a, b));
    }
    None
}

fn is_primitive_like(name: &str) -> bool {
    matches!(
        name,
        "bool"
            | "char"
            | "u8"
            | "u16"
            | "u32"
            | "u64"
            | "u128"
            | "usize"
            | "i8"
            | "i16"
            | "i32"
            | "i64"
            | "i128"
            | "isize"
            | "f32"
            | "f64"
            | "String"
    )
}

#[derive(Clone, Debug)]
enum ReturnShape {
    Unit,
    Primitive,
    OwnedVec(ParamElem),
    OwnedOption(ParamElem),
    OwnedHashMap,
    OwnedHashSet,
    OwnedMultiset,
    OwnedUserType(Ident),
}

fn classify_return(ret: &ReturnType, user_types: &HashSet<String>) -> Result<ReturnShape, Error> {
    let ty = match ret {
        ReturnType::Default => return Ok(ReturnShape::Unit),
        ReturnType::Type(_, _, _, ty) => ty,
    };
    match ty.as_ref() {
        Type::Path(tp) if tp.qself.is_none() && tp.path.segments.len() == 1 => {
            let seg = &tp.path.segments[0];
            let name = seg.ident.to_string();
            match name.as_str() {
                "Vec" => {
                    let inner = first_type_arg(&seg.arguments).ok_or_else(|| {
                        Error::new_spanned(ty, "verus_pbt: expected Vec<T> in return type")
                    })?;
                    Ok(ReturnShape::OwnedVec(classify_param_elem(inner, user_types)?))
                }
                "Option" => {
                    let inner = first_type_arg(&seg.arguments).ok_or_else(|| {
                        Error::new_spanned(ty, "verus_pbt: expected Option<T> in return type")
                    })?;
                    Ok(ReturnShape::OwnedOption(classify_param_elem(inner, user_types)?))
                }
                "HashMap" => Ok(ReturnShape::OwnedHashMap),
                "HashSet" => Ok(ReturnShape::OwnedHashSet),
                "Multiset" => Ok(ReturnShape::OwnedMultiset),
                _ => {
                    if user_types.contains(&name) {
                        Ok(ReturnShape::OwnedUserType(seg.ident.clone()))
                    } else if is_primitive_like(&name) {
                        Ok(ReturnShape::Primitive)
                    } else {
                        Err(Error::new_spanned(
                            ty,
                            format!(
                                "verus_pbt: unsupported return type `{}`.",
                                name
                            ),
                        ))
                    }
                }
            }
        }
        Type::Tuple(tt) if tt.elems.is_empty() => Ok(ReturnShape::Unit),
        _ => Err(Error::new_spanned(
            ty,
            "verus_pbt: unsupported return type.",
        )),
    }
}

// ---------------------------------------------------------------------------
// Contract rewriter
// ---------------------------------------------------------------------------

/// Rewriter applied to each `requires` / `ensures` expression. Two jobs:
///   1. Strip `.deep_view()` method calls (the receiver becomes the harness
///      binding directly).
///   2. Rename calls to known spec fns: `f(x)` → `exec_f(x)` for free fns,
///      and `x.f(...)` → `x.exec_f(...)` for spec methods.
struct ContractRewriter<'a> {
    spec_fn_names: &'a HashSet<String>,
    /// Per parameter: how `<param>.deep_view()` translates at the call site.
    param_call_form: &'a HashMap<String, TokenStream2>,
    /// Idents whose value is a user-defined type at the harness level (the
    /// user's OWN type, e.g. `User`). Maps ident-name → user type name. Used
    /// to insert `__pbt_to_exec_T(&x)` conversions before spec-fn / spec-
    /// method calls that expect the engine `Exec*` form.
    user_typed_idents: &'a HashMap<String, Ident>,
    return_ident: Option<Ident>,
    return_shape: ReturnShape,
}

impl<'a> VisitMut for ContractRewriter<'a> {
    fn visit_expr_mut(&mut self, expr: &mut Expr) {
        // Recurse first so nested rewrites land before parent rewrites.
        verus_syn::visit_mut::visit_expr_mut(self, expr);

        // 0. Verus-style chained comparisons: `a <= b <= c` parses in
        // verus_syn as `(a <= b) <= c`. In Verus this is meaningful; in plain
        // Rust it's a type error. Rewrite to `(a <= b) && (b <= c)` when we
        // detect the shape.
        if let Some(rewritten) = rewrite_chained_compare(expr) {
            *expr = rewritten;
            return;
        }

        // 1. Strip `<expr>.deep_view()`.
        if let Expr::MethodCall(ExprMethodCall { receiver, method, args, .. }) = expr {
            if method == "deep_view" && args.is_empty() {
                let receiver_clone = (**receiver).clone();

                // Return-named ident: re-shape per ReturnShape.
                if let Some(ret_ident) = &self.return_ident {
                    if expr_is_ident(&receiver_clone, ret_ident) {
                        *expr = self.rewrite_return_deep_view(ret_ident.clone());
                        return;
                    }
                }

                // Parameter ident: substitute the registered call form.
                if let Some(name) = ident_of_expr(&receiver_clone) {
                    if let Some(call_form) = self.param_call_form.get(&name) {
                        let cf = call_form.clone();
                        *expr = verus_syn::parse_quote!( #cf );
                        return;
                    }
                }

                // Otherwise: just unwrap to the receiver (best-effort).
                *expr = receiver_clone;
                return;
            }
        }

        // 2. Rename `f(args)` to `exec_f(args)` when `f` is a known spec fn.
        // If an argument is a bare user-typed ident, insert the conversion.
        if let Expr::Call(call) = expr {
            if let Expr::Path(ExprPath { path, qself: None, .. }) = call.func.as_mut() {
                if path.segments.len() == 1 {
                    let seg = &mut path.segments[0];
                    let name = seg.ident.to_string();
                    if self.spec_fn_names.contains(&name) {
                        seg.ident = format_ident!("exec_{}", seg.ident);
                        // Convert any bare user-typed argument: `f(u)` where
                        // `u: User` → `exec_f(&__pbt_to_exec_User(&u))`.
                        for arg in call.args.iter_mut() {
                            self.convert_user_arg(arg);
                        }
                    }
                }
            }
        }

        // 3. Spec-method call on a user-typed receiver. We route it through
        // the engine companion: `u.f(..)` →
        // `<U as ToExecModel>::to_exec_model(&u).exec_f(..)`. This works for
        // both in-block spec methods and EXTERNAL ones (defined + provided in
        // another file), since `exec_f` is generated on the `Exec*` type at
        // its `#[pbt_provide]` site and reached by path.
        if let Expr::MethodCall(mc) = expr {
            let name = mc.method.to_string();
            let recv_user_ty = ident_of_expr(&mc.receiver)
                .and_then(|n| self.user_typed_idents.get(&n).cloned());

            if let Some(user_ty) = recv_user_ty {
                // Receiver is a user-typed ident: always treat the call as a
                // spec-companion call (unknown methods on a sampled user value
                // can only be spec companions in this context).
                if !is_known_runtime_method(&name) {
                    mc.method = format_ident!("exec_{}", mc.method);
                    let recv_name = ident_of_expr(&mc.receiver).unwrap();
                    let recv_id = format_ident!("{}", recv_name);
                    let new_recv: Expr = verus_syn::parse_quote! {
                        <#user_ty as ::verus_pbt_runtime::ToExecModel>::to_exec_model(&#recv_id)
                    };
                    *mc.receiver = new_recv;
                }
            } else if self.spec_fn_names.contains(&name) {
                // Receiver isn't a tracked user-typed ident, but the method is
                // a known in-block spec fn (e.g. chained `x.perm.is_revoked()`
                // where `x.perm` is already an Exec value): just rename.
                mc.method = format_ident!("exec_{}", mc.method);
            }
        }
    }
}

impl<'a> ContractRewriter<'a> {
    /// If `arg` is a bare user-typed ident `u` (or `*u`), replace it with
    /// `&__pbt_to_exec_User(&u)` so it can be passed to an `exec_*` spec fn
    /// (which takes the borrowed engine form).
    fn convert_user_arg(&self, arg: &mut Expr) {
        // Unwrap a single deref: `*p` where `p: &User`.
        let inner: &Expr = match &*arg {
            Expr::Unary(u) if matches!(u.op, verus_syn::UnOp::Deref(_)) => u.expr.as_ref(),
            other => other,
        };
        if let Some(name) = ident_of_expr(inner) {
            if let Some(user_ty) = self.user_typed_idents.get(&name) {
                let id = format_ident!("{}", name);
                *arg = verus_syn::parse_quote! {
                    &<#user_ty as ::verus_pbt_runtime::ToExecModel>::to_exec_model(&#id)
                };
            }
        }
    }

    fn rewrite_return_deep_view(&self, ret_ident: Ident) -> Expr {
        match &self.return_shape {
            ReturnShape::OwnedVec(_) => {
                verus_syn::parse_quote_spanned! { ret_ident.span() => #ret_ident.as_slice() }
            }
            ReturnShape::OwnedUserType(_)
            | ReturnShape::OwnedOption(_)
            | ReturnShape::OwnedHashMap
            | ReturnShape::OwnedHashSet
            | ReturnShape::OwnedMultiset => {
                verus_syn::parse_quote_spanned! { ret_ident.span() => &#ret_ident }
            }
            ReturnShape::Primitive | ReturnShape::Unit => {
                verus_syn::parse_quote_spanned! { ret_ident.span() => #ret_ident }
            }
        }
    }
}

fn ident_of_expr(expr: &Expr) -> Option<String> {
    if let Expr::Path(ExprPath { path, qself: None, .. }) = expr {
        if path.segments.len() == 1 && matches!(path.segments[0].arguments, PathArguments::None) {
            return Some(path.segments[0].ident.to_string());
        }
    }
    None
}

/// Detects `a <= b <= c` (or `<`, `<=`, `<`, `<=` mix) parsed as a left-
/// associative chain `(a <= b) <= c`, and rewrites it as
/// `(a <= b) && (b <= c)`. Same handling for `a > b > c` etc., and for
/// equality runs `a == b == c`. Anything else: returns None.
fn rewrite_chained_compare(expr: &Expr) -> Option<Expr> {
    use verus_syn::BinOp;

    fn is_comparison(op: &BinOp) -> bool {
        matches!(
            op,
            BinOp::Lt(..)
                | BinOp::Le(..)
                | BinOp::Gt(..)
                | BinOp::Ge(..)
                | BinOp::Eq(..)
                | BinOp::Ne(..)
        )
    }

    let outer = match expr {
        Expr::Binary(b) if is_comparison(&b.op) => b,
        _ => return None,
    };

    let inner = match outer.left.as_ref() {
        Expr::Binary(b) if is_comparison(&b.op) => b,
        _ => return None,
    };

    // Reconstruct: (a OP1 b) OP2 c  ===>  (a OP1 b) && (b OP2 c)
    let inner_b: &Expr = inner.right.as_ref();
    let outer_left: Expr = (*outer.left).clone();
    let inner_b_clone: Expr = inner_b.clone();
    let op2 = outer.op.clone();
    let outer_right: Expr = (*outer.right).clone();
    let new_right: Expr = verus_syn::parse_quote! { #inner_b_clone #op2 #outer_right };
    Some(verus_syn::parse_quote! { (#outer_left) && (#new_right) })
}

fn expr_is_ident(expr: &Expr, ident: &Ident) -> bool {
    if let Expr::Path(ExprPath { path, qself: None, .. }) = expr {
        if path.segments.len() == 1 {
            return &path.segments[0].ident == ident;
        }
    }
    false
}

fn return_ident_of(item_fn: &ItemFn) -> Option<Ident> {
    if let ReturnType::Type(_, _, output_pat, _) = &item_fn.sig.output {
        if let Some(boxed) = output_pat.as_ref() {
            return pat_to_ident(&boxed.1);
        }
    }
    None
}

fn pat_to_ident(pat: &Pat) -> Option<Ident> {
    match pat {
        Pat::Ident(pi) => Some(pi.ident.clone()),
        Pat::Type(PatType { pat, .. }) => pat_to_ident(pat),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Phase 4: inline forall / exists lifting
// ---------------------------------------------------------------------------

/// Detects whether an expression contains a `forall` or `exists` quantifier.
/// We walk the AST with verus_syn's read-only visitor.
fn contains_quantifier(expr: &Expr) -> bool {
    struct QFinder {
        found: bool,
    }
    impl<'a> Visit<'a> for QFinder {
        fn visit_expr_unary(&mut self, e: &'a ExprUnary) {
            if matches!(e.op, UnOp::Forall(..) | UnOp::Exists(..)) {
                self.found = true;
                return;
            }
            verus_syn::visit::visit_expr_unary(self, e);
        }
    }
    let mut f = QFinder { found: false };
    f.visit_expr(expr);
    f.found
}

/// Free-variable analysis: collect all simple-path identifiers reachable from
/// `expr` that are NOT bound locally by a closure / let / pattern. This is a
/// best-effort pass — when in doubt it returns the ident as a free variable
/// (the worst case is that the synthetic spec fn carries an unused
/// parameter, which is benign).
fn collect_free_idents(expr: &Expr, exclude_built_ins: bool) -> Vec<String> {
    struct Collector {
        bound: Vec<String>,
        free: Vec<String>,
        exclude_built_ins: bool,
    }
    impl Collector {
        fn is_built_in(&self, name: &str) -> bool {
            // Don't capture commonly-used type / module names that are not
            // actual local variables. Verus / Rust language keywords aren't
            // visited as ident expressions.
            matches!(
                name,
                "true" | "false" | "Some" | "None" | "Ok" | "Err"
            )
        }
    }
    impl<'a> Visit<'a> for Collector {
        fn visit_expr_closure(&mut self, c: &'a verus_syn::ExprClosure) {
            // Closure params: bind each ident pattern in the body scope.
            let snapshot = self.bound.len();
            for input in &c.inputs {
                collect_pat_binders(&input.pat, &mut self.bound);
            }
            verus_syn::visit::visit_expr(self, &c.body);
            self.bound.truncate(snapshot);
        }
        fn visit_expr_path(&mut self, p: &'a ExprPath) {
            if p.qself.is_none()
                && p.path.segments.len() == 1
                && matches!(p.path.segments[0].arguments, PathArguments::None)
            {
                let name = p.path.segments[0].ident.to_string();
                if !self.bound.contains(&name) {
                    if !(self.exclude_built_ins && self.is_built_in(&name)) {
                        if !self.free.contains(&name) {
                            self.free.push(name);
                        }
                    }
                }
            }
            verus_syn::visit::visit_expr_path(self, p);
        }
        fn visit_local(&mut self, l: &'a verus_syn::Local) {
            // Visit the init expression in the OLD scope, then bind.
            if let Some(init) = &l.init {
                verus_syn::visit::visit_expr(self, &init.expr);
            }
            collect_pat_binders(&l.pat, &mut self.bound);
        }
    }

    fn collect_pat_binders(pat: &Pat, bound: &mut Vec<String>) {
        match pat {
            Pat::Ident(pi) => bound.push(pi.ident.to_string()),
            Pat::Type(pt) => collect_pat_binders(&pt.pat, bound),
            Pat::Tuple(t) => {
                for p in &t.elems {
                    collect_pat_binders(p, bound);
                }
            }
            Pat::TupleStruct(ts) => {
                for p in &ts.elems {
                    collect_pat_binders(p, bound);
                }
            }
            Pat::Struct(s) => {
                for f in &s.fields {
                    collect_pat_binders(&f.pat, bound);
                }
            }
            _ => {}
        }
    }

    let mut c = Collector { bound: vec![], free: vec![], exclude_built_ins };
    c.visit_expr(expr);
    c.free
}

/// Walk a contract clause and detect references the macro definitely cannot
/// turn into a runnable form. Returns a descriptive error if found.
///
/// NOTE (Phase 3): method calls on user-typed receivers are no longer flagged
/// here. They are now always lowered to `<T as ToExecModel>::to_exec_model(..)
/// .exec_<m>()`, which resolves across files by trait/path. If the type was
/// never `#[pbt_provide]`'d, the `on_unimplemented` diagnostics on
/// `ToExecModel` / `PbtSpecCompanion` fire at the harness call site — a
/// better, localized error than a macro-time guess. This function is retained
/// as a hook for future high-confidence checks; currently it accepts
/// everything.
fn check_clause_resolvable(
    _clause: &Expr,
    _spec_fn_names: &HashSet<String>,
    _user_typed_idents: &HashMap<String, Ident>,
    _self_ident: Option<&Ident>,
) -> Result<(), Error> {
    Ok(())
}

#[allow(dead_code)]
fn check_clause_resolvable_unused(
    clause: &Expr,
    spec_fn_names: &HashSet<String>,
    user_typed_idents: &HashMap<String, Ident>,
    self_ident: Option<&Ident>,
) -> Result<(), Error> {
    struct Checker<'a> {
        spec_fn_names: &'a HashSet<String>,
        user_typed_idents: &'a HashMap<String, Ident>,
        self_ident: Option<&'a Ident>,
        error: Option<Error>,
    }
    impl<'a> Checker<'a> {
        fn receiver_is_user_typed(&self, recv: &Expr) -> bool {
            if let Some(name) = ident_of_expr(recv) {
                if self.user_typed_idents.contains_key(&name) {
                    return true;
                }
                if let Some(s) = self.self_ident {
                    if name == s.to_string() {
                        return true;
                    }
                }
            }
            false
        }
    }
    impl<'ast, 'a> Visit<'ast> for Checker<'a> {
        fn visit_expr_method_call(&mut self, mc: &'ast verus_syn::ExprMethodCall) {
            let method = mc.method.to_string();
            if self.error.is_none()
                && self.receiver_is_user_typed(&mc.receiver)
                && !self.spec_fn_names.contains(&method)
                && !is_known_runtime_method(&method)
            {
                self.error = Some(Error::new_spanned(
                    &mc.method,
                    format!(
                        "verus_pbt: the contract calls `.{method}(...)`, but `{method}` is \
                         not a spec fn defined inside this verus_pbt_unverified! block.\n\n\
                         The harness needs a runnable companion (`exec_{method}`) to evaluate \
                         this clause, and the macro can only generate one for spec fns it can \
                         see between its own braces. If `{method}` is defined in another module \
                         or file, the macro cannot reach it.\n\n\
                         Fix: move the spec fn `{method}` (and any types/spec fns it depends on) \
                         into this same `verus_pbt_unverified! {{ ... }}` block.",
                        method = method
                    ),
                ));
            }
            verus_syn::visit::visit_expr_method_call(self, mc);
        }
    }
    let mut c = Checker {
        spec_fn_names,
        user_typed_idents,
        self_ident,
        error: None,
    };
    c.visit_expr(clause);
    match c.error {
        Some(e) => Err(e),
        None => Ok(()),
    }
}

/// Methods the engine / runtime knows how to compile on exec values. These
/// are NOT spec fns the user defined, so they must not be flagged as
/// "unresolved spec method". Mirrors the method list in exec_spec.rs plus
/// the deep_view bridge.
fn is_known_runtime_method(name: &str) -> bool {
    matches!(
        name,
        "deep_view"
            | "len"
            | "dom"
            | "index"
            | "drop_first"
            | "drop_last"
            | "add"
            | "push"
            | "update"
            | "subrange"
            | "to_multiset"
            | "take"
            | "skip"
            | "last"
            | "first"
            | "count"
            | "is_prefix_of"
            | "is_suffix_of"
            | "contains"
            | "contains_key"
            | "get"
            | "index_of"
            | "index_of_first"
            | "index_of_last"
            | "insert"
            | "remove"
            | "intersect"
            | "union"
            | "difference"
            | "sub"
            | "unwrap"
            | "as_slice"
            | "clone"
    )
}

/// For a clause that contains an inline quantifier, lift the entire clause
/// into a synthetic `spec fn __pbt_clause_<n>(...)`. Returns:
///   - the synthetic spec fn (as an `ItemFn` to push into engine_items)
///   - a replacement clause that calls it: `__pbt_clause_n(arg1, arg2, ...)`
///
/// Free-variable analysis selects which params of the exec fn (and which
/// `result` ident, if any) the clause captures.
fn lift_quantified_clause(
    clause: &Expr,
    exec_fn_name: &Ident,
    counter: &mut u64,
    param_specs: &[(Ident, TokenStream2)], // (name, spec_type) for each fn param
    return_ident: Option<&Ident>,
    return_shape: &ReturnShape,
) -> (TokenStream2, TokenStream2) {
    let id = *counter;
    *counter += 1;
    let synth_name = format_ident!("__pbt_clause_{}_{}", exec_fn_name, id);

    let free = collect_free_idents(clause, /*exclude_built_ins=*/ true);

    // Build (param_name, spec_type) pairs for the synthetic spec fn,
    // dropping any free idents that aren't params or the return.
    let mut sig_params: Vec<(Ident, TokenStream2)> = Vec::new();
    let mut call_args: Vec<TokenStream2> = Vec::new();

    for free_name in &free {
        // Match against fn parameters first.
        if let Some((id, spec_ty)) = param_specs.iter().find(|(p, _)| p == free_name) {
            sig_params.push((id.clone(), spec_ty.clone()));
            // The harness call passes `<param>.deep_view()` for the spec
            // type; that's already handled by ContractRewriter when it sees
            // the synthetic spec fn — except the synthetic spec fn ITSELF
            // takes the spec type and the rewriter gets the call form. We
            // want the call site of the lifted clause to read
            // `__pbt_clause_n(<param>.deep_view(), ...)`, then the existing
            // rewriter strips `.deep_view()` per param shape.
            call_args.push(quote! { #id.deep_view() });
            continue;
        }
        // Match against the return ident.
        if let Some(ri) = return_ident {
            if free_name == &ri.to_string() {
                let spec_ty = return_shape_to_spec_type(return_shape);
                sig_params.push((ri.clone(), spec_ty));
                call_args.push(quote! { #ri.deep_view() });
                continue;
            }
        }
        // Free vars that don't bind to params: skip silently. They're
        // probably constants or names from the surrounding module.
    }

    let sig_param_decls = sig_params.iter().map(|(n, t)| quote! { #n: #t });

    // Emit the synthetic spec fn.
    let body = clause;
    let synth_fn = quote! {
        spec fn #synth_name(#(#sig_param_decls),*) -> bool {
            #body
        }
    };

    let replacement = quote! { #synth_name(#(#call_args),*) };
    (synth_fn, replacement)
}

fn return_shape_to_spec_type(shape: &ReturnShape) -> TokenStream2 {
    match shape {
        ReturnShape::Unit => quote! { () },
        ReturnShape::Primitive => quote! { _ }, // shouldn't happen in practice
        ReturnShape::OwnedVec(e) => {
            let inner = match e {
                ParamElem::Primitive(t) => quote! { #t },
                ParamElem::UserType(n) => quote! { #n },
            };
            quote! { Seq<#inner> }
        }
        ReturnShape::OwnedOption(e) => {
            let inner = match e {
                ParamElem::Primitive(t) => quote! { #t },
                ParamElem::UserType(n) => quote! { #n },
            };
            quote! { Option<#inner> }
        }
        ReturnShape::OwnedHashMap => quote! { Map<_, _> },
        ReturnShape::OwnedHashSet => quote! { Set<_> },
        ReturnShape::OwnedMultiset => quote! { Multiset<_> },
        ReturnShape::OwnedUserType(n) => quote! { #n },
    }
}

// ---------------------------------------------------------------------------
// PbtStrategy impl emission for user types (Phase 3)
// ---------------------------------------------------------------------------

/// Build a `BoxedStrategy` expression for a single field type. The strategy
/// produces the harness type (user's own type for user-defined elements).
fn strategy_for_type(ty: &Type, user_types: &HashSet<String>) -> Result<TokenStream2, Error> {
    let elem = classify_param_elem(ty, user_types)?;
    let elem_ty = elem.harness_type();
    Ok(quote! {
        <#elem_ty as ::verus_pbt_runtime::PbtStrategy>::pbt_strategy()
    })
}

/// Emit everything the harness needs for a user-defined struct:
///   - `PbtStrategy for <Struct>` (samples the user's OWN type)
///   - manual `Clone` + `Debug` (we can't derive on the Verus type without
///     tripping Verus's auto-derive checks)
///   - `__pbt_to_exec_<Struct>(&Struct) -> ExecStruct` converter.
fn emit_struct_support(
    item_struct: &ItemStruct,
    user_types: &HashSet<String>,
) -> Result<TokenStream2, Error> {
    let name = &item_struct.ident;
    let exec_name = format_ident!("Exec{}", name);
    let conv = to_exec_fn_name(name);

    let clone_impl = emit_clone_impl_struct(name, &item_struct.fields);
    let debug_impl = emit_debug_impl(name);

    let strategy_impl = match &item_struct.fields {
        Fields::Named(named) => {
            let field_names: Vec<&Ident> =
                named.named.iter().map(|f| f.ident.as_ref().unwrap()).collect();
            let field_strats: Vec<TokenStream2> = named
                .named
                .iter()
                .map(|f| strategy_for_type(&f.ty, user_types))
                .collect::<Result<Vec<_>, _>>()?;
            let tuple_pat = quote! { (#(#field_names),*) };
            quote! {
                impl ::verus_pbt_runtime::PbtStrategy for #name {
                    type Strategy = ::proptest::strategy::BoxedStrategy<#name>;
                    fn pbt_strategy() -> Self::Strategy {
                        use ::proptest::strategy::Strategy;
                        (#(#field_strats),*)
                            .prop_map(|#tuple_pat| #name { #(#field_names),* })
                            .boxed()
                    }
                }
            }
        }
        Fields::Unnamed(unnamed) => {
            let n = unnamed.unnamed.len();
            let field_strats: Vec<TokenStream2> = unnamed
                .unnamed
                .iter()
                .map(|f| strategy_for_type(&f.ty, user_types))
                .collect::<Result<Vec<_>, _>>()?;
            let var_names: Vec<Ident> = (0..n).map(|i| format_ident!("__f{}", i)).collect();
            let tuple_pat = quote! { (#(#var_names),*) };
            quote! {
                impl ::verus_pbt_runtime::PbtStrategy for #name {
                    type Strategy = ::proptest::strategy::BoxedStrategy<#name>;
                    fn pbt_strategy() -> Self::Strategy {
                        use ::proptest::strategy::Strategy;
                        (#(#field_strats),*)
                            .prop_map(|#tuple_pat| #name(#(#var_names),*))
                            .boxed()
                    }
                }
            }
        }
        Fields::Unit => quote! {
            impl ::verus_pbt_runtime::PbtStrategy for #name {
                type Strategy = ::proptest::strategy::BoxedStrategy<#name>;
                fn pbt_strategy() -> Self::Strategy {
                    use ::proptest::strategy::Strategy;
                    ::proptest::strategy::Just(#name).boxed()
                }
            }
        },
    };

    // Converter body.
    let conv_body = match &item_struct.fields {
        Fields::Named(named) => {
            let inits = named.named.iter().map(|f| {
                let fname = f.ident.as_ref().unwrap();
                let conv_field = elem_to_exec_expr(&f.ty, quote! { self_value.#fname }, user_types);
                quote! { #fname: #conv_field }
            });
            quote! { #exec_name { #(#inits),* } }
        }
        Fields::Unnamed(unnamed) => {
            let inits = unnamed.unnamed.iter().enumerate().map(|(i, f)| {
                let idx = verus_syn::Index::from(i);
                elem_to_exec_expr(&f.ty, quote! { self_value.#idx }, user_types)
            });
            quote! { #exec_name(#(#inits),*) }
        }
        Fields::Unit => quote! { #exec_name },
    };

    Ok(quote! {
        #clone_impl
        #debug_impl
        #strategy_impl
        impl ::verus_pbt_runtime::ToExecModel for #name {
            type Exec = #exec_name;
            fn to_exec_model(&self) -> #exec_name {
                let self_value = self;
                #conv_body
            }
        }
        impl ::verus_pbt_runtime::PbtSpecCompanion for #name {}
        // Back-compat free fn (used by older call sites); delegates to the trait.
        #[allow(non_snake_case)]
        fn #conv(self_value: &#name) -> #exec_name {
            <#name as ::verus_pbt_runtime::ToExecModel>::to_exec_model(self_value)
        }
    })
}

fn emit_enum_support(
    item_enum: &ItemEnum,
    user_types: &HashSet<String>,
) -> Result<TokenStream2, Error> {
    let name = &item_enum.ident;
    let exec_name = format_ident!("Exec{}", name);
    let conv = to_exec_fn_name(name);

    if item_enum.variants.is_empty() {
        return Err(Error::new_spanned(
            item_enum,
            "verus_pbt: cannot generate a strategy for an empty enum",
        ));
    }

    let clone_impl = emit_clone_impl_enum(name, item_enum);
    let debug_impl = emit_debug_impl(name);

    let mut variant_arms: Vec<TokenStream2> = Vec::new();
    let mut conv_arms: Vec<TokenStream2> = Vec::new();
    for variant in &item_enum.variants {
        let vname = &variant.ident;
        match &variant.fields {
            Fields::Named(named) => {
                let field_names: Vec<&Ident> =
                    named.named.iter().map(|f| f.ident.as_ref().unwrap()).collect();
                let field_strats: Vec<TokenStream2> = named
                    .named
                    .iter()
                    .map(|f| strategy_for_type(&f.ty, user_types))
                    .collect::<Result<Vec<_>, _>>()?;
                let tuple_pat = quote! { (#(#field_names),*) };
                variant_arms.push(quote! {
                    (#(#field_strats),*)
                        .prop_map(|#tuple_pat| #name::#vname { #(#field_names),* })
                        .boxed()
                });
                // converter arm
                let conv_inits = named.named.iter().map(|f| {
                    let fname = f.ident.as_ref().unwrap();
                    let conv_field = elem_to_exec_expr(&f.ty, quote! { #fname.clone() }, user_types);
                    quote! { #fname: #conv_field }
                });
                conv_arms.push(quote! {
                    #name::#vname { #(#field_names),* } => #exec_name::#vname { #(#conv_inits),* }
                });
            }
            Fields::Unnamed(unnamed) => {
                let n = unnamed.unnamed.len();
                let field_strats: Vec<TokenStream2> = unnamed
                    .unnamed
                    .iter()
                    .map(|f| strategy_for_type(&f.ty, user_types))
                    .collect::<Result<Vec<_>, _>>()?;
                let var_names: Vec<Ident> = (0..n).map(|i| format_ident!("__f{}", i)).collect();
                let tuple_pat = quote! { (#(#var_names),*) };
                variant_arms.push(quote! {
                    (#(#field_strats),*)
                        .prop_map(|#tuple_pat| #name::#vname(#(#var_names),*))
                        .boxed()
                });
                let conv_inits = unnamed.unnamed.iter().enumerate().map(|(i, f)| {
                    let vn = &var_names[i];
                    elem_to_exec_expr(&f.ty, quote! { #vn.clone() }, user_types)
                });
                conv_arms.push(quote! {
                    #name::#vname(#(#var_names),*) => #exec_name::#vname(#(#conv_inits),*)
                });
            }
            Fields::Unit => {
                variant_arms.push(quote! {
                    ::proptest::strategy::Just(#name::#vname).boxed()
                });
                conv_arms.push(quote! {
                    #name::#vname => #exec_name::#vname
                });
            }
        }
    }

    Ok(quote! {
        #clone_impl
        #debug_impl
        impl ::verus_pbt_runtime::PbtStrategy for #name {
            type Strategy = ::proptest::strategy::BoxedStrategy<#name>;
            fn pbt_strategy() -> Self::Strategy {
                use ::proptest::strategy::Strategy;
                ::proptest::prop_oneof![
                    #(#variant_arms),*
                ]
                .boxed()
            }
        }
        impl ::verus_pbt_runtime::ToExecModel for #name {
            type Exec = #exec_name;
            fn to_exec_model(&self) -> #exec_name {
                match self {
                    #(#conv_arms),*
                }
            }
        }
        impl ::verus_pbt_runtime::PbtSpecCompanion for #name {}
        #[allow(non_snake_case)]
        fn #conv(self_value: &#name) -> #exec_name {
            <#name as ::verus_pbt_runtime::ToExecModel>::to_exec_model(self_value)
        }
    })
}

/// Build the expression converting a field of type `ty` (accessed via `expr`,
/// which yields the user-side value) into its `Exec*` form.
fn elem_to_exec_expr(ty: &Type, expr: TokenStream2, user_types: &HashSet<String>) -> TokenStream2 {
    match classify_param_elem(ty, user_types) {
        Ok(ParamElem::Primitive(_)) => expr,
        Ok(ParamElem::UserType(name)) => {
            // Fully-qualified trait call: resolves across files and triggers
            // the ToExecModel `on_unimplemented` diagnostic if unprovided.
            quote! {
                <#name as ::verus_pbt_runtime::ToExecModel>::to_exec_model(&#expr)
            }
        }
        // Total fallback: keep as-is.
        Err(_) => quote! { #expr },
    }
}

fn emit_clone_impl_struct(name: &Ident, fields: &Fields) -> TokenStream2 {
    let body = match fields {
        Fields::Named(named) => {
            let field_clones = named.named.iter().map(|f| {
                let n = f.ident.as_ref().unwrap();
                quote! { #n: self.#n.clone() }
            });
            quote! { #name { #(#field_clones),* } }
        }
        Fields::Unnamed(unnamed) => {
            let field_clones = (0..unnamed.unnamed.len()).map(|i| {
                let idx = verus_syn::Index::from(i);
                quote! { self.#idx.clone() }
            });
            quote! { #name(#(#field_clones),*) }
        }
        Fields::Unit => quote! { #name },
    };
    quote! {
        impl ::std::clone::Clone for #name {
            fn clone(&self) -> Self {
                #body
            }
        }
    }
}

fn emit_debug_impl(name: &Ident) -> TokenStream2 {
    // We can't `#[derive(Debug)]` on the Verus-side type (Verus's derive
    // handling rejects it), and we can't reference the user type's fields
    // generically here without re-deriving. Instead, Debug delegates to the
    // engine's `Exec*` companion (which DOES derive a full Debug) by
    // converting through the generated `__pbt_to_exec_*` fn. This gives
    // useful counterexample output ("ExecUser { name_len: 1, ... }").
    let conv = to_exec_fn_name(name);
    quote! {
        impl ::std::fmt::Debug for #name {
            fn fmt(&self, f: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result {
                ::std::fmt::Debug::fmt(&#conv(self), f)
            }
        }
    }
}

fn emit_clone_impl_enum(name: &Ident, item_enum: &ItemEnum) -> TokenStream2 {
    let arms = item_enum.variants.iter().map(|variant| {
        let vname = &variant.ident;
        match &variant.fields {
            Fields::Named(named) => {
                let names: Vec<&Ident> =
                    named.named.iter().map(|f| f.ident.as_ref().unwrap()).collect();
                let clones = names.iter().map(|n| quote! { #n: #n.clone() });
                quote! {
                    #name::#vname { #(#names),* } => #name::#vname { #(#clones),* }
                }
            }
            Fields::Unnamed(unnamed) => {
                let n = unnamed.unnamed.len();
                let names: Vec<Ident> = (0..n).map(|i| format_ident!("__f{}", i)).collect();
                let clones = names.iter().map(|n| quote! { #n.clone() });
                quote! {
                    #name::#vname(#(#names),*) => #name::#vname(#(#clones),*)
                }
            }
            Fields::Unit => quote! {
                #name::#vname => #name::#vname
            },
        }
    });
    quote! {
        impl ::std::clone::Clone for #name {
            fn clone(&self) -> Self {
                match self {
                    #(#arms),*
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Harness emission
// ---------------------------------------------------------------------------

struct HarnessOutput {
    /// The `proptest! { ... }` block.
    harness_tokens: TokenStream2,
    /// Synthetic spec fns this harness's clauses required (Phase 4).
    synthetic_spec_fns: Vec<TokenStream2>,
}

fn emit_harness(
    target: &ContractTarget,
    spec_fn_names: &HashSet<String>,
    user_types: &HashSet<String>,
    clause_counter: &mut u64,
) -> Result<HarnessOutput, Error> {
    // Pull out the bits that depend on free-fn vs method shape.
    let (sig, fn_name, is_method, self_ty_for_method): (&verus_syn::Signature, &Ident, bool, Option<Ident>) =
        match target {
            ContractTarget::FreeFn(item_fn) => (&item_fn.sig, &item_fn.sig.ident, false, None),
            ContractTarget::Method { self_ty, method } => {
                (&method.sig, &method.sig.ident, true, Some(self_ty.clone()))
            }
        };
    let pbt_fn_name = if is_method {
        let self_str = self_ty_for_method.as_ref().unwrap().to_string();
        format_ident!("pbt_{}_{}", self_str, fn_name)
    } else {
        format_ident!("pbt_{}", fn_name)
    };

    // 1. Inspect parameters. Methods get a synthetic `self` ident bound
    // to the same shape as `&Self` (a `RefUserType`).
    let mut param_idents = Vec::new();
    let mut param_shapes = Vec::new();
    let mut self_ident: Option<Ident> = None;
    for p in &sig.inputs {
        match &p.kind {
            FnArgKind::Receiver(rcv) => {
                if !is_method {
                    return Err(Error::new_spanned(
                        p,
                        "verus_pbt: free fns cannot have a `self` receiver",
                    ));
                }
                if rcv.reference.is_none() {
                    return Err(Error::new_spanned(
                        p,
                        "verus_pbt: only `&self` is supported (no owned `self` or `&mut self`)",
                    ));
                }
                if rcv.mutability.is_some() {
                    return Err(Error::new_spanned(
                        p,
                        "verus_pbt: `&mut self` is not yet supported (Phase 2 work)",
                    ));
                }
                let self_ty = self_ty_for_method.as_ref().unwrap();
                // Recover the user-name (strip "Exec" if present). Whether or
                // not the type is defined in THIS block, we treat the self
                // receiver as a `RefUserType`: in-block types get a generated
                // strategy/converter here; external types resolve theirs by
                // trait across files (and surface the `on_unimplemented`
                // diagnostic if never `#[pbt_provide]`'d).
                let user_name_str = self_ty.to_string();
                let canonical_user_name = user_name_str
                    .strip_prefix("Exec")
                    .unwrap_or(&user_name_str);
                let canonical_user_ident =
                    Ident::new(canonical_user_name, self_ty.span());
                let synth_self =
                    Ident::new("self_value", proc_macro2::Span::call_site());
                param_idents.push(synth_self.clone());
                param_shapes.push(ParamShape::RefUserType(canonical_user_ident));
                self_ident = Some(synth_self);
            }
            FnArgKind::Typed(pat_type) => {
                let ident = match pat_to_ident(&pat_type.pat) {
                    Some(id) => id,
                    None => {
                        return Err(Error::new_spanned(
                            &pat_type.pat,
                            "verus_pbt: parameters must be simple `name: Type` patterns",
                        ));
                    }
                };
                let shape = classify_param_type(&pat_type.ty, user_types)?;
                param_idents.push(ident);
                param_shapes.push(shape);
            }
        }
    }

    // 2. Per-param call form for the rewriter.
    let mut param_call_form: HashMap<String, TokenStream2> = HashMap::new();
    let mut user_typed_idents: HashMap<String, Ident> = HashMap::new();
    for (id, shape) in param_idents.iter().zip(param_shapes.iter()) {
        param_call_form.insert(id.to_string(), shape.call_form_for_deep_view(id));
        if let ParamShape::RefUserType(t) | ParamShape::OwnedUserType(t) = shape {
            user_typed_idents.insert(id.to_string(), t.clone());
        }
    }
    let _ = &self_ident;

    // 3. Return shape and ident.
    let return_shape = classify_return(&sig.output, user_types)?;
    let return_ident = match target {
        ContractTarget::FreeFn(item_fn) => return_ident_of(item_fn),
        ContractTarget::Method { method, .. } => {
            // ImplItemFn return signature follows the same shape; reuse the
            // helper by faking a temporary ItemFn-shaped accessor.
            if let ReturnType::Type(_, _, output_pat, _) = &method.sig.output {
                if let Some(boxed) = output_pat.as_ref() {
                    pat_to_ident(&boxed.1)
                } else {
                    None
                }
            } else {
                None
            }
        }
    };

    // 4. Build (name, spec_type) for synthetic-spec-fn signature use.
    let param_specs: Vec<(Ident, TokenStream2)> = param_idents
        .iter()
        .zip(param_shapes.iter())
        .map(|(id, shape)| (id.clone(), shape.spec_type()))
        .collect();

    // 5. Process each requires/ensures clause.
    let mut synthetic_spec_fns: Vec<TokenStream2> = Vec::new();
    let mut rewritten_requires: Vec<TokenStream2> = Vec::new();
    let mut rewritten_ensures: Vec<TokenStream2> = Vec::new();

    let process_clause = |clause_expr: &Expr,
                          synthetic_spec_fns: &mut Vec<TokenStream2>,
                          counter: &mut u64|
     -> TokenStream2 {
        let mut clause_expr = clause_expr.clone();
        // For methods: rewrite `self` → `<self_value>` before further
        // processing so the rewriter and quantifier-lift see ordinary idents.
        if let Some(self_id) = &self_ident {
            replace_self_with_ident(&mut clause_expr, self_id);
        }

        if contains_quantifier(&clause_expr) {
            let (synth, replacement) = lift_quantified_clause(
                &clause_expr,
                fn_name,
                counter,
                &param_specs,
                return_ident.as_ref(),
                &return_shape,
            );
            synthetic_spec_fns.push(synth);
            let mut replacement_expr: Expr =
                verus_syn::parse2(replacement).expect("synthetic clause must parse");
            let synth_name_str = if let Expr::Call(c) = &replacement_expr {
                if let Expr::Path(p) = c.func.as_ref() {
                    p.path.segments.last().map(|s| s.ident.to_string())
                } else {
                    None
                }
            } else {
                None
            };
            let mut combined_specs = spec_fn_names.clone();
            if let Some(n) = synth_name_str {
                combined_specs.insert(n);
            }
            let mut rw = ContractRewriter {
                spec_fn_names: &combined_specs,
                param_call_form: &param_call_form,
                user_typed_idents: &user_typed_idents,
                return_ident: return_ident.clone(),
                return_shape: return_shape.clone(),
            };
            rw.visit_expr_mut(&mut replacement_expr);
            quote! { #replacement_expr }
        } else {
            let mut e = clause_expr;
            let mut rw = ContractRewriter {
                spec_fn_names,
                param_call_form: &param_call_form,
                user_typed_idents: &user_typed_idents,
                return_ident: return_ident.clone(),
                return_shape: return_shape.clone(),
            };
            rw.visit_expr_mut(&mut e);
            quote! { #e }
        }
    };

    if let Some(req) = &sig.spec.requires {
        for e in req.exprs.exprs.iter() {
            let mut checked = e.clone();
            if let Some(self_id) = &self_ident {
                replace_self_with_ident(&mut checked, self_id);
            }
            check_clause_resolvable(
                &checked,
                spec_fn_names,
                &user_typed_idents,
                self_ident.as_ref(),
            )?;
            rewritten_requires.push(process_clause(e, &mut synthetic_spec_fns, clause_counter));
        }
    }
    if let Some(ens) = &sig.spec.ensures {
        for e in ens.exprs.exprs.iter() {
            let mut checked = e.clone();
            if let Some(self_id) = &self_ident {
                replace_self_with_ident(&mut checked, self_id);
            }
            check_clause_resolvable(
                &checked,
                spec_fn_names,
                &user_typed_idents,
                self_ident.as_ref(),
            )?;
            rewritten_ensures.push(process_clause(e, &mut synthetic_spec_fns, clause_counter));
        }
    }

    // 6. Build the proptest harness body.
    let strategy_decls: Vec<TokenStream2> = param_idents
        .iter()
        .zip(param_shapes.iter())
        .map(|(id, shape)| {
            let ty = shape.harness_type();
            quote! { #id in ::verus_pbt_runtime::pbt_strategy::<#ty>() }
        })
        .collect();

    let real_call_args: Vec<TokenStream2> = param_idents
        .iter()
        .zip(param_shapes.iter())
        .map(|(id, shape)| shape.arg_for_real_call(id))
        .collect();

    let result_binding = return_ident
        .clone()
        .unwrap_or_else(|| Ident::new("__pbt_result", Span::call_site()));

    // Adapt the call to either `super::fn_name(...)` or
    // `super::Self::method(&self_value, ...)`. For methods the receiver is
    // already in `real_call_args[0]` (since we treat self as a ParamShape).
    let real_call: TokenStream2 = if is_method {
        let self_ty = self_ty_for_method.as_ref().unwrap();
        quote! { super::#self_ty::#fn_name(#(#real_call_args),*) }
    } else {
        quote! { super::#fn_name(#(#real_call_args),*) }
    };

    let result_let = match return_shape {
        ReturnShape::Unit => quote! {
            #real_call;
            let #result_binding: () = ();
            let _ = &#result_binding;
        },
        _ => quote! {
            let #result_binding = #real_call;
        },
    };

    let harness_tokens = quote_spanned! { fn_name.span() =>
        proptest! {
            #[test]
            fn #pbt_fn_name(
                #(#strategy_decls),*
            ) {
                #(::proptest::prop_assume!(#rewritten_requires);)*
                #result_let
                #(::proptest::prop_assert!(#rewritten_ensures);)*
            }
        }
    };

    Ok(HarnessOutput { harness_tokens, synthetic_spec_fns })
}

/// Walk an expression and replace every `self` ident with `replacement`.
fn replace_self_with_ident(expr: &mut Expr, replacement: &Ident) {
    struct R<'a> {
        replacement: &'a Ident,
    }
    impl<'a> VisitMut for R<'a> {
        fn visit_expr_path_mut(&mut self, p: &mut ExprPath) {
            for seg in p.path.segments.iter_mut() {
                if seg.ident == "self" {
                    seg.ident = self.replacement.clone();
                }
            }
            verus_syn::visit_mut::visit_expr_path_mut(self, p);
        }
    }
    let mut r = R { replacement };
    r.visit_expr_mut(expr);
}

// ---------------------------------------------------------------------------
// Top-level entry point
// ---------------------------------------------------------------------------

static UNIQUE_ID: AtomicU64 = AtomicU64::new(0);

fn fresh_mod_name() -> Ident {
    let id = UNIQUE_ID.fetch_add(1, Ordering::Relaxed);
    Ident::new(&format!("__verus_pbt_{}", id), Span::call_site())
}

pub fn expand(input: TokenStream, verified: bool) -> TokenStream {
    let parsed: PbtItems = parse_macro_input!(input as PbtItems);
    let classified = classify(parsed.0);

    // Build harnesses first; they may produce synthetic spec fns that need
    // to be appended to the engine input.
    let mut clause_counter: u64 = 0;
    let mut harnesses_tokens: Vec<TokenStream2> = Vec::new();
    let mut synthetic_spec_fns: Vec<TokenStream2> = Vec::new();
    for target in &classified.contract_targets {
        let out = match emit_harness(
            target,
            &classified.spec_fn_names,
            &classified.user_type_names,
            &mut clause_counter,
        ) {
            Ok(h) => h,
            Err(err) => return err.to_compile_error().into(),
        };
        harnesses_tokens.push(out.harness_tokens);
        synthetic_spec_fns.extend(out.synthetic_spec_fns);
    }

    // Build the engine input: classified.engine_items + synthetic spec fns.
    let engine_items_ts = {
        let items = &classified.engine_items;
        quote! {
            #(#items)*
            #(#synthetic_spec_fns)*
        }
    };

    let engine_block: TokenStream2 =
        super::exec_spec::exec_spec(engine_items_ts.into(), /*unverified=*/ !verified).into();

    // Pass-through items.
    let v = crate::syntax::Vstd(Span::call_site());
    let passthrough_block = {
        let items = &classified.passthrough_items;
        quote! {
            #v::prelude::verus! {
                #(#items)*
            }
        }
    };

    // Strategy + Clone/Debug + to_exec converter for each user type.
    let strategy_impls: Result<Vec<TokenStream2>, Error> = classified
        .user_types
        .iter()
        .map(|ut| match ut {
            UserType::Struct(s) => emit_struct_support(s, &classified.user_type_names),
            UserType::Enum(e) => emit_enum_support(e, &classified.user_type_names),
        })
        .collect();
    let strategy_block = match strategy_impls {
        Ok(impls) => {
            if impls.is_empty() {
                quote! {}
            } else {
                quote! {
                    #(#impls)*
                }
            }
        }
        Err(err) => return err.to_compile_error().into(),
    };

    // Tier-4 external stub companions: emit `exec_<name>` fns into the harness
    // module so contract calls `exec_<name>(..)` resolve. Errors here surface
    // as compile errors at the macro site.
    let external_companions = {
        let mut out = TokenStream2::new();
        for body in &classified.external_provide_bodies {
            match crate::contrib::external_pbt_provide::emit_companions(body.clone()) {
                Ok(ts) => out.extend(ts),
                Err(err) => return err.to_compile_error().into(),
            }
        }
        out
    };

    // Single test module holding strategy/Clone/Debug/converter support AND
    // the proptest harnesses, so the harnesses can call the generated
    // `__pbt_to_exec_*` converters and `pbt_strategy::<UserType>()` directly.
    let mod_name = fresh_mod_name();
    let test_mod = if harnesses_tokens.is_empty() && classified.user_types.is_empty() {
        quote! {}
    } else {
        quote! {
            #[cfg(test)]
            #[allow(non_snake_case)]
            #[allow(unused_imports)]
            #[allow(dead_code)]
            mod #mod_name {
                use super::*;
                use ::proptest::prelude::*;
                #strategy_block
                #external_companions
                #(#harnesses_tokens)*
            }
        }
    };

    let combined = quote! {
        #engine_block
        #passthrough_block
        #test_mod
    };

    combined.into()
}
