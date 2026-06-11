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
    /// `runtime fn name → spec fn name` redirect from
    /// `#[verifier::when_used_as_spec(spec_X)]` attributes. The contract
    /// rewriter consults this when emitting `exec_<...>` calls so a runtime
    /// fn marked as a spec proxy lowers to the right companion.
    when_used_as_spec_redirect: HashMap<String, String>,
}

/// Extract the spec-fn target from a `#[verifier::when_used_as_spec(spec_X)]`
/// attribute on a runtime fn. Returns the spec fn name as a String.
fn extract_when_used_as_spec(attrs: &[verus_syn::Attribute]) -> Option<String> {
    for attr in attrs {
        let path = attr.path();
        if path.leading_colon.is_some() {
            continue;
        }
        let segs: Vec<String> = path.segments.iter().map(|s| s.ident.to_string()).collect();
        let segs: Vec<&str> = segs.iter().map(|s| s.as_str()).collect();
        if !matches!(&segs[..], ["verifier", "when_used_as_spec"]) {
            continue;
        }
        if let verus_syn::Meta::List(list) = &attr.meta {
            if let Ok(id) = verus_syn::parse2::<Ident>(list.tokens.clone()) {
                return Some(id.to_string());
            }
        }
    }
    None
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
    let mut when_used_as_spec_redirect: HashMap<String, String> = HashMap::new();

    // First pass: collect when_used_as_spec mappings before classifying so
    // contract rewrites for any item see the full redirect map.
    for item in &items {
        match item {
            Item::Fn(f) => {
                if let Some(t) = extract_when_used_as_spec(&f.attrs) {
                    when_used_as_spec_redirect.insert(f.sig.ident.to_string(), t);
                }
            }
            Item::Impl(im) => {
                for ii in &im.items {
                    if let verus_syn::ImplItem::Fn(f) = ii {
                        if let Some(t) = extract_when_used_as_spec(&f.attrs) {
                            when_used_as_spec_redirect
                                .insert(f.sig.ident.to_string(), t);
                        }
                    }
                }
            }
            _ => {}
        }
    }

    for item in items {
        match &item {
            Item::Fn(item_fn) => match &item_fn.sig.mode {
                FnMode::Spec(..) => {
                    spec_fn_names.insert(item_fn.sig.ident.to_string());
                    engine_items.push(item.clone());
                }
                // `fn` (default) and explicit `exec fn` both denote
                // executable code. Either is valid as a contract-bearing
                // target that the harness should sample and run.
                FnMode::Default | FnMode::Exec(..) => {
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
                            } else if matches!(
                                impl_fn.sig.mode,
                                FnMode::Default | FnMode::Exec(..)
                            ) {
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
        when_used_as_spec_redirect,
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
    /// `[E; N]` — fixed-size array. `N` is a const expression (an integer
    /// literal after substitution by `#[pbt(N = 4)]`). The harness samples
    /// a `Vec<E>` of length `N` and converts via `core::array::from_fn`.
    OwnedArray(ParamElem, Expr),
    /// `&[E; N]` — fixed-size array reference. Same shape as `OwnedArray`,
    /// but the call site borrows the sampled array.
    RefArray(ParamElem, Expr),
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
    /// `&str` — string slice. The harness samples a `String` and passes
    /// it via `as_str()`. Contracts that read `s@` get a deep_view onto the
    /// `Seq<char>` projection (`s.chars().collect::<Vec<_>>()`).
    RefStr,
    /// `String` — owned string. Harness samples directly.
    OwnedString,
    /// `&mut <inner>`. The harness samples a value of the inner shape's
    /// harness type, snapshots its deep_view before the call, and passes
    /// `&mut <id>` as the argument. Contracts mentioning `old(<id>)@` lower
    /// to the snapshot; bare `<id>@` (or `final(<id>)@`) lowers to the
    /// post-call deep_view.
    ///
    /// Limitation: not every inner shape is sound to mutate through. We
    /// support `OwnedVec`, `OwnedHashMap`, `OwnedHashSet`, `OwnedString`,
    /// `OwnedUserType`, and `OwnedOption` — shapes whose harness binding is
    /// already a value the test owns. Reference shapes (`Slice`, `RefStr`,
    /// `RefUserType`) are rejected with a diagnostic.
    MutRef(Box<ParamShape>),
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
            ParamShape::OwnedArray(e, _) | ParamShape::RefArray(e, _) => {
                // Sample as a Vec<E>; fixed-length convergence is enforced
                // by the strategy decl (vec(elem_strategy, N..=N)). The
                // harness converts the Vec to `[E; N]` at the call site.
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
            ParamShape::RefStr | ParamShape::OwnedString => {
                quote! { ::std::string::String }
            }
            ParamShape::MutRef(inner) => inner.harness_type(),
        }
    }

    /// What to put in the call to `super::<fn>(...)` at the harness site.
    fn arg_for_real_call(&self, harness_ident: &Ident) -> TokenStream2 {
        match self {
            ParamShape::Primitive(_) => quote! { #harness_ident },
            ParamShape::OwnedVec(_) => quote! { #harness_ident.clone() },
            ParamShape::Slice(_) => quote! { #harness_ident.as_slice() },
            ParamShape::OwnedArray(elem, len) => {
                // `[E; N]` by value: use array::from_fn to map the sampled
                // Vec into a fixed-size array.
                let elem_ty = elem.harness_type();
                quote! {
                    ::core::array::from_fn::<#elem_ty, #len, _>(|i| #harness_ident[i].clone())
                }
            }
            ParamShape::RefArray(elem, len) => {
                // `&[E; N]`: build the array, then borrow.
                let elem_ty = elem.harness_type();
                quote! {
                    &::core::array::from_fn::<#elem_ty, #len, _>(|i| #harness_ident[i].clone())
                }
            }
            ParamShape::OwnedOption(_) => quote! { #harness_ident.clone() },
            ParamShape::OwnedHashMap(_, _) => quote! { #harness_ident.clone() },
            ParamShape::OwnedHashSet(_) => quote! { #harness_ident.clone() },
            ParamShape::OwnedMultiset(_) => quote! {
                ::vstd::contrib::exec_spec::ExecMultiset { m: #harness_ident.clone() }
            },
            // The user's exec fn takes their OWN type (`&User` / `User`).
            ParamShape::RefUserType(_) => quote! { &#harness_ident },
            ParamShape::OwnedUserType(_) => quote! { #harness_ident.clone() },
            ParamShape::RefStr => quote! { #harness_ident.as_str() },
            ParamShape::OwnedString => quote! { #harness_ident.clone() },
            // `&mut <inner>` is passed as a mutable borrow of the harness
            // binding. The call mutates `<id>` in place; the post-state
            // deep_view is computed *after* the call from the same binding.
            ParamShape::MutRef(_) => quote! { &mut #harness_ident },
        }
    }

    /// Emit a pre-call `let` binding for shapes that need to materialize a
    /// non-temporary so the borrow can outlive the call. Returns
    /// `(prebound_ident, let_stmt)` if a pre-binding is needed; the harness
    /// uses `prebound_ident` as the call argument in place of the
    /// `arg_for_real_call` form.
    ///
    /// Currently used for fixed-size arrays: building `[T; N]` via
    /// `array::from_fn` returns a temporary, and `&[T; N]` parameters need
    /// the array to live across the call.
    fn pre_call_binding(&self, harness_ident: &Ident) -> Option<(Ident, TokenStream2)> {
        match self {
            ParamShape::OwnedArray(elem, len) | ParamShape::RefArray(elem, len) => {
                let elem_ty = elem.harness_type();
                let bound = format_ident!("__pbt_arr_{}", harness_ident);
                let stmt = quote! {
                    let #bound: [#elem_ty; #len] =
                        ::core::array::from_fn(|i| #harness_ident[i].clone());
                };
                Some((bound, stmt))
            }
            ParamShape::MutRef(inner) => inner.pre_call_binding(harness_ident),
            _ => None,
        }
    }

    /// Like `arg_for_real_call`, but uses a pre-bound name when one was
    /// produced by `pre_call_binding`.
    fn arg_with_optional_prebinding(
        &self,
        harness_ident: &Ident,
        prebound: Option<&Ident>,
    ) -> TokenStream2 {
        match (self, prebound) {
            (ParamShape::OwnedArray(_, _), Some(b)) => quote! { #b },
            (ParamShape::RefArray(_, _), Some(b)) => quote! { &#b },
            _ => self.arg_for_real_call(harness_ident),
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
            ParamShape::OwnedArray(_, _) | ParamShape::RefArray(_, _) => {
                // Treat the sampled `Vec<E>` as a slice for the `Exec*`
                // companion's purposes; this matches how `&[E]` deep_view
                // is dispatched.
                quote! { #harness_ident.as_slice() }
            }
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
            ParamShape::RefStr | ParamShape::OwnedString => {
                // Lower the spec view `s@: Seq<char>` to a runtime
                // `Vec<char>` via `__pbt_str_chars`, then take a slice. We
                // call the runtime helper (rather than emitting a block) to
                // keep the rewritten clause a flat call expression — block
                // syntax `{ ... }` trips proptest's format-string scanner
                // inside `prop_assert!`.
                quote! {
                    ::verus_pbt_runtime::__pbt_str_chars(&#harness_ident).as_slice()
                }
            }
            // For `&mut <inner>`, the *post-call* deep_view is the inner
            // shape's normal call form. The pre-call view is computed
            // separately and stashed in `pre_view_for` keyed on the ident.
            ParamShape::MutRef(inner) => inner.call_form_for_deep_view(harness_ident),
        }
    }

    /// For `&mut`-receiving shapes, build a *value* (cloned where
    /// necessary) that captures the pre-call deep_view of `harness_ident`.
    /// The snapshot is stored in a local before the call so that
    /// `old(<id>)@` rewrites in the contract resolve to it. Returns `None`
    /// for non-mut shapes — they don't need a separate pre-state because
    /// the post-call value is the same as the pre-call value.
    ///
    /// The snapshot deliberately materializes an OWNED value (not a
    /// borrow), so that mutation through the `&mut` arg doesn't invalidate
    /// it. For `OwnedVec`/`OwnedHashMap`/`OwnedHashSet`/`OwnedString`/
    /// `OwnedOption`/`OwnedUserType` the harness binding already holds an
    /// owned value, so a `.clone()` is sufficient. The snapshot is
    /// returned in the form expected by `call_form_for_deep_view` (e.g.
    /// `slice` for `OwnedVec`) so the rewriter can substitute it
    /// pointwise wherever `<id>@` would have appeared.
    fn pre_call_view_snapshot(&self, harness_ident: &Ident) -> Option<TokenStream2> {
        let inner = match self {
            ParamShape::MutRef(inner) => inner,
            _ => return None,
        };
        // For each owned shape, we just clone the harness binding into a
        // snapshot ident; the deep_view path then reads from the snapshot.
        // The actual snapshot value is stored in a local named
        // `__pbt_pre_<id>` and returned here as the deep_view form for
        // the contract rewriter.
        let snap = format_ident!("__pbt_pre_{}", harness_ident);
        match inner.as_ref() {
            ParamShape::OwnedVec(_) => Some(quote! { #snap.as_slice() }),
            ParamShape::OwnedString => Some(quote! {
                ::verus_pbt_runtime::__pbt_str_chars(&#snap).as_slice()
            }),
            ParamShape::OwnedOption(_)
            | ParamShape::OwnedHashMap(_, _)
            | ParamShape::OwnedHashSet(_)
            | ParamShape::OwnedUserType(_) => Some(quote! { &#snap }),
            ParamShape::Primitive(_) => Some(quote! { #snap }),
            _ => None,
        }
    }

    /// Emit the `let __pbt_pre_<id> = ...;` statement that captures the
    /// pre-call value of a `&mut`-shaped param. Paired with
    /// `pre_call_view_snapshot`. Returns `None` for non-mut shapes.
    fn pre_state_let(&self, harness_ident: &Ident) -> Option<TokenStream2> {
        let _inner = match self {
            ParamShape::MutRef(inner) => inner,
            _ => return None,
        };
        let snap = format_ident!("__pbt_pre_{}", harness_ident);
        // A blanket clone covers all the shapes we currently support
        // (Owned*, String, primitive). Non-Clone shapes wouldn't be
        // routed here because emit_harness rejects them.
        Some(quote! {
            let #snap = #harness_ident.clone();
        })
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
            ParamShape::OwnedArray(e, _) | ParamShape::RefArray(e, _) => {
                // Spec view of `[E; N]` is a `Seq<E>`; the engine treats it
                // identically to a slice for the purpose of contract
                // companions.
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
            ParamShape::RefStr | ParamShape::OwnedString => {
                // Spec view of a string is a `Seq<char>`; the engine
                // recognises it identically to a slice of `char`.
                quote! { Seq<char> }
            }
            ParamShape::MutRef(inner) => inner.spec_type(),
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
        // `[E; N]` by value.
        Type::Array(arr) => {
            let elem = classify_param_elem(&arr.elem, user_types)?;
            return Ok(ParamShape::OwnedArray(elem, arr.len.clone()));
        }
        Type::Reference(type_ref) => {
            let is_mut = type_ref.mutability.is_some();
            // `&mut [E]`: structurally PBT can't easily diff slice elements
            // because the call could return a sub-slice mutated in place
            // and we have no way to compute "what was". Reject with a
            // clean diagnostic.
            if is_mut {
                if let Type::Slice(_) = type_ref.elem.as_ref() {
                    return Err(Error::new_spanned(
                        ty,
                        "verus_pbt: `&mut [E]` parameters are not supported. Pass the data \
by value (`Vec<E>`, `&mut Vec<E>`) so the harness can snapshot it.",
                    ));
                }
                if let Type::Path(tp) = type_ref.elem.as_ref() {
                    if tp.qself.is_none() && tp.path.segments.len() == 1 {
                        let name = tp.path.segments[0].ident.to_string();
                        if name == "str" {
                            return Err(Error::new_spanned(
                                ty,
                                "verus_pbt: `&mut str` parameters are not supported. \
Pass the data by `&mut String` so the harness can snapshot it.",
                            ));
                        }
                    }
                }
                // Recurse on the inner without the `mut` to get the inner
                // shape, then wrap in MutRef. We synthesize a non-mut
                // reference type wrapper so the inner classification
                // doesn't itself need to know about mutability — except
                // we don't actually want a reference wrap, we want the
                // OWNED form. For `&mut Vec<T>`, the harness samples a
                // `Vec<T>` and passes `&mut <id>`. So drop the reference
                // and reclassify the inner as the owned shape.
                let inner_owned: Type = (*type_ref.elem).clone();
                let inner_shape = classify_param_type(&inner_owned, user_types)?;
                // Disallow nested mut-refs and other forms that don't
                // round-trip via clone+snapshot.
                match &inner_shape {
                    ParamShape::OwnedVec(_)
                    | ParamShape::OwnedHashMap(_, _)
                    | ParamShape::OwnedHashSet(_)
                    | ParamShape::OwnedString
                    | ParamShape::OwnedOption(_)
                    | ParamShape::OwnedUserType(_)
                    | ParamShape::Primitive(_) => {}
                    _ => {
                        return Err(Error::new_spanned(
                            ty,
                            "verus_pbt: `&mut <T>` is supported for owned shapes \
(Vec, HashMap, HashSet, String, Option, user type, primitive). The inner type \
here doesn't fit; pass an owned form instead.",
                        ));
                    }
                }
                return Ok(ParamShape::MutRef(Box::new(inner_shape)));
            }
            // `&[E]`
            if let Type::Slice(slice) = type_ref.elem.as_ref() {
                let elem = classify_param_elem(&slice.elem, user_types)?;
                return Ok(ParamShape::Slice(elem));
            }
            // `&[E; N]` — fixed-size array reference.
            if let Type::Array(arr) = type_ref.elem.as_ref() {
                let elem = classify_param_elem(&arr.elem, user_types)?;
                return Ok(ParamShape::RefArray(elem, arr.len.clone()));
            }
            // `&str` — string slice. Classify here BEFORE the user-type
            // path, since `str` isn't a user type and isn't capitalized.
            if let Type::Path(tp) = type_ref.elem.as_ref() {
                if tp.qself.is_none() && tp.path.segments.len() == 1 {
                    let seg = &tp.path.segments[0];
                    let name = seg.ident.to_string();
                    if name == "str" && matches!(seg.arguments, PathArguments::None) {
                        return Ok(ParamShape::RefStr);
                    }
                }
            }
            // `&UserType` or `&ExecUserType` (no generic args).
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
                 `&UserType`. For `&Container<E>` (e.g. `&Vec<T>`, `&Option<T>`), supply \
                 the parameter by value (`Container<E>`) at the harness layer; the \
                 trusted body can still borrow internally.",
            ))
        }
        Type::Path(tp) if tp.qself.is_none() && !tp.path.segments.is_empty() => {
            let seg = tp.path.segments.last().unwrap();
            let name = seg.ident.to_string();
            let is_single_seg = tp.path.segments.len() == 1;
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
                "String" if is_single_seg => Ok(ParamShape::OwnedString),
                _ => {
                    if is_single_seg && user_types.contains(&name)
                        && matches!(seg.arguments, PathArguments::None)
                    {
                        return Ok(ParamShape::OwnedUserType(seg.ident.clone()));
                    }
                    if is_single_seg {
                        if let Some(stripped) = strip_exec_prefix(&name, user_types) {
                            if matches!(seg.arguments, PathArguments::None) {
                                return Ok(ParamShape::OwnedUserType(Ident::new(
                                    stripped,
                                    seg.ident.span(),
                                )));
                            }
                        }
                    }
                    if is_single_seg && is_primitive_like(&name) {
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
            // Verus spec integer types — `nat` (non-negative ghost) and
            // `int` (unbounded ghost). At PBT time we lower them to runtime
            // counterparts (u64 / i128) so contracts written in spec
            // arithmetic compile.
            | "nat"
            | "int"
    )
}

#[derive(Clone, Debug)]
enum ReturnShape {
    Unit,
    Primitive,
    OwnedVec(ParamElem),
    /// `[T; N]` returned by value. The const length is retained for
    /// symmetry with `OwnedArray` on the param side; current emission only
    /// reads the element shape.
    #[allow(dead_code)]
    OwnedArray(ParamElem, Expr),
    OwnedOption(ParamElem),
    OwnedHashMap,
    OwnedHashSet,
    OwnedMultiset,
    OwnedUserType(Ident),
    /// `&T` where `T: Copy` (or known primitive). The harness adapts by
    /// dereferencing the result before checking the contract.
    RefPrimitive(Type),
    /// `&[T]`. The harness adapts by cloning to `Vec<T>` for `deep_view`
    /// purposes.
    RefSlice(ParamElem),
    /// `&[T; N]`. Same engine treatment as `RefSlice`. The const length is
    /// retained on the variant for symmetry with `OwnedArray` and so future
    /// emission paths (e.g. fixed-length contract folding) can read it.
    #[allow(dead_code)]
    RefArray(ParamElem, Expr),
    /// `&UserType`. Same engine treatment as `OwnedUserType` once
    /// dereferenced.
    RefUserType(Ident),
    /// `&str`. Lowered to `Seq<char>` for contract evaluation.
    RefStr,
    /// `String`. Same as `RefStr` for contract purposes; harness binds the
    /// returned `String` and converts to chars on demand.
    OwnedString,
}

fn classify_return(
    ret: &ReturnType,
    user_types: &HashSet<String>,
    self_ty_for_method: Option<&Ident>,
) -> Result<ReturnShape, Error> {
    let ty = match ret {
        ReturnType::Default => return Ok(ReturnShape::Unit),
        ReturnType::Type(_, _, _, ty) => ty,
    };
    // Substitute `Self` (capital-S identifier or `Self::...` path) with the
    // concrete impl's Self type before classification. This is what lets a
    // method written as `fn make() -> Self` be sampled and converted as the
    // user type.
    let mut owner;
    let ty_ref: &Type = if let Some(self_ty) = self_ty_for_method {
        owner = (**ty).clone();
        replace_self_ty(&mut owner, self_ty);
        &owner
    } else {
        ty.as_ref()
    };
    match ty_ref {
        // `[E; N]` by value.
        Type::Array(arr) => {
            let elem = classify_param_elem(&arr.elem, user_types)?;
            return Ok(ReturnShape::OwnedArray(elem, arr.len.clone()));
        }
        Type::Reference(type_ref) => {
            // `&[T]`
            if let Type::Slice(slice) = type_ref.elem.as_ref() {
                let elem = classify_param_elem(&slice.elem, user_types)?;
                return Ok(ReturnShape::RefSlice(elem));
            }
            // `&[T; N]`
            if let Type::Array(arr) = type_ref.elem.as_ref() {
                let elem = classify_param_elem(&arr.elem, user_types)?;
                return Ok(ReturnShape::RefArray(elem, arr.len.clone()));
            }
            // `&str`
            if let Type::Path(tp) = type_ref.elem.as_ref() {
                if tp.qself.is_none() && tp.path.segments.len() == 1 {
                    let seg = &tp.path.segments[0];
                    let name = seg.ident.to_string();
                    if name == "str" && matches!(seg.arguments, PathArguments::None) {
                        return Ok(ReturnShape::RefStr);
                    }
                }
            }
            // `&Path`
            if let Type::Path(tp) = type_ref.elem.as_ref() {
                if tp.qself.is_none() && tp.path.segments.len() == 1 {
                    let seg = &tp.path.segments[0];
                    let name = seg.ident.to_string();
                    if user_types.contains(&name)
                        && matches!(seg.arguments, PathArguments::None)
                    {
                        return Ok(ReturnShape::RefUserType(seg.ident.clone()));
                    }
                    if is_primitive_like(&name) {
                        return Ok(ReturnShape::RefPrimitive((*type_ref.elem).clone()));
                    }
                    if name.chars().next().is_some_and(|c| c.is_uppercase()) {
                        return Ok(ReturnShape::RefUserType(seg.ident.clone()));
                    }
                }
            }
            Err(Error::new_spanned(
                ty,
                "verus_pbt: unsupported reference return type. Supported: \
`&T` for primitives, `&[T]`, and `&UserType`.",
            ))
        }
        Type::Path(tp) if tp.qself.is_none() && !tp.path.segments.is_empty() => {
            // Use the LAST segment as the type's name. This lets us handle
            // both bare `Vec<T>` and qualified `alloc::vec::Vec<T>` /
            // `std::collections::HashMap<K, V>` / etc. — common in vstd code.
            let seg = tp.path.segments.last().unwrap();
            let name = seg.ident.to_string();
            // Single-segment paths can be user types; multi-segment paths
            // can't (we'd need full path resolution to map them).
            let is_single_seg = tp.path.segments.len() == 1;
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
                "String" if is_single_seg => Ok(ReturnShape::OwnedString),
                _ => {
                    if is_single_seg && user_types.contains(&name) {
                        Ok(ReturnShape::OwnedUserType(seg.ident.clone()))
                    } else if is_single_seg && is_primitive_like(&name) {
                        Ok(ReturnShape::Primitive)
                    } else if is_single_seg
                        && name.chars().next().is_some_and(|c| c.is_uppercase())
                    {
                        // External user type (defined + `#[pbt_provide]`'d in
                        // another module). Same trait-resolved treatment as
                        // a user type.
                        Ok(ReturnShape::OwnedUserType(seg.ident.clone()))
                    } else {
                        Err(Error::new_spanned(
                            ty,
                            format!(
                                "verus_pbt: unsupported return type `{}`. Supported: \
primitives, `Vec<E>`, `Option<E>`, `HashMap<K, V>`, `HashSet<E>`, `Multiset<E>`, \
and user-defined types (including `Self` inside an impl).",
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
            "verus_pbt: unsupported return type. Supported: primitives, `Vec<E>`, \
`Option<E>`, `HashMap<K, V>`, `HashSet<E>`, `Multiset<E>`, and user-defined types \
(including `Self` inside an impl).",
        )),
    }
}

/// Replace every occurrence of the `Self` type (in `Type::Path`s) with the
/// concrete impl Self type. Recurses into generic arguments, references,
/// slices, and tuples.
fn replace_self_ty(ty: &mut Type, self_ty: &Ident) {
    use verus_syn::visit_mut::{self, VisitMut};
    struct R<'a> {
        self_ty: &'a Ident,
    }
    impl<'a> VisitMut for R<'a> {
        fn visit_type_path_mut(&mut self, tp: &mut verus_syn::TypePath) {
            // Replace a leading `Self` segment in a non-qualified path with the
            // concrete type (works for `Self`, `Self::Item`, etc.).
            if tp.qself.is_none() && !tp.path.segments.is_empty() {
                if tp.path.segments[0].ident == "Self" {
                    let span = tp.path.segments[0].ident.span();
                    tp.path.segments[0].ident = Ident::new(&self.self_ty.to_string(), span);
                }
            }
            visit_mut::visit_type_path_mut(self, tp);
        }
    }
    let mut r = R { self_ty };
    r.visit_type_mut(ty);
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
    /// For `&mut`-shaped params this is the *post-call* view (after the
    /// real fn returns); the pre-call view is in `pre_view_for`.
    param_call_form: &'a HashMap<String, TokenStream2>,
    /// Per parameter: how `old(<param>).deep_view()` translates. Only
    /// populated for `&mut` params; for normal params the pre-state and
    /// post-state are the same, so `old(<id>)` is treated as `<id>` at
    /// the rewriter level.
    pre_view_for: &'a HashMap<String, TokenStream2>,
    /// Idents whose value is a user-defined type at the harness level (the
    /// user's OWN type, e.g. `User`). Maps ident-name → user type name. Used
    /// to insert `__pbt_to_exec_T(&x)` conversions before spec-fn / spec-
    /// method calls that expect the engine `Exec*` form.
    user_typed_idents: &'a HashMap<String, Ident>,
    /// `runtime fn name → spec fn name` redirect for
    /// `#[verifier::when_used_as_spec(...)]`. When rewriting `f(args)` in a
    /// contract, we redirect to `exec_<spec_name>(args)` instead of
    /// `exec_<f>(args)` if `f` is in this map.
    when_used_as_spec_redirect: &'a HashMap<String, String>,
    return_ident: Option<Ident>,
    return_shape: ReturnShape,
}

impl<'a> VisitMut for ContractRewriter<'a> {
    fn visit_expr_mut(&mut self, expr: &mut Expr) {
        // Pre-recurse normalization of two-state markers.
        //
        // `final(<x>)` parses as `Expr::Final(ExprFinal { arg: <x> })` —
        // it represents the post-call value of `x`, which is what bare
        // `<x>` already means in our rewrite scheme. Strip the marker.
        //
        // `old(<x>)` parses as `Expr::Call(old, [<x>])` (no dedicated
        // verus_syn variant; `old` is a regular fn-name). Replace with a
        // synthetic ident `__pbt_pre_<x>` that the deep_view rewrite will
        // resolve via `pre_view_for`.
        if let Expr::Final(f) = expr {
            let inner = (*f.arg).clone();
            *expr = inner;
        }
        if let Expr::Call(call) = expr {
            if let Expr::Path(ExprPath { path, qself: None, .. }) = call.func.as_ref() {
                if path.leading_colon.is_none()
                    && path.segments.len() == 1
                    && path.segments[0].ident == "old"
                    && call.args.len() == 1
                {
                    if let Some(name) = ident_of_expr(&call.args[0]) {
                        if self.pre_view_for.contains_key(&name) {
                            // Replace `old(<x>)` with the synthetic ident
                            // `__pbt_pre_<x>`; the deep_view rewriter
                            // below picks this up via the `pre_view_for`
                            // mapping (registered at the same key as
                            // `param_call_form`).
                            let synth: Ident =
                                format_ident!("__pbt_pre_{}", name);
                            *expr = verus_syn::parse_quote! { #synth };
                        }
                    }
                }
            }
        }

        // Recurse first so nested rewrites land before parent rewrites.
        verus_syn::visit_mut::visit_expr_mut(self, expr);

        // 0a. Verus spec-integer casts: `x as nat` / `x as int` are spec-
        // only conversions that have no runtime counterpart. Lower them to
        // the runtime counterparts the engine uses for those types
        // (`nat` → `u64`, `int` → `i128`). The harness then operates on
        // primitive integers for arithmetic.
        if let Expr::Cast(cast) = expr {
            if let Type::Path(tp) = cast.ty.as_ref() {
                if tp.qself.is_none()
                    && tp.path.leading_colon.is_none()
                    && tp.path.segments.len() == 1
                {
                    let target = tp.path.segments[0].ident.to_string();
                    if target == "nat" || target == "int" {
                        let runtime: TokenStream2 = if target == "nat" {
                            quote! { u64 }
                        } else {
                            quote! { i128 }
                        };
                        let inner = (*cast.expr).clone();
                        *expr = verus_syn::parse_quote! { (#inner as #runtime) };
                        return;
                    }
                }
            }
        }

        // 0. Verus-style chained comparisons: `a <= b <= c` parses in
        // verus_syn as `(a <= b) <= c`. In Verus this is meaningful; in plain
        // Rust it's a type error. Rewrite to `(a <= b) && (b <= c)` when we
        // detect the shape.
        if let Some(rewritten) = rewrite_chained_compare(expr) {
            *expr = rewritten;
            return;
        }

        // 1. Strip `<expr>.deep_view()` or `<expr>@` (Verus's `View`-postfix
        // shorthand). Both denote the same spec view: in Verus, `s@` parses
        // as `Expr::View { expr: s }` and is semantically equivalent to
        // `s.deep_view()` for the purpose of contract evaluation. Treat them
        // identically in the harness rewriter. Also handle the explicit
        // `<expr>.view()` form (used in vstd as a longhand for `s@`).
        let view_receiver: Option<Expr> = match expr {
            Expr::MethodCall(ExprMethodCall { receiver, method, args, .. })
                if (method == "deep_view" || method == "view") && args.is_empty() =>
            {
                Some((**receiver).clone())
            }
            Expr::View(v) => Some((*v.expr).clone()),
            _ => None,
        };
        if let Some(receiver_clone) = view_receiver {
            // Return-named ident: re-shape per ReturnShape.
            if let Some(ret_ident) = &self.return_ident {
                if expr_is_ident(&receiver_clone, ret_ident) {
                    *expr = self.rewrite_return_deep_view(ret_ident.clone());
                    return;
                }
            }

            // Parameter ident: substitute the registered call form.
            if let Some(name) = ident_of_expr(&receiver_clone) {
                // First check the pre-state map for `__pbt_pre_<id>`
                // synthetic idents (introduced by the `old(...)`
                // normalization step above). The pre-state form is
                // already a deep_view-shaped expression — substitute it
                // directly without going through `param_call_form`.
                if let Some(stripped) = name.strip_prefix("__pbt_pre_") {
                    if let Some(pre) = self.pre_view_for.get(stripped) {
                        let p = pre.clone();
                        *expr = verus_syn::parse_quote!( #p );
                        return;
                    }
                }
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

        // 2. Rename `f(args)` to `exec_f(args)` when `f` is a known spec fn,
        // or to `exec_<spec_X>(args)` when `f` has `when_used_as_spec(spec_X)`.
        // If an argument is a bare user-typed ident, insert the conversion.
        if let Expr::Call(call) = expr {
            if let Expr::Path(ExprPath { path, qself: None, .. }) = call.func.as_mut() {
                if path.segments.len() == 1 {
                    let seg = &mut path.segments[0];
                    let name = seg.ident.to_string();
                    let target_name: Option<String> = if let Some(redirected) =
                        self.when_used_as_spec_redirect.get(&name)
                    {
                        Some(redirected.clone())
                    } else if self.spec_fn_names.contains(&name) {
                        Some(name.clone())
                    } else {
                        None
                    };
                    if let Some(t) = target_name {
                        seg.ident = format_ident!("exec_{}", t);
                        // Convert any bare user-typed argument: `f(u)` where
                        // `u: User` → `exec_f(&__pbt_to_exec_User(&u))`.
                        for arg in call.args.iter_mut() {
                            self.convert_user_arg(arg);
                        }
                    }
                }
            }
        }

        // 2b. Lower `Seq`-style method calls that appear directly in the
        // harness (e.g. inside an `ensures` clause). The engine handles
        // these inside its own block, but contract clauses are rewritten by
        // this visitor and end up in the harness's `prop_assert!` — so we
        // need a slice-shape lowering. Patterns:
        //   <slice>.index(i as int)      → <slice>[i as usize]
        //   <slice>.subrange(i, j)       → &<slice>[i as usize..j as usize]
        //   <slice>.update(i, v)         → { let mut __t = <slice>.to_vec(); __t[i as usize] = v; __t }
        //   <slice>.len()                → <slice>.len()  (already valid)
        if let Expr::MethodCall(mc) = expr {
            let method = mc.method.to_string();
            let receiver = (*mc.receiver).clone();
            match method.as_str() {
                "index" if mc.args.len() == 1 => {
                    let idx = mc.args.first().unwrap().clone();
                    let new: Expr = verus_syn::parse_quote! {
                        (#receiver)[(#idx) as usize]
                    };
                    *expr = new;
                    return;
                }
                "subrange" if mc.args.len() == 2 => {
                    let i = mc.args[0].clone();
                    let j = mc.args[1].clone();
                    let new: Expr = verus_syn::parse_quote! {
                        &(#receiver)[(#i) as usize..(#j) as usize]
                    };
                    *expr = new;
                    return;
                }
                "update" if mc.args.len() == 2 => {
                    let i = mc.args[0].clone();
                    let v = mc.args[1].clone();
                    // Lower to a call into the harness's `__pbt_seq_update`
                    // helper. Calling a fn keeps the expression flat — block
                    // / closure syntax in prop_assert! tripped its
                    // format-string parser.
                    let new: Expr = verus_syn::parse_quote! {
                        ::verus_pbt_runtime::__pbt_seq_update((#receiver).to_vec(), (#i) as usize, #v)
                    };
                    *expr = new;
                    return;
                }
                "push" if mc.args.len() == 1 => {
                    // `<slice>.push(x)` is Verus's `Seq::push`, which
                    // returns a new sequence with `x` appended. Lower
                    // through `__pbt_seq_push` to keep the expression
                    // flat (block syntax trips prop_assert!).
                    let v = mc.args[0].clone();
                    let new: Expr = verus_syn::parse_quote! {
                        ::verus_pbt_runtime::__pbt_seq_push((#receiver).to_vec(), #v)
                    };
                    *expr = new;
                    return;
                }
                "add" if mc.args.len() == 1 => {
                    // `<slice>.add(<other>)` is Verus's `Seq::add` (the
                    // method form of `Seq + Seq`). Lower the same way as
                    // the binary `+` form.
                    let other = mc.args[0].clone();
                    let new: Expr = verus_syn::parse_quote! {
                        ::verus_pbt_runtime::__pbt_seq_concat(#receiver, #other).as_slice()
                    };
                    *expr = new;
                    return;
                }
                _ => {}
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
                    let exec_name = self
                        .when_used_as_spec_redirect
                        .get(&name)
                        .cloned()
                        .unwrap_or_else(|| name.clone());
                    mc.method = format_ident!("exec_{}", exec_name);
                    let recv_name = ident_of_expr(&mc.receiver).unwrap();
                    let recv_id = format_ident!("{}", recv_name);
                    let new_recv: Expr = verus_syn::parse_quote! {
                        <#user_ty as ::verus_pbt_runtime::ToExecModel>::to_exec_model(&#recv_id)
                    };
                    *mc.receiver = new_recv;
                }
            } else if let Some(redirected) = self.when_used_as_spec_redirect.get(&name) {
                // Method-style runtime call with a `when_used_as_spec` redirect:
                // call the spec companion directly.
                mc.method = format_ident!("exec_{}", redirected);
            } else if self.spec_fn_names.contains(&name) {
                // Receiver isn't a tracked user-typed ident, but the method is
                // a known in-block spec fn (e.g. chained `x.perm.is_revoked()`
                // where `x.perm` is already an Exec value): just rename.
                mc.method = format_ident!("exec_{}", mc.method);
            }
        }

        // 4. Sequence concat: `<lhs>.as_slice() + <rhs>.as_slice()` arises
        // when contract clauses write `a@ + b@` (Verus's `Seq::add` / `+`).
        // Plain Rust slices don't support `+`, so route through the runtime
        // helper. Detection is post-rewrite: by the time we see the parent
        // `BinOp::Add`, both children have already been lowered to slice
        // form by the deep_view substitution above.
        if let Expr::Binary(b) = expr {
            if matches!(b.op, verus_syn::BinOp::Add(..))
                && expr_is_slice_call(&b.left)
                && expr_is_slice_call(&b.right)
            {
                let l = (*b.left).clone();
                let r = (*b.right).clone();
                *expr = verus_syn::parse_quote! {
                    ::verus_pbt_runtime::__pbt_seq_concat(#l, #r).as_slice()
                };
                return;
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
            ReturnShape::OwnedArray(_, _) => {
                // Returned `[E; N]` is already array-shaped; `as_slice()`
                // converts to `&[E]` for the engine's `Seq<E>` treatment.
                verus_syn::parse_quote_spanned! { ret_ident.span() => #ret_ident.as_slice() }
            }
            ReturnShape::RefSlice(_) | ReturnShape::RefArray(_, _) => {
                // `&[T]` / `&[T; N]` are already slice-shaped.
                verus_syn::parse_quote_spanned! { ret_ident.span() => #ret_ident }
            }
            ReturnShape::OwnedUserType(_)
            | ReturnShape::OwnedOption(_)
            | ReturnShape::OwnedHashMap
            | ReturnShape::OwnedHashSet
            | ReturnShape::OwnedMultiset => {
                verus_syn::parse_quote_spanned! { ret_ident.span() => &#ret_ident }
            }
            ReturnShape::RefUserType(_) => {
                // Already a reference; pass through.
                verus_syn::parse_quote_spanned! { ret_ident.span() => #ret_ident }
            }
            ReturnShape::RefPrimitive(_) => {
                // `&T` where `T: Copy`: dereference for value comparisons.
                verus_syn::parse_quote_spanned! { ret_ident.span() => *#ret_ident }
            }
            ReturnShape::RefStr | ReturnShape::OwnedString => {
                // `&str` / `String`: collect chars via the runtime helper
                // (a free fn, not a block expression) so the rewritten
                // clause is a flat call. Block syntax `{ ... }` trips
                // proptest's format-string scanner inside prop_assert!.
                let receiver: Expr = match &self.return_shape {
                    ReturnShape::RefStr => verus_syn::parse_quote_spanned! {
                        ret_ident.span() => &#ret_ident
                    },
                    _ => verus_syn::parse_quote_spanned! {
                        ret_ident.span() => &#ret_ident[..]
                    },
                };
                verus_syn::parse_quote_spanned! { ret_ident.span() =>
                    ::verus_pbt_runtime::__pbt_str_chars(#receiver).as_slice()
                }
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
///
/// Also handles longer chains: `0 <= i <= j <= s.len()` parses as
/// `(((0 <= i) <= j) <= s.len())`. After the inner `(0 <= i) <= j` rewrites
/// to `(0 <= i) && (i <= j)`, the outer `<expr> <= s.len()` needs to grab
/// the rightmost-comparison-RHS (`j` here) as the new chain pivot.
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

    /// Recover the chain pivot from a left-side expression that may already
    /// have been rewritten to `<...> && (a OP b)` form. Returns `b` for
    /// the trailing comparison.
    fn rightmost_compare_rhs(e: &Expr) -> Option<Expr> {
        match e {
            Expr::Binary(b) if is_comparison(&b.op) => Some((*b.right).clone()),
            Expr::Binary(b) if matches!(b.op, BinOp::And(_)) => {
                // After a previous chain rewrite the right side is a
                // comparison.
                rightmost_compare_rhs(&b.right)
            }
            Expr::Paren(p) => rightmost_compare_rhs(&p.expr),
            _ => None,
        }
    }

    let outer = match expr {
        Expr::Binary(b) if is_comparison(&b.op) => b,
        _ => return None,
    };

    // Standard 2-level case: inner is a comparison.
    if let Expr::Binary(inner) = outer.left.as_ref() {
        if is_comparison(&inner.op) {
            let inner_b: Expr = (*inner.right).clone();
            let outer_left: Expr = (*outer.left).clone();
            let op2 = outer.op.clone();
            let outer_right: Expr = (*outer.right).clone();
            let new_right: Expr =
                verus_syn::parse_quote! { #inner_b #op2 #outer_right };
            return Some(verus_syn::parse_quote! { (#outer_left) && (#new_right) });
        }
    }

    // Longer chain case: the left side has already been rewritten to a
    // conjunction, e.g. `(0 <= i) && (i <= j)`. Walk to the rightmost
    // comparison RHS to use as the new chain pivot.
    if let Some(pivot) = rightmost_compare_rhs(&outer.left) {
        let outer_left: Expr = (*outer.left).clone();
        let op2 = outer.op.clone();
        let outer_right: Expr = (*outer.right).clone();
        let new_right: Expr = verus_syn::parse_quote! { #pivot #op2 #outer_right };
        return Some(verus_syn::parse_quote! { (#outer_left) && (#new_right) });
    }

    None
}

/// True if `expr` is `<receiver>.as_slice()` (no args). Used by the contract
/// rewriter to detect that an operand has already been lowered to a slice
/// form by a prior deep_view rewrite, so a parent `+` can route through
/// `__pbt_seq_concat` instead of relying on a non-existent `Add` impl on
/// raw slices.
fn expr_is_slice_call(expr: &Expr) -> bool {
    if let Expr::MethodCall(mc) = expr {
        return mc.method == "as_slice" && mc.args.is_empty();
    }
    false
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

/// Rewrite `int` / `nat` types appearing as quantifier-bound variable types
/// (in `forall`/`exists` closure params) to runtime equivalents (`i64`/`u64`).
/// The engine's `exec_spec` rejects spec-only `int`/`nat` for quantified vars,
/// so the lift pass needs to swap them before producing the synthetic spec
/// fn body. The rewrite is conservative — it only touches *closure
/// parameter* types, not arbitrary type positions, so spec-side semantics
/// (like `s.len()` returning `nat`) are preserved.
fn rewrite_int_nat_in_quantifiers(expr: &mut Expr) {
    struct R;
    impl VisitMut for R {
        fn visit_expr_closure_mut(&mut self, c: &mut verus_syn::ExprClosure) {
            for input in c.inputs.iter_mut() {
                rewrite_pat_int_nat(&mut input.pat);
            }
            verus_syn::visit_mut::visit_expr_closure_mut(self, c);
        }
    }
    fn rewrite_pat_int_nat(pat: &mut verus_syn::Pat) {
        if let verus_syn::Pat::Type(pt) = pat {
            replace_int_nat_in_type(&mut pt.ty);
        }
    }
    fn replace_int_nat_in_type(ty: &mut Type) {
        if let Type::Path(tp) = ty {
            if tp.qself.is_none() && tp.path.segments.len() == 1 {
                let name = tp.path.segments[0].ident.to_string();
                if name == "int" {
                    *ty = verus_syn::parse_quote! { i64 };
                    return;
                }
                if name == "nat" {
                    *ty = verus_syn::parse_quote! { u64 };
                    return;
                }
            }
        }
    }
    R.visit_expr_mut(expr);
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

    // Engine restriction: quantifier-bound variables must be a runtime
    // primitive int (`u32`, `i64`, etc.); `int` / `nat` are spec-only and
    // rejected. Rewrite the spec types to runtime equivalents (`int → i64`,
    // `nat → u64`) before lifting so contracts written in spec arithmetic
    // can still be PBT'd.
    let mut clause = clause.clone();
    rewrite_int_nat_in_quantifiers(&mut clause);

    let free = collect_free_idents(&clause, /*exclude_built_ins=*/ true);

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
    let body = clause.clone();
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
        ReturnShape::OwnedVec(e) | ReturnShape::RefSlice(e) => {
            let inner = match e {
                ParamElem::Primitive(t) => quote! { #t },
                ParamElem::UserType(n) => quote! { #n },
            };
            quote! { Seq<#inner> }
        }
        ReturnShape::OwnedArray(e, _) | ReturnShape::RefArray(e, _) => {
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
        ReturnShape::OwnedUserType(n) | ReturnShape::RefUserType(n) => quote! { #n },
        ReturnShape::RefPrimitive(t) => quote! { #t },
        ReturnShape::RefStr | ReturnShape::OwnedString => quote! { Seq<char> },
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

/// If `ty` is a single-segment path with a recognized ghost/permission wrapper
/// name (`Tracked`, `Ghost`, `Proof`), return the wrapper name so the harness
/// can refuse this parameter with an actionable error.
fn ghost_wrapper_name(ty: &Type) -> Option<&'static str> {
    let tp = match ty {
        Type::Path(tp) if tp.qself.is_none() => tp,
        // `&Tracked<...>` / `&mut Tracked<...>` etc.
        Type::Reference(r) => return ghost_wrapper_name(&r.elem),
        _ => return None,
    };
    if tp.path.segments.is_empty() {
        return None;
    }
    let seg = tp.path.segments.last().unwrap();
    match seg.ident.to_string().as_str() {
        "Tracked" => Some("Tracked"),
        "Ghost" => Some("Ghost"),
        "Proof" => Some("Proof"),
        _ => None,
    }
}

/// For a `ParamShape::OwnedVec(elem)` or `ParamShape::Slice(elem)`, build a
/// proptest element strategy producing the element type the harness samples
/// (the user's type for user-defined elements). Returns None for shapes that
/// aren't sized by a `len()` precondition.
fn element_strategy_for_shape(shape: &ParamShape) -> Option<TokenStream2> {
    let elem = match shape {
        ParamShape::OwnedVec(e) | ParamShape::Slice(e) => e,
        ParamShape::OwnedArray(e, _) | ParamShape::RefArray(e, _) => e,
        _ => return None,
    };
    let elem_ty = match elem {
        ParamElem::Primitive(t) => quote! { #t },
        ParamElem::UserType(n) => quote! { #n },
    };
    Some(quote! { <#elem_ty as ::verus_pbt_runtime::PbtStrategy>::pbt_strategy() })
}

/// Scan a function's `requires` clauses for patterns of the shape
/// `<param>@.len() == <const>` (and the equivalent `<param>.deep_view().len()
/// == <const>`), returning a map from parameter name to the required length.
/// Handles either side of `==`. Used to pre-size collection strategies in the
/// harness so `prop_assume!` doesn't reject most samples.
fn scan_fixed_length_constraints(sig: &verus_syn::Signature) -> HashMap<String, usize> {
    use verus_syn::{BinOp, ExprBinary, ExprLit, Lit};
    let mut out: HashMap<String, usize> = HashMap::new();
    let Some(req) = &sig.spec.requires else {
        return out;
    };

    // Match `<param>@.len()` or `<param>.deep_view().len()`, returning the
    // param name. Conservative: bare ident only (no field access, no chained
    // method calls).
    fn extract_param_len(expr: &Expr) -> Option<String> {
        // Outer must be `.len()` with no args.
        let Expr::MethodCall(mc) = expr else {
            return None;
        };
        if mc.method != "len" || !mc.args.is_empty() {
            return None;
        }
        // Inner must be either `s@` (Expr::View) or `s.deep_view()`.
        match mc.receiver.as_ref() {
            Expr::View(v) => ident_of_expr(&v.expr),
            Expr::MethodCall(inner)
                if inner.method == "deep_view" && inner.args.is_empty() =>
            {
                ident_of_expr(&inner.receiver)
            }
            _ => None,
        }
    }

    fn extract_usize_lit(expr: &Expr) -> Option<usize> {
        if let Expr::Lit(ExprLit { lit: Lit::Int(li), .. }) = expr {
            li.base10_parse::<usize>().ok()
        } else {
            None
        }
    }

    fn walk(e: &Expr, out: &mut HashMap<String, usize>) {
        match e {
            Expr::Binary(ExprBinary { op: BinOp::Eq(_), left, right, .. }) => {
                if let (Some(name), Some(n)) =
                    (extract_param_len(left), extract_usize_lit(right))
                {
                    out.entry(name).or_insert(n);
                }
                if let (Some(name), Some(n)) =
                    (extract_param_len(right), extract_usize_lit(left))
                {
                    out.entry(name).or_insert(n);
                }
            }
            Expr::Binary(ExprBinary { op: BinOp::And(_), left, right, .. }) => {
                walk(left, out);
                walk(right, out);
            }
            Expr::BigAnd(b) => {
                for inner in &b.exprs {
                    walk(&inner.expr, out);
                }
            }
            Expr::Paren(p) => walk(&p.expr, out),
            _ => {}
        }
    }

    for e in req.exprs.exprs.iter() {
        walk(e, &mut out);
    }
    out
}

/// Scan for usize-typed params whose precondition couples them to a
/// collection param's length: `i < s@.len()`, `i <= s@.len()`, etc.
/// Returns a map from the *index* param name to the maximum length the
/// strategy should sample. The "max length" comes from the engine's
/// collection bound (`DEFAULT_COLLECTION_MAX = 16`), so an index sampled
/// in `0..16` will satisfy `i < s.len()` for *some* sampled `s` — much
/// better than the default ~0% rate.
///
/// The bound is conservative: we sample the index up to the collection
/// max, then `prop_assume!` filters cases where the actually-sampled
/// collection happens to be shorter. Empirically this drops the reject rate
/// from ~100% to ~50% for the simple `i < s.len()` shape.
fn scan_index_bound_constraints(sig: &verus_syn::Signature) -> HashMap<String, usize> {
    use verus_syn::{BinOp, ExprBinary};
    let mut out: HashMap<String, usize> = HashMap::new();
    let Some(req) = &sig.spec.requires else {
        return out;
    };
    const DEFAULT_MAX: usize = 16;

    /// Returns the param name if `expr` is a bare ident (the index var).
    fn extract_param_name(expr: &Expr) -> Option<String> {
        ident_of_expr(expr)
    }

    /// Returns the unsigned integer value if `expr` is a literal integer
    /// (e.g. `4`, `4usize`). Used to recognise const-bound preconditions
    /// like `i < 4` for fixed-size array harnesses.
    fn extract_usize_literal(expr: &Expr) -> Option<usize> {
        if let Expr::Lit(verus_syn::ExprLit {
            lit: verus_syn::Lit::Int(li),
            ..
        }) = expr
        {
            return li.base10_parse::<usize>().ok();
        }
        None
    }

    /// True if `expr` is a `<x>@.len()` / `<x>.deep_view().len()` /
    /// `<x>.view().len()` / `<x>.len()` — anything that looks like a length
    /// call on a collection param.
    fn is_collection_len(expr: &Expr) -> bool {
        if let Expr::MethodCall(mc) = expr {
            if mc.method == "len" && mc.args.is_empty() {
                let receiver = mc.receiver.as_ref();
                if matches!(receiver, Expr::View(_)) {
                    return true;
                }
                if let Expr::MethodCall(inner) = receiver {
                    if (inner.method == "deep_view" || inner.method == "view")
                        && inner.args.is_empty()
                    {
                        return true;
                    }
                }
                if ident_of_expr(receiver).is_some() {
                    return true;
                }
            }
        }
        false
    }

    fn walk(e: &Expr, out: &mut HashMap<String, usize>) {
        match e {
            Expr::Binary(ExprBinary { op, left, right, .. }) => {
                let bound = match op {
                    BinOp::Lt(_) | BinOp::Le(_) => Some(DEFAULT_MAX),
                    _ => None,
                };
                if let Some(b) = bound {
                    if let Some(name) = extract_param_name(left) {
                        if is_collection_len(right) {
                            out.entry(name.clone()).or_insert(b);
                        }
                        // Literal upper-bound: `i < 4` or `i <= 4`. Cap the
                        // sampled range at the literal so prop_assume!
                        // doesn't reject. Strict `<` shrinks by one.
                        if let Some(lit) = extract_usize_literal(right) {
                            let cap = match op {
                                BinOp::Lt(_) => lit.saturating_sub(1),
                                _ => lit,
                            };
                            out.entry(name).or_insert(cap);
                        }
                    }
                    // Chained-compare shapes: `0 <= i < s.len()` parses as
                    // `(0 <= i) < s.len()`. Pattern-match the inner LHS (or
                    // deeper) to recover the index name. For longer chains
                    // (`0 <= i <= j < s.len()`) recurse into the left.
                    if let Some(rightmost) = rightmost_chain_param(left) {
                        if is_collection_len(right) {
                            out.entry(rightmost.clone()).or_insert(b);
                        }
                        if let Some(lit) = extract_usize_literal(right) {
                            let cap = match op {
                                BinOp::Lt(_) => lit.saturating_sub(1),
                                _ => lit,
                            };
                            out.entry(rightmost).or_insert(cap);
                        }
                    }
                    // Also recursively handle the LHS so e.g. `(0 <= i) <= j`
                    // contributes its inner relations to the map.
                    walk(left, out);
                }
                if matches!(op, BinOp::And(_)) {
                    walk(left, out);
                    walk(right, out);
                }
            }
            Expr::BigAnd(b) => {
                for inner in &b.exprs {
                    walk(&inner.expr, out);
                }
            }
            Expr::Paren(p) => walk(&p.expr, out),
            _ => {}
        }
    }

    /// Walk `<expr> <op> <expr>` where the chain is left-associative and
    /// return the rightmost ident in the chain. Used to extract the chain's
    /// trailing variable from arbitrarily deep nestings.
    fn rightmost_chain_param(e: &Expr) -> Option<String> {
        match e {
            Expr::Binary(b) => {
                if matches!(
                    b.op,
                    BinOp::Lt(_) | BinOp::Le(_) | BinOp::Gt(_) | BinOp::Ge(_)
                ) {
                    extract_param_name(&b.right)
                } else {
                    None
                }
            }
            Expr::Paren(p) => rightmost_chain_param(&p.expr),
            _ => None,
        }
    }

    /// Second pass: propagate bounds from already-mapped params to params
    /// that are bounded against them. Handles `i <= j` by giving `i` the
    /// same bound as `j` when `j` is in the map. Iterates to a fixed point.
    fn walk_transitive(e: &Expr, out: &mut HashMap<String, usize>) {
        fn walk_once(e: &Expr, out: &mut HashMap<String, usize>) -> bool {
            let mut changed = false;
            match e {
                Expr::Binary(ExprBinary { op, left, right, .. }) => {
                    if matches!(op, BinOp::Lt(_) | BinOp::Le(_)) {
                        // Direct shape: `<lname> <op> <rname>`.
                        if let (Some(li), Some(ri)) = (
                            extract_param_name(left),
                            extract_param_name(right),
                        ) {
                            if let Some(&b) = out.get(&ri) {
                                if !out.contains_key(&li) {
                                    out.insert(li, b);
                                    changed = true;
                                }
                            }
                        }
                        // Chained shape: `<inner> <op> <rname>` where inner
                        // is itself a comparison. Walk to the inner's
                        // rightmost ident and try to inherit from rname.
                        if let Some(inner_rightmost) = rightmost_chain_param(left)
                        {
                            if let Some(ri) = extract_param_name(right) {
                                if let Some(&b) = out.get(&ri) {
                                    if !out.contains_key(&inner_rightmost) {
                                        out.insert(inner_rightmost, b);
                                        changed = true;
                                    }
                                }
                            }
                        }
                    }
                    if matches!(op, BinOp::And(_)) {
                        changed |= walk_once(left, out);
                        changed |= walk_once(right, out);
                    }
                    // Recurse into Lt/Le's left too — handles arbitrarily
                    // deep chains like `0 <= i <= j <= s.len()`.
                    if matches!(op, BinOp::Lt(_) | BinOp::Le(_)) {
                        changed |= walk_once(left, out);
                    }
                }
                Expr::BigAnd(b) => {
                    for inner in &b.exprs {
                        changed |= walk_once(&inner.expr, out);
                    }
                }
                Expr::Paren(p) => {
                    changed |= walk_once(&p.expr, out);
                }
                _ => {}
            }
            changed
        }
        loop {
            if !walk_once(e, out) {
                break;
            }
        }
    }

    for e in req.exprs.exprs.iter() {
        walk(e, &mut out);
    }
    // Second pass: propagate bounds through `<= other_param` chains.
    for e in req.exprs.exprs.iter() {
        walk_transitive(e, &mut out);
    }
    out
}

fn emit_harness(
    target: &ContractTarget,
    spec_fn_names: &HashSet<String>,
    user_types: &HashSet<String>,
    when_used_as_spec_redirect: &HashMap<String, String>,
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

    // 0. Reject ghost/tracked parameters early. Permission-passing methods
    // (`Tracked<&mut PointsTo<V>>`, `Ghost<...>`, etc.) have no runtime
    // representation: proptest can't sample one. Surface a clean diagnostic
    // pointing the user at the offending parameter rather than letting the
    // engine produce a confusing "unsupported type" error downstream.
    for p in &sig.inputs {
        if let FnArgKind::Typed(pat_type) = &p.kind {
            if let Some(wrapper) = ghost_wrapper_name(&pat_type.ty) {
                return Err(Error::new_spanned(
                    &pat_type.ty,
                    format!(
                        "verus_pbt: this parameter has type `{wrapper}<...>`, which carries \
ghost/permission state that doesn't exist at runtime. Property-based testing requires \
sample-able runtime values, so methods that take `Tracked<...>` / `Ghost<...>` / \
`Proof<...>` parameters can't be harnessed.\n\
\n\
If you want to test the runtime-observable behavior, factor it into a wrapper fn that \
takes only ordinary types and add `#[pbt]` to that wrapper instead.",
                        wrapper = wrapper
                    ),
                ));
            }
        }
        // Tracked receivers (`tracked self` / `tracked &self`) — same
        // reasoning; Verus_syn carries this on the receiver's mode marker.
    }
    // Also reject ghost/tracked return types.
    if let ReturnType::Type(_, _, _, ty) = &sig.output {
        if let Some(wrapper) = ghost_wrapper_name(ty) {
            return Err(Error::new_spanned(
                ty,
                format!(
                    "verus_pbt: this function returns `{wrapper}<...>`, which carries \
ghost/permission state that doesn't exist at runtime. Property-based testing requires \
the return value to be a sample-able runtime value.",
                    wrapper = wrapper
                ),
            ));
        }
    }

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
                        "verus_pbt: only `&self` and `&mut self` are supported (no owned `self`)",
                    ));
                }
                let is_mut = rcv.mutability.is_some();
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
                let receiver_shape = if is_mut {
                    // `&mut self` → wrap the user-type shape in MutRef so
                    // the harness samples an owned user value, snapshots
                    // its pre-state, and passes `&mut self_value` at the
                    // call site. Contracts mentioning `old(self)@` lower
                    // to `__pbt_pre_self_value`'s deep_view; bare `self@`
                    // (or `final(self)@`) lowers to the post-call view.
                    ParamShape::MutRef(Box::new(ParamShape::OwnedUserType(
                        canonical_user_ident,
                    )))
                } else {
                    ParamShape::RefUserType(canonical_user_ident)
                };
                param_shapes.push(receiver_shape);
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
                let mut owner_ty;
                let ty_for_classify: &Type = if let Some(self_ty) = self_ty_for_method.as_ref()
                {
                    owner_ty = (*pat_type.ty).clone();
                    replace_self_ty(&mut owner_ty, self_ty);
                    &owner_ty
                } else {
                    pat_type.ty.as_ref()
                };
                let shape = classify_param_type(ty_for_classify, user_types)?;
                param_idents.push(ident);
                param_shapes.push(shape);
            }
        }
    }

    // 2. Per-param call form for the rewriter.
    //
    // For each param we compute:
    //   • `param_call_form[id]`: how `<id>@` (or `<id>.deep_view()`)
    //     translates AT THE POST-CALL (or current) state. This is the
    //     normal deep_view form for non-mut params; for `&mut` params it's
    //     the *post-call* deep_view since the harness binding has been
    //     mutated by the real call.
    //   • `pre_view_for[id]`: how `old(<id>)@` translates. Only populated
    //     for `&mut` params; for owned/ref params there's no observable
    //     mutation, so the pre-state and post-state coincide and we leave
    //     this empty (and the rewriter resolves `old(<id>)` to bare `<id>`).
    //   • `user_typed_idents[id]`: the user-defined type name for params
    //     whose value is a sampled user type (drives the
    //     `<U as ToExecModel>::to_exec_model(&id)` insertion).
    //
    // Also: `mut_ref_param_idents` collects ParamShape::MutRef ids so we
    // can emit `let __pbt_pre_<id> = <id>.clone();` snapshots before the
    // call.
    let mut param_call_form: HashMap<String, TokenStream2> = HashMap::new();
    let mut pre_view_for: HashMap<String, TokenStream2> = HashMap::new();
    let mut user_typed_idents: HashMap<String, Ident> = HashMap::new();
    for (id, shape) in param_idents.iter().zip(param_shapes.iter()) {
        param_call_form.insert(id.to_string(), shape.call_form_for_deep_view(id));
        if let Some(snap) = shape.pre_call_view_snapshot(id) {
            pre_view_for.insert(id.to_string(), snap);
        }
        // Reach into MutRef to find user-typed inner shapes.
        let inner_for_user_check: &ParamShape = match shape {
            ParamShape::MutRef(inner) => inner.as_ref(),
            other => other,
        };
        if let ParamShape::RefUserType(t) | ParamShape::OwnedUserType(t) =
            inner_for_user_check
        {
            user_typed_idents.insert(id.to_string(), t.clone());
        }
    }
    let _ = &self_ident;

    // 3. Return shape and ident.
    let return_shape = classify_return(&sig.output, user_types, self_ty_for_method.as_ref())?;
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
                pre_view_for: &pre_view_for,
                user_typed_idents: &user_typed_idents,
                when_used_as_spec_redirect,
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
                pre_view_for: &pre_view_for,
                user_typed_idents: &user_typed_idents,
                when_used_as_spec_redirect,
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
    // Pre-scan the requires for fixed-length constraints on collection params.
    // Patterns like `s@.len() == 4` (or `s.deep_view().len() == 4`) are common
    // for binary parsing/serialization APIs and would otherwise cause proptest
    // to reject ~all sampled inputs (default Vec strategy is 0..=16).
    let fixed_lengths: HashMap<String, usize> = scan_fixed_length_constraints(sig);
    // Pre-scan for usize-typed params bounded by another collection's len
    // (e.g. `i < s@.len()`). Sample those in `0..=DEFAULT_MAX` so prop_assume
    // doesn't reject ~all samples.
    let index_bounds: HashMap<String, usize> = scan_index_bound_constraints(sig);
    let strategy_decls: Vec<TokenStream2> = param_idents
        .iter()
        .zip(param_shapes.iter())
        .map(|(id, shape)| {
            let ty = shape.harness_type();
            // For `&mut`-shaped params we need to mutate the harness
            // binding through the call, so emit `mut <id>` on the
            // proptest decl. The same convention is fine for non-mut
            // params (an unused `mut` is a warning at most), but we keep
            // it scoped to actual mutation to minimize spurious warnings.
            let lhs_id: TokenStream2 = if matches!(shape, ParamShape::MutRef(_)) {
                quote! { mut #id }
            } else {
                quote! { #id }
            };
            // Fixed-size array params: sample a Vec<E> of exactly N
            // elements (the const expression in the array shape, after
            // const-generic substitution). This pre-empts the
            // fixed_lengths-driven path because the size is known
            // structurally rather than via a `requires` clause.
            if let ParamShape::OwnedArray(_, len) | ParamShape::RefArray(_, len) = shape {
                if let Some(elem_strategy) = element_strategy_for_shape(shape) {
                    return quote! {
                        #lhs_id in ::proptest::collection::vec(#elem_strategy, (#len)..=(#len))
                    };
                }
            }
            // For Vec<T> / Slice<T> params with a fixed-length precondition,
            // sample exactly that length so prop_assume! never rejects.
            if let Some(&len) = fixed_lengths.get(&id.to_string()) {
                if let Some(elem_strategy) = element_strategy_for_shape(shape) {
                    return quote! {
                        #lhs_id in ::proptest::collection::vec(#elem_strategy, #len..=#len)
                    };
                }
            }
            // For usize index params bounded by `< collection.len()`, sample
            // in `0..=max` so a high fraction of samples satisfy the
            // precondition. The remaining mismatches (where the actually
            // sampled collection is shorter) get filtered by prop_assume!.
            if let Some(&max) = index_bounds.get(&id.to_string()) {
                if matches!(shape, ParamShape::Primitive(_)) {
                    return quote! {
                        #lhs_id in (0usize..=#max)
                    };
                }
            }
            quote! { #lhs_id in ::verus_pbt_runtime::pbt_strategy::<#ty>() }
        })
        .collect();

    // Pre-call bindings: for shapes that need a stable storage location
    // (currently fixed-size arrays), emit a `let` before the call so the
    // borrow lives long enough.
    let mut pre_call_bindings: Vec<TokenStream2> = Vec::new();
    let mut prebinding_idents: Vec<Option<Ident>> = Vec::new();
    for (id, shape) in param_idents.iter().zip(param_shapes.iter()) {
        if let Some((bound, stmt)) = shape.pre_call_binding(id) {
            pre_call_bindings.push(stmt);
            prebinding_idents.push(Some(bound));
        } else {
            prebinding_idents.push(None);
        }
    }

    // For each `&mut`-shaped param, snapshot the pre-call value so the
    // contract's `old(<id>)` references can read it after the call has
    // mutated `<id>`. Snapshot *before* any other pre-call binding so
    // the snapshot reflects the truly-original sampled value.
    let mut pre_state_lets: Vec<TokenStream2> = Vec::new();
    for (id, shape) in param_idents.iter().zip(param_shapes.iter()) {
        if let Some(stmt) = shape.pre_state_let(id) {
            pre_state_lets.push(stmt);
        }
    }

    // Harness arguments need to be `mut` for `&mut`-shaped params so
    // `&mut <id>` is well-typed. Walk the strategy decls and prepend
    // `mut ` where needed. We only have access to param idents here; the
    // strategy decls already emit `<id> in <strategy>` syntax — proptest
    // accepts a `mut` keyword on the binding.
    //
    // (Implemented inside the strategy decl construction below to keep
    // the normal-path emission clean.)

    let real_call_args: Vec<TokenStream2> = param_idents
        .iter()
        .zip(param_shapes.iter())
        .zip(prebinding_idents.iter())
        .map(|((id, shape), prebound)| {
            shape.arg_with_optional_prebinding(id, prebound.as_ref())
        })
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
            #![proptest_config(::proptest::test_runner::Config {
                // Bump the global rejects ceiling so harnesses with
                // multi-param relational preconditions (e.g. `i <= j`) can
                // still complete enough successful cases. Default is 1024;
                // we raise it to 65536. The default success threshold
                // (256) is unchanged.
                max_global_rejects: 65536,
                ..::proptest::test_runner::Config::default()
            })]

            #[test]
            fn #pbt_fn_name(
                #(#strategy_decls),*
            ) {
                // Snapshot pre-call state for `&mut`-shaped params FIRST so
                // both `requires` and `ensures` can reference `old(<id>)`.
                #(#pre_state_lets)*
                #(::proptest::prop_assume!(#rewritten_requires);)*
                #(#pre_call_bindings)*
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
            &classified.when_used_as_spec_redirect,
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
