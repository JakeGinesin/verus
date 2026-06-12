//! `#[pbt_provide]` and `#[pbt]` attribute preprocessing.
//!
//! These run as a whole-`Vec<Item>` pass during `contrib_preprocess_items`,
//! which gives them sibling visibility within a single `verus! { ... }` block
//! (the per-item hook used by `auto_spec` cannot see siblings).
//!
//! ## `#[pbt_provide]`
//!
//! Marks a `struct`/`enum`/spec-fn as a source of property-based-testing
//! infrastructure. The marked item (and, for a type, its inherent impls) is
//! folded into a single `verus_pbt_unverified! { ... }` block, so the backend
//! emits the engine `Exec*` companions, `exec_*` spec fns, and the
//! `PbtStrategy` / `ToExecModel` / `PbtSpecCompanion` trait impls (which
//! resolve by trait lookup across files).
//!
//! ## `#[pbt]`
//!
//! Marks a contract-bearing exec fn (free or method) to be property-tested.
//! The pass computes the transitive closure of spec fns + user types its
//! `requires`/`ensures` (and their bodies/fields) reach **among siblings in
//! the same `verus!` block**, and folds the exec fn + that closure into one
//! engine block. The backend then generates both the engine companions and
//! the `proptest!` harness. The user adds only `#[pbt]` — no separate macro
//! block, no `#[pbt_provide]` for in-block dependencies.
//!
//! Items the closure cannot resolve in-block (defined in another file) are
//! left out; the harness references them by trait, and a missing
//! `#[pbt_provide]` at their definition site surfaces as the
//! `on_unimplemented` diagnostic on `PbtStrategy`/`ToExecModel`.

use proc_macro2::TokenStream as TokenStream2;
use quote::{format_ident, quote};
use std::collections::{HashMap, HashSet};
use verus_syn::spanned::Spanned;
use verus_syn::visit::Visit;
use verus_syn::visit_mut::VisitMut;
use verus_syn::{
    Attribute, Expr, ExprPath, FnMode, GenericArgument, GenericParam, Generics, Ident, ImplItem,
    Item, ItemFn, Meta, PathArguments, Type, UseTree,
};

// ---------------------------------------------------------------------------
// Generics / instantiation
// ---------------------------------------------------------------------------

/// A substitution map carrying both type-param and const-param bindings the
/// user supplied at a `#[pbt(...)]` callsite. Type bindings (e.g.
/// `#[pbt(T = u64)]`) live in `map`; const-generic bindings (e.g.
/// `#[pbt(N = 4)]`) live in `consts`. The two maps are kept parallel rather
/// than merged because their substitution semantics differ — type-params
/// substitute inside `Type` nodes (visit_type_mut), const-params substitute
/// inside expression positions of `[T; N]` arrays and turbofish const args
/// (visit_expr_mut + a `Type::Array` case).
#[derive(Clone, Default, Debug)]
pub(crate) struct Subst {
    pub map: HashMap<String, Type>,
    pub consts: HashMap<String, Expr>,
}

impl Subst {
    fn is_empty(&self) -> bool {
        self.map.is_empty() && self.consts.is_empty()
    }

    /// Equality on textual representation of the bound types and const
    /// expressions — robust enough for the conflict-detection use case.
    fn agrees_with(&self, other: &Subst) -> bool {
        if self.map.len() != other.map.len() {
            return false;
        }
        if self.consts.len() != other.consts.len() {
            return false;
        }
        for (k, v) in &self.map {
            match other.map.get(k) {
                Some(v2) if quote!(#v).to_string() == quote!(#v2).to_string() => {}
                _ => return false,
            }
        }
        for (k, v) in &self.consts {
            match other.consts.get(k) {
                Some(v2) if quote!(#v).to_string() == quote!(#v2).to_string() => {}
                _ => return false,
            }
        }
        true
    }

    /// Pretty-print as `K = T, N = 4` for diagnostics.
    fn render(&self) -> String {
        let mut keys: Vec<(&String, String)> = self
            .map
            .iter()
            .map(|(k, v)| (k, format!("{}", quote!(#v))))
            .chain(
                self.consts
                    .iter()
                    .map(|(k, v)| (k, format!("{}", quote!(#v)))),
            )
            .collect();
        keys.sort_by(|a, b| a.0.cmp(b.0));
        keys.iter()
            .map(|(k, v)| format!("{} = {}", k, v))
            .collect::<Vec<_>>()
            .join(", ")
    }
}

/// Parse the body of a `#[pbt(K = T, V = U)]` (or `#[pbt_provide(...)]`)
/// attribute into a `Subst`.
///
/// Each pair's RHS is first attempted as a `Type` (for type-param bindings),
/// and on parse failure as an `Expr` (for const-param bindings like
/// `#[pbt(N = 4)]`). The resolution into the type vs. const map is delayed
/// to the substitution step, where we look at the surrounding item's
/// generics to decide which slot a given key goes into. This keeps parsing
/// liberal so a malformed entry doesn't kill the whole `#[pbt(...)]`. Returns
/// `None` if `attr` is the bare `#[pbt]` form (no parens).
fn parse_marker_subst(attr: &Attribute) -> Option<Subst> {
    let tokens = match &attr.meta {
        Meta::Path(_) => return None,
        Meta::List(list) => list.tokens.clone(),
        Meta::NameValue(_) => return None,
    };
    use verus_syn::parse::Parser;
    use verus_syn::punctuated::Punctuated;
    use verus_syn::Token;

    /// A single `K = <Type-or-Expr>` pair. `value` carries the RHS as raw
    /// tokens so we can speculatively re-parse it as a `Type` first and an
    /// `Expr` second; this avoids the order-dependent failure mode where a
    /// `Type` parse consumes input even when it's actually an `Expr`.
    struct Pair {
        key: Ident,
        _eq: Token![=],
        value: TokenStream2,
    }
    impl verus_syn::parse::Parse for Pair {
        fn parse(input: verus_syn::parse::ParseStream) -> verus_syn::parse::Result<Self> {
            let key: Ident = input.parse()?;
            let _eq: Token![=] = input.parse()?;
            // Greedily collect tokens until a comma at the current
            // bracket-depth. This mirrors how attribute meta args are
            // typically tokenized and lets us delay the Type-vs-Expr choice.
            let value: TokenStream2 = input.step(|cursor| {
                let mut acc = TokenStream2::new();
                let mut cur = *cursor;
                while let Some((tt, next)) = cur.token_tree() {
                    if let proc_macro2::TokenTree::Punct(p) = &tt {
                        if p.as_char() == ',' {
                            return Ok((acc, cur));
                        }
                    }
                    acc.extend(std::iter::once(tt));
                    cur = next;
                }
                Ok((acc, cur))
            })?;
            Ok(Pair { key, _eq, value })
        }
    }

    let parser =
        |s: verus_syn::parse::ParseStream| Punctuated::<Pair, Token![,]>::parse_terminated(s);
    let pairs = match parser.parse2(tokens) {
        Ok(p) => p,
        Err(_) => return Some(Subst::default()),
    };
    let mut map = HashMap::new();
    let mut consts = HashMap::new();
    for p in pairs {
        // Try Type first, then Expr. Both are valid surface forms; prefer
        // the Type interpretation when both succeed because the common case
        // is `T = u32`. The const-param path triggers only for entries like
        // `N = 4`, which fail the Type parse since a bare integer literal
        // isn't a Type.
        let v_ts = p.value.clone();
        if let Ok(ty) = verus_syn::parse2::<Type>(v_ts.clone()) {
            map.insert(p.key.to_string(), ty);
        } else if let Ok(e) = verus_syn::parse2::<Expr>(v_ts) {
            consts.insert(p.key.to_string(), e);
        }
        // Silently drop unparseable RHS — caller's bad form, downstream
        // errors will fire when the user tries to use the key.
    }
    Some(Subst { map, consts })
}

/// Find a `#[pbt]`-family marker on an item and return its parsed subst.
fn item_marker_subst(item: &Item, name: &str) -> Option<Subst> {
    item_attrs(item)?
        .iter()
        .find(|a| attr_is(a, name))
        .and_then(parse_marker_subst)
}

fn impl_fn_marker_subst(f: &verus_syn::ImplItemFn, name: &str) -> Option<Subst> {
    f.attrs
        .iter()
        .find(|a| attr_is(a, name))
        .and_then(parse_marker_subst)
}

/// Returns the names of an item's type parameters (e.g. `["V"]` for
/// `struct Stack<V> { ... }`). Empty for non-generic items.
fn item_type_params(item: &Item) -> Vec<Ident> {
    let generics: Option<&Generics> = match item {
        Item::Struct(s) => Some(&s.generics),
        Item::Enum(e) => Some(&e.generics),
        Item::Impl(im) => Some(&im.generics),
        Item::Fn(f) => Some(&f.sig.generics),
        _ => None,
    };
    generics
        .map(|g| {
            g.params
                .iter()
                .filter_map(|p| match p {
                    GenericParam::Type(tp) => Some(tp.ident.clone()),
                    _ => None,
                })
                .collect()
        })
        .unwrap_or_default()
}

/// Returns the names of an item's const-generic parameters (e.g. `["N"]` for
/// `fn foo<const N: usize>() { ... }`). Empty for non-generic items.
fn item_const_params(item: &Item) -> Vec<Ident> {
    let generics: Option<&Generics> = match item {
        Item::Struct(s) => Some(&s.generics),
        Item::Enum(e) => Some(&e.generics),
        Item::Impl(im) => Some(&im.generics),
        Item::Fn(f) => Some(&f.sig.generics),
        _ => None,
    };
    generics
        .map(|g| {
            g.params
                .iter()
                .filter_map(|p| match p {
                    GenericParam::Const(cp) => Some(cp.ident.clone()),
                    _ => None,
                })
                .collect()
        })
        .unwrap_or_default()
}

/// Best-effort display name for diagnostics: type name for struct/enum/impl,
/// fn name for fns, fallback to "item" otherwise.
fn item_display_name(item: &Item) -> String {
    match item {
        Item::Struct(s) => s.ident.to_string(),
        Item::Enum(e) => e.ident.to_string(),
        Item::Fn(f) => f.sig.ident.to_string(),
        Item::Impl(im) => {
            if let Type::Path(tp) = im.self_ty.as_ref() {
                if let Some(seg) = tp.path.segments.last() {
                    return format!("impl {}", seg.ident);
                }
            }
            "impl".into()
        }
        _ => "item".into(),
    }
}

/// Strip the type-args from any in-block reference to a monomorphized sibling.
/// After substitution, `struct Cell<V>` becomes `struct Cell` (no params), so
/// references like `Cell<u64>` in fields, impl Self types, and turbofish
/// uses must lose their `<u64>` to compile. Walks types and expr-paths;
/// matches by single-segment ident name only.
fn strip_type_args_for_names(item: &mut Item, names: &HashSet<String>) {
    if names.is_empty() {
        return;
    }
    struct R<'a> {
        names: &'a HashSet<String>,
    }
    impl<'a> VisitMut for R<'a> {
        fn visit_type_path_mut(&mut self, tp: &mut verus_syn::TypePath) {
            if tp.qself.is_none() && tp.path.segments.len() == 1 {
                let seg = &mut tp.path.segments[0];
                if self.names.contains(&seg.ident.to_string()) {
                    seg.arguments = PathArguments::None;
                }
            }
            verus_syn::visit_mut::visit_type_path_mut(self, tp);
        }
        fn visit_expr_path_mut(&mut self, p: &mut ExprPath) {
            for seg in p.path.segments.iter_mut() {
                if self.names.contains(&seg.ident.to_string()) {
                    seg.arguments = PathArguments::None;
                }
            }
            verus_syn::visit_mut::visit_expr_path_mut(self, p);
        }
    }
    R { names }.visit_item_mut(item);
}

/// Apply a substitution to a `Type`. Replaces every single-segment
/// `TypePath` whose ident is a key in `subst.map` with the bound type, and
/// every `Type::Array(_, len)` whose `len` expression is a single-ident path
/// matching a key in `subst.consts` with the bound expression — recursively
/// inside generic args, references, slices, tuples, etc.
fn substitute_type(ty: &mut Type, subst: &Subst) {
    if subst.is_empty() {
        return;
    }
    struct R<'a> {
        subst: &'a Subst,
    }
    impl<'a> VisitMut for R<'a> {
        fn visit_type_mut(&mut self, t: &mut Type) {
            // First, pre-empt `Type::Path` whose head ident matches: replace
            // the whole node, since `T<X>` doesn't make sense if `T` is a
            // primitive.
            if let Type::Path(tp) = t {
                if tp.qself.is_none()
                    && tp.path.leading_colon.is_none()
                    && tp.path.segments.len() == 1
                    && matches!(tp.path.segments[0].arguments, PathArguments::None)
                {
                    let name = tp.path.segments[0].ident.to_string();
                    if let Some(replacement) = self.subst.map.get(&name) {
                        *t = replacement.clone();
                        return;
                    }
                }
            }
            // `[T; N]`: recurse into `elem` (handled by visit_type_mut) AND
            // substitute the length expression if it's a single-ident path
            // matching a const-param key.
            if let Type::Array(arr) = t {
                substitute_const_expr(&mut arr.len, self.subst);
            }
            verus_syn::visit_mut::visit_type_mut(self, t);
        }
        fn visit_path_arguments_mut(&mut self, args: &mut PathArguments) {
            // Substitute const generic arguments inside `Foo::<T, N>` when
            // `N` resolves to a const-bound key. We walk the args here
            // because the default visitor would visit `GenericArgument::Const`
            // expressions but our `visit_expr_mut` is currently scoped to
            // const positions only via this path.
            if let PathArguments::AngleBracketed(ab) = args {
                for arg in ab.args.iter_mut() {
                    if let GenericArgument::Const(e) = arg {
                        substitute_const_expr(e, self.subst);
                    }
                }
            }
            verus_syn::visit_mut::visit_path_arguments_mut(self, args);
        }
    }
    R { subst }.visit_type_mut(ty);
}

/// If `e` is a single-segment path expression matching a key in
/// `subst.consts`, replace it with the bound expression. Otherwise no-op.
/// The replacement is whole-expression: a const generic name appears in
/// const position only, so we don't need to recurse into its substructure.
fn substitute_const_expr(e: &mut Expr, subst: &Subst) {
    if subst.consts.is_empty() {
        return;
    }
    if let Expr::Path(p) = e {
        if p.qself.is_none()
            && p.path.leading_colon.is_none()
            && p.path.segments.len() == 1
            && matches!(p.path.segments[0].arguments, PathArguments::None)
        {
            let name = p.path.segments[0].ident.to_string();
            if let Some(replacement) = subst.consts.get(&name) {
                *e = replacement.clone();
            }
        }
    }
}

/// Apply a substitution everywhere inside an item: field types, method
/// signatures, return types, generic args inside expression paths in spec fn
/// bodies, etc. After substitution, strip type-params from `generics.params`
/// and `where` clauses so the post-subst item is monomorphic.
fn substitute_item(item: &mut Item, subst: &Subst) {
    if subst.is_empty() {
        return;
    }
    struct R<'a> {
        subst: &'a Subst,
    }
    impl<'a> VisitMut for R<'a> {
        fn visit_type_mut(&mut self, t: &mut Type) {
            substitute_type(t, self.subst);
            // Don't recurse — substitute_type already walks the subtree.
        }
        fn visit_expr_path_mut(&mut self, p: &mut ExprPath) {
            // Substitute inside generic args of expression paths
            // (e.g. `Vec::<V>::new()`).
            for seg in p.path.segments.iter_mut() {
                if let PathArguments::AngleBracketed(ab) = &mut seg.arguments {
                    for arg in ab.args.iter_mut() {
                        if let GenericArgument::Type(t) = arg {
                            substitute_type(t, self.subst);
                        }
                    }
                }
            }
            verus_syn::visit_mut::visit_expr_path_mut(self, p);
        }
    }
    R { subst }.visit_item_mut(item);
    strip_substituted_generics(item, subst);
}

/// Remove substituted type-params from an item's generics list and prune any
/// `where` clauses that reference only substituted params. Conservative:
/// leaves untouched anything we don't fully understand.
fn strip_substituted_generics(item: &mut Item, subst: &Subst) {
    let generics: Option<&mut Generics> = match item {
        Item::Struct(s) => Some(&mut s.generics),
        Item::Enum(e) => Some(&mut e.generics),
        Item::Impl(im) => Some(&mut im.generics),
        Item::Fn(f) => Some(&mut f.sig.generics),
        _ => None,
    };
    if let Some(g) = generics {
        // Remove substituted type AND const params.
        let keep = |p: &GenericParam| -> bool {
            match p {
                GenericParam::Type(tp) => !subst.map.contains_key(&tp.ident.to_string()),
                GenericParam::Const(cp) => !subst.consts.contains_key(&cp.ident.to_string()),
                _ => true,
            }
        };
        let new_params: verus_syn::punctuated::Punctuated<_, _> =
            g.params.iter().filter(|p| keep(p)).cloned().collect();
        g.params = new_params;
        if g.params.is_empty() {
            g.lt_token = None;
            g.gt_token = None;
        }
        // Drop the whole where-clause if all bounded types have been
        // substituted away. (Attempting to selectively keep bounds whose
        // types reference unsubstituted params is fragile; rustc will catch
        // any leftover bound that no longer makes sense.)
        if let Some(wc) = &mut g.where_clause {
            let preds: verus_syn::punctuated::Punctuated<_, _> = wc
                .predicates
                .iter()
                .filter(|pred| match pred {
                    verus_syn::WherePredicate::Type(pt) => {
                        !type_is_fully_substituted(&pt.bounded_ty, subst)
                    }
                    _ => true,
                })
                .cloned()
                .collect();
            wc.predicates = preds;
        }
        if g.where_clause
            .as_ref()
            .map_or(false, |wc| wc.predicates.is_empty())
        {
            g.where_clause = None;
        }
    }
    // For impls, also substitute the Self type and trait_ args.
    if let Item::Impl(im) = item {
        substitute_type(&mut im.self_ty, subst);
        if let Some((_, path, _)) = &mut im.trait_ {
            for seg in path.segments.iter_mut() {
                if let PathArguments::AngleBracketed(ab) = &mut seg.arguments {
                    for arg in ab.args.iter_mut() {
                        if let GenericArgument::Type(t) = arg {
                            substitute_type(t, subst);
                        }
                    }
                }
            }
        }
        // And substitute inside each impl-fn's signature/body — covered by
        // the generic visitor above, but be explicit about clauses too.
        for ii in &mut im.items {
            if let ImplItem::Fn(f) = ii {
                substitute_signature(&mut f.sig, subst);
            }
        }
    }
    if let Item::Fn(f) = item {
        substitute_signature(&mut f.sig, subst);
    }
}

fn substitute_signature(sig: &mut verus_syn::Signature, subst: &Subst) {
    if subst.is_empty() {
        return;
    }
    // Substitute inside spec.requires / spec.ensures / spec.recommends / etc.
    if let Some(req) = &mut sig.spec.requires {
        for e in req.exprs.exprs.iter_mut() {
            substitute_expr_types(e, subst);
        }
    }
    if let Some(ens) = &mut sig.spec.ensures {
        for e in ens.exprs.exprs.iter_mut() {
            substitute_expr_types(e, subst);
        }
    }
}

fn substitute_expr_types(expr: &mut Expr, subst: &Subst) {
    struct R<'a> {
        subst: &'a Subst,
    }
    impl<'a> VisitMut for R<'a> {
        fn visit_type_mut(&mut self, t: &mut Type) {
            substitute_type(t, self.subst);
        }
        fn visit_expr_mut(&mut self, e: &mut Expr) {
            // Substitute const-generic name expressions wherever they appear
            // (e.g. `i < N` in a `requires` clause where `N` was bound to
            // `4` by `#[pbt(N = 4)]`). Recurse first so substitution happens
            // bottom-up and we don't re-visit the replacement.
            verus_syn::visit_mut::visit_expr_mut(self, e);
            substitute_const_expr(e, self.subst);
        }
    }
    R { subst }.visit_expr_mut(expr);
}

/// True if every `TypePath` head ident in `ty` is a substituted param. Used to
/// decide whether to drop a `where` predicate after substitution.
fn type_is_fully_substituted(ty: &Type, subst: &Subst) -> bool {
    if let Type::Path(tp) = ty {
        if tp.qself.is_none() && tp.path.segments.len() == 1 {
            let name = tp.path.segments[0].ident.to_string();
            return subst.map.contains_key(&name);
        }
    }
    false
}

/// Resolve a single `Type` argument under the active substitution, ignoring
/// unbound names (they pass through unchanged).
fn resolve_type_under(ty: &Type, subst: &Subst) -> Type {
    let mut copy = ty.clone();
    substitute_type(&mut copy, subst);
    copy
}

/// Suggest a default concrete type for an unbound type parameter, used in
/// the diagnostic that fires when a `#[pbt]` is missing an instantiation. A
/// best-effort guess based on common bounds; rustc will provide a better
/// error if our guess fails to satisfy a more specific bound.
fn suggest_default_type(_param: &Ident, bounds: &[String]) -> Type {
    // Return a token-parseable Type for `u32`, the safe default that
    // satisfies most common numeric / Copy / Eq / Hash / Debug bounds we
    // see in vstd-style spec code.
    let _ = bounds;
    verus_syn::parse_quote!(u32)
}



// ---------------------------------------------------------------------------
// Attribute helpers
// ---------------------------------------------------------------------------

/// Lenient match for our marker attributes, mirroring `collect_attrs`:
/// accepts `#[m]`, `#[contrib::m]`, `#[vstd::contrib::m]`.
fn attr_is(attr: &Attribute, name: &str) -> bool {
    let path = attr.path();
    if path.leading_colon.is_some() {
        return false;
    }
    let segs: Vec<String> = path.segments.iter().map(|s| s.ident.to_string()).collect();
    let segs: Vec<&str> = segs.iter().map(|s| s.as_str()).collect();
    match &segs[..] {
        [s] => *s == name,
        ["contrib", s] => *s == name,
        ["vstd", "contrib", s] => *s == name,
        _ => false,
    }
}

fn item_attrs_mut(item: &mut Item) -> Option<&mut Vec<Attribute>> {
    match item {
        Item::Enum(i) => Some(&mut i.attrs),
        Item::Struct(i) => Some(&mut i.attrs),
        Item::Impl(i) => Some(&mut i.attrs),
        Item::Fn(i) => Some(&mut i.attrs),
        Item::Mod(i) => Some(&mut i.attrs),
        Item::Use(i) => Some(&mut i.attrs),
        Item::Const(i) => Some(&mut i.attrs),
        Item::Static(i) => Some(&mut i.attrs),
        Item::Type(i) => Some(&mut i.attrs),
        Item::Macro(i) => Some(&mut i.attrs),
        Item::ExternCrate(i) => Some(&mut i.attrs),
        Item::ForeignMod(i) => Some(&mut i.attrs),
        Item::Trait(i) => Some(&mut i.attrs),
        Item::TraitAlias(i) => Some(&mut i.attrs),
        Item::Union(i) => Some(&mut i.attrs),
        Item::AssumeSpecification(i) => Some(&mut i.attrs),
        _ => None,
    }
}

fn item_attrs(item: &Item) -> Option<&Vec<Attribute>> {
    match item {
        Item::Enum(i) => Some(&i.attrs),
        Item::Struct(i) => Some(&i.attrs),
        Item::Impl(i) => Some(&i.attrs),
        Item::Fn(i) => Some(&i.attrs),
        Item::Mod(i) => Some(&i.attrs),
        Item::Use(i) => Some(&i.attrs),
        Item::Const(i) => Some(&i.attrs),
        Item::Static(i) => Some(&i.attrs),
        Item::Type(i) => Some(&i.attrs),
        Item::Macro(i) => Some(&i.attrs),
        Item::ExternCrate(i) => Some(&i.attrs),
        Item::ForeignMod(i) => Some(&i.attrs),
        Item::Trait(i) => Some(&i.attrs),
        Item::TraitAlias(i) => Some(&i.attrs),
        Item::Union(i) => Some(&i.attrs),
        Item::AssumeSpecification(i) => Some(&i.attrs),
        _ => None,
    }
}

fn item_has_attr(item: &Item, name: &str) -> bool {
    item_attrs(item).map_or(false, |attrs| attrs.iter().any(|a| attr_is(a, name)))
}

/// Find the span of an attribute named `name` on `item` (for error reporting).
fn item_attr_span(item: &Item, name: &str) -> Option<proc_macro2::Span> {
    item_attrs(item)?
        .iter()
        .find(|a| attr_is(a, name))
        .map(|a| a.path().segments.last().map(|s| s.ident.span()).unwrap_or_else(|| a.path().span()))
}

/// Find the span of an attribute named `name` on an impl-item fn.
fn impl_fn_attr_span(f: &verus_syn::ImplItemFn, name: &str) -> Option<proc_macro2::Span> {
    f.attrs
        .iter()
        .find(|a| attr_is(a, name))
        .map(|a| a.path().segments.last().map(|s| s.ident.span()).unwrap_or_else(|| a.path().span()))
}

/// Item kinds `#[pbt_provide]` knows how to fold into the engine block.
/// Returns a static description of the item kind for error messages, or None
/// when the item kind is supported.
fn pbt_provide_unsupported_item_kind(item: &Item) -> Option<&'static str> {
    match item {
        // Supported: types, free fns (spec or exec), inherent impl blocks
        // (generic or not — generics get instantiated either via marker or
        // by inheritance), `assume_specification` items (which the pass
        // synthesizes into an exec wrapper that gets PBT'd), and trait
        // impl blocks (which the pass pre-rewrites to inherent shape with
        // mangled method names).
        Item::Struct(_) | Item::Enum(_) | Item::Fn(_) | Item::AssumeSpecification(_) => None,
        Item::Impl(_) => None,
        Item::Trait(_) => Some("a trait declaration"),
        Item::TraitAlias(_) => Some("a trait alias"),
        Item::Mod(_) => Some("a module"),
        Item::Use(_) => Some("a `use` declaration"),
        Item::Const(_) => Some("a `const` item"),
        Item::Static(_) => Some("a `static` item"),
        Item::Type(_) => Some("a type alias"),
        Item::Macro(_) => Some("a macro invocation"),
        Item::ExternCrate(_) => Some("an `extern crate` declaration"),
        Item::ForeignMod(_) => Some("an `extern { ... }` block"),
        Item::Union(_) => Some("a union (only structs and enums are supported)"),
        _ => Some("an item of an unsupported kind"),
    }
}

/// True if `f` is a body-less spec fn (i.e. an `uninterp spec fn` or a spec fn
/// declared without a body that the parser flagged with a deprecation warning).
/// The exec_spec engine cannot compile body-less specs into runnable companions,
/// so we surface a tailored error before invoking it.
fn is_uninterp_spec_fn(f: &ItemFn) -> bool {
    matches!(f.sig.mode, FnMode::Spec(..) | FnMode::SpecChecked(..))
        && (f.semi_token.is_some() || f.block.stmts.is_empty())
}

fn impl_fn_is_uninterp_spec(f: &verus_syn::ImplItemFn) -> bool {
    matches!(f.sig.mode, FnMode::Spec(..) | FnMode::SpecChecked(..))
        && (f.semi_token.is_some() || f.block.stmts.is_empty())
}

/// Lenient match for a macro invocation path: `m!`, `contrib::m!`,
/// `vstd::contrib::m!`.
fn macro_path_is(mac: &verus_syn::Macro, name: &str) -> bool {
    let path = &mac.path;
    if path.leading_colon.is_some() {
        return false;
    }
    let segs: Vec<String> = path.segments.iter().map(|s| s.ident.to_string()).collect();
    let segs: Vec<&str> = segs.iter().map(|s| s.as_str()).collect();
    match &segs[..] {
        [s] => *s == name,
        ["contrib", s] => *s == name,
        ["vstd", "contrib", s] => *s == name,
        _ => false,
    }
}

/// If `item` is an `external_pbt_provide! { ... }` invocation, return the names
/// of the spec fns it provides (Tier 4 trusted stubs).
fn external_provide_names(item: &Item) -> Option<Vec<String>> {
    if let Item::Macro(m) = item {
        if macro_path_is(&m.mac, "external_pbt_provide") {
            return Some(crate::contrib::external_pbt_provide::provided_names(
                m.mac.tokens.clone(),
            ));
        }
    }
    None
}

fn strip_attr_item(item: &mut Item, name: &str) {
    if let Some(attrs) = item_attrs_mut(item) {
        attrs.retain(|a| !attr_is(a, name));
    }
}

fn impl_fn_has_attr(f: &verus_syn::ImplItemFn, name: &str) -> bool {
    f.attrs.iter().any(|a| attr_is(a, name))
}

fn strip_attr_impl_fn(f: &mut verus_syn::ImplItemFn, name: &str) {
    f.attrs.retain(|a| !attr_is(a, name));
}

// ---------------------------------------------------------------------------
// Item identity helpers
// ---------------------------------------------------------------------------

fn type_def_name(item: &Item) -> Option<Ident> {
    match item {
        Item::Struct(s) => Some(s.ident.clone()),
        Item::Enum(e) => Some(e.ident.clone()),
        _ => None,
    }
}

fn free_spec_or_fn_name(item: &Item) -> Option<Ident> {
    if let Item::Fn(f) = item {
        Some(f.sig.ident.clone())
    } else {
        None
    }
}

fn inherent_impl_self_name(item: &Item) -> Option<Ident> {
    if let Item::Impl(im) = item {
        if im.trait_.is_some() {
            return None;
        }
        if let Type::Path(tp) = im.self_ty.as_ref() {
            if tp.qself.is_none() && tp.path.segments.len() == 1 {
                return Some(tp.path.segments[0].ident.clone());
            }
        }
    }
    None
}

// ---------------------------------------------------------------------------
// Reference collection (for closure analysis)
// ---------------------------------------------------------------------------

/// Collect every single-segment identifier referenced anywhere in an
/// expression — spec-fn calls `f(..)`, method calls `.m(..)`, type-ish path
/// segments, struct literals, etc. Over-collection is fine: we only keep the
/// ones that resolve to a sibling type/spec fn.
fn collect_idents_in_expr(expr: &Expr, out: &mut HashSet<String>) {
    struct C<'a> {
        out: &'a mut HashSet<String>,
    }
    impl<'ast, 'a> Visit<'ast> for C<'a> {
        fn visit_expr_path(&mut self, p: &'ast ExprPath) {
            for seg in &p.path.segments {
                self.out.insert(seg.ident.to_string());
            }
            verus_syn::visit::visit_expr_path(self, p);
        }
        fn visit_expr_method_call(&mut self, mc: &'ast verus_syn::ExprMethodCall) {
            self.out.insert(mc.method.to_string());
            verus_syn::visit::visit_expr_method_call(self, mc);
        }
    }
    let mut c = C { out };
    c.visit_expr(expr);
}

/// Like `collect_idents_in_expr` but also captures type arguments at each
/// use site. Returns a list of `(name, type_args)` pairs so the generics-
/// aware closure pass can propagate substitutions through the call graph.
fn collect_typed_refs_in_expr(expr: &Expr, out: &mut Vec<(String, Vec<Type>)>) {
    struct C<'a> {
        out: &'a mut Vec<(String, Vec<Type>)>,
    }
    impl<'ast, 'a> Visit<'ast> for C<'a> {
        fn visit_expr_path(&mut self, p: &'ast ExprPath) {
            for seg in &p.path.segments {
                let args = path_seg_type_args(&seg.arguments);
                self.out.push((seg.ident.to_string(), args));
            }
            verus_syn::visit::visit_expr_path(self, p);
        }
        fn visit_expr_method_call(&mut self, mc: &'ast verus_syn::ExprMethodCall) {
            let args = mc
                .turbofish
                .as_ref()
                .map(|tf| {
                    tf.args
                        .iter()
                        .filter_map(|a| match a {
                            GenericArgument::Type(t) => Some(t.clone()),
                            _ => None,
                        })
                        .collect::<Vec<_>>()
                })
                .unwrap_or_default();
            self.out.push((mc.method.to_string(), args));
            verus_syn::visit::visit_expr_method_call(self, mc);
        }
    }
    let mut c = C { out };
    c.visit_expr(expr);
}

fn path_seg_type_args(args: &PathArguments) -> Vec<Type> {
    if let PathArguments::AngleBracketed(ab) = args {
        ab.args
            .iter()
            .filter_map(|a| match a {
                GenericArgument::Type(t) => Some(t.clone()),
                _ => None,
            })
            .collect()
    } else {
        Vec::new()
    }
}

/// Collect identifiers referenced in a type (for transitive type closure):
/// the type name itself and any generic argument type names.
fn collect_idents_in_type(ty: &Type, out: &mut HashSet<String>) {
    struct C<'a> {
        out: &'a mut HashSet<String>,
    }
    impl<'ast, 'a> Visit<'ast> for C<'a> {
        fn visit_type_path(&mut self, tp: &'ast verus_syn::TypePath) {
            for seg in &tp.path.segments {
                self.out.insert(seg.ident.to_string());
                if let PathArguments::AngleBracketed(ab) = &seg.arguments {
                    for arg in &ab.args {
                        if let verus_syn::GenericArgument::Type(inner) = arg {
                            collect_idents_in_type(inner, self.out);
                        }
                    }
                }
            }
            verus_syn::visit::visit_type_path(self, tp);
        }
    }
    let mut c = C { out };
    c.visit_type(ty);
}

/// Like `collect_idents_in_type` but captures `(name, type_args)` at each
/// type reference. Used by the generics-aware closure pass to propagate
/// substitutions through field types and signatures.
fn collect_typed_refs_in_type(ty: &Type, out: &mut Vec<(String, Vec<Type>)>) {
    struct C<'a> {
        out: &'a mut Vec<(String, Vec<Type>)>,
    }
    impl<'ast, 'a> Visit<'ast> for C<'a> {
        fn visit_type_path(&mut self, tp: &'ast verus_syn::TypePath) {
            // Only single-segment paths are siblings we can resolve.
            if tp.qself.is_none()
                && tp.path.leading_colon.is_none()
                && tp.path.segments.len() == 1
            {
                let seg = &tp.path.segments[0];
                let args = path_seg_type_args(&seg.arguments);
                self.out.push((seg.ident.to_string(), args.clone()));
                for a in &args {
                    collect_typed_refs_in_type(a, self.out);
                }
                return;
            }
            verus_syn::visit::visit_type_path(self, tp);
        }
    }
    let mut c = C { out };
    c.visit_type(ty);
}

// ---------------------------------------------------------------------------
// Sibling index
// ---------------------------------------------------------------------------

/// Index over the block's sibling items so the closure can resolve names.
struct SiblingIndex {
    /// type name -> index of its struct/enum definition in `items`
    type_defs: HashMap<String, usize>,
    /// type name -> indices of its inherent impl blocks
    type_impls: HashMap<String, Vec<usize>>,
    /// free spec/fn name -> index
    free_fns: HashMap<String, usize>,
    /// spec method name -> set of owning type names (so a `.m()` call can pull
    /// in the owning type's impl)
    method_owners: HashMap<String, HashSet<String>>,
    /// item index -> ordered list of its type-param names (e.g. `["V"]`).
    /// Empty for items without generics.
    type_params_by_idx: HashMap<usize, Vec<Ident>>,
}

fn build_index(items: &[Item]) -> SiblingIndex {
    let mut type_defs = HashMap::new();
    let mut type_impls: HashMap<String, Vec<usize>> = HashMap::new();
    let mut free_fns = HashMap::new();
    let mut method_owners: HashMap<String, HashSet<String>> = HashMap::new();
    let mut type_params_by_idx: HashMap<usize, Vec<Ident>> = HashMap::new();

    for (i, item) in items.iter().enumerate() {
        let tps = item_type_params(item);
        if !tps.is_empty() {
            type_params_by_idx.insert(i, tps);
        }
        if let Some(n) = type_def_name(item) {
            type_defs.insert(n.to_string(), i);
        }
        if let Some(n) = free_spec_or_fn_name(item) {
            free_fns.insert(n.to_string(), i);
        }
        if let Some(self_name) = inherent_impl_self_name(item) {
            type_impls.entry(self_name.to_string()).or_default().push(i);
            if let Item::Impl(im) = item {
                for ii in &im.items {
                    if let ImplItem::Fn(f) = ii {
                        method_owners
                            .entry(f.sig.ident.to_string())
                            .or_default()
                            .insert(self_name.to_string());
                    }
                }
            }
        }
    }

    SiblingIndex {
        type_defs,
        type_impls,
        free_fns,
        method_owners,
        type_params_by_idx,
    }
}

/// Conflict info for diagnostics: which sibling item, and the two
/// disagreeing instantiations encountered.
#[derive(Debug)]
struct InstantiationConflict {
    item_idx: usize,
    item_name: String,
    first: Subst,
    second: Subst,
}

/// Result of the generics-aware closure pass.
struct ClosureResult {
    /// Per-item subst (empty for non-generic items).
    chosen: HashMap<usize, Subst>,
    /// Disagreeing instantiations encountered during the walk.
    conflicts: Vec<InstantiationConflict>,
}

/// Build a substitution from a positional list of concrete type args,
/// mapping the callee's type-param names to those args. If `args` is
/// shorter than `params`, fall back to inheriting the caller's binding by
/// matching param names (so `nonzero<T>(...)` reached from `check<T = u32>`
/// inherits `T = u32` even when the callsite has no turbofish).
fn subst_from_args(params: &[Ident], args: &[Type], caller_subst: &Subst) -> Subst {
    let mut map = HashMap::new();
    for (i, p) in params.iter().enumerate() {
        let key = p.to_string();
        if let Some(a) = args.get(i) {
            let mut resolved = a.clone();
            substitute_type(&mut resolved, caller_subst);
            map.insert(key, resolved);
        } else if let Some(t) = caller_subst.map.get(&key) {
            map.insert(key, t.clone());
        }
    }
    // Propagate the caller's const-generic substitutions verbatim — there
    // is no positional `args`-style binding for const generics in our
    // closure walk yet (we don't track the path of the call's turbofish
    // const args), so the safest and most useful behavior is to inherit
    // the caller's consts unchanged. When const generics are used by name
    // inside the callee item, the inherited map drives them to the same
    // value as in the caller.
    let consts = caller_subst.consts.clone();
    Subst { map, consts }
}

/// Generics-aware closure: like `compute_closure` but propagates
/// substitutions along the call/reference graph. The return preserves a
/// per-item subst so the engine emits monomorphized versions of generic
/// items folded by `#[pbt]` callsites.
fn compute_closure_with_substs(
    seeds: Vec<(String, Vec<Type>, Subst)>,
    items: &[Item],
    index: &SiblingIndex,
) -> ClosureResult {
    let mut chosen: HashMap<usize, Subst> = HashMap::new();
    let mut conflicts: Vec<InstantiationConflict> = Vec::new();
    let mut chosen_types: HashSet<String> = HashSet::new();
    // Worklist entries: (name, callsite type-args, caller subst).
    let mut worklist: Vec<(String, Vec<Type>, Subst)> = seeds;
    // Already-explored (name, subst-fingerprint) pairs.
    let mut seen: HashSet<(String, String)> = HashSet::new();

    while let Some((name, args, caller)) = worklist.pop() {
        // Resolve args under caller subst before further use.
        let resolved_args: Vec<Type> =
            args.iter().map(|t| resolve_type_under(t, &caller)).collect();
        let key = (name.clone(), {
            let s = Subst { map: caller.map.clone(), consts: caller.consts.clone() };
            s.render()
        });
        if !seen.insert(key) {
            continue;
        }

        // Try to resolve as a sibling type.
        if let Some(&def_idx) = index.type_defs.get(&name) {
            let params = index
                .type_params_by_idx
                .get(&def_idx)
                .cloned()
                .unwrap_or_default();
            let new_subst = subst_from_args(&params, &resolved_args, &caller);
            record_subst(def_idx, &name, new_subst.clone(), &mut chosen, &mut conflicts);
            chosen_types.insert(name.clone());
            // Recurse into field types under the new subst.
            let mut refs = Vec::<(String, Vec<Type>)>::new();
            collect_type_field_typed_refs(&items[def_idx], &mut refs);
            for (n, a) in refs {
                worklist.push((n, a, new_subst.clone()));
            }
            // Pull in inherent impls.
            if let Some(impl_idxs) = index.type_impls.get(&name) {
                for &ix in impl_idxs {
                    let impl_params = index
                        .type_params_by_idx
                        .get(&ix)
                        .cloned()
                        .unwrap_or_default();
                    // For an `impl<V> Stack<V>` block, the impl's params line
                    // up positionally with the type's params via the Self
                    // type's type-args. Use the new_subst (which already maps
                    // the type's params to concrete types) to derive the
                    // impl's subst.
                    let impl_subst = derive_impl_subst(
                        &impl_params,
                        &items[ix],
                        &new_subst,
                    );
                    record_subst(
                        ix,
                        &format!("{} impl block", name),
                        impl_subst.clone(),
                        &mut chosen,
                        &mut conflicts,
                    );
                    let mut impl_refs = Vec::<(String, Vec<Type>)>::new();
                    collect_impl_spec_typed_refs(&items[ix], &mut impl_refs);
                    for (n, a) in impl_refs {
                        worklist.push((n, a, impl_subst.clone()));
                    }
                }
            }
        }

        // Sibling free fn.
        if let Some(&fn_idx) = index.free_fns.get(&name) {
            let params = index
                .type_params_by_idx
                .get(&fn_idx)
                .cloned()
                .unwrap_or_default();
            let new_subst = subst_from_args(&params, &resolved_args, &caller);
            record_subst(fn_idx, &name, new_subst.clone(), &mut chosen, &mut conflicts);
            let mut refs = Vec::<(String, Vec<Type>)>::new();
            collect_fn_spec_typed_refs(&items[fn_idx], &mut refs);
            for (n, a) in refs {
                worklist.push((n, a, new_subst.clone()));
            }
        }

        // Sibling method name → owning type(s).
        if let Some(owners) = index.method_owners.get(&name) {
            for owner in owners {
                // Method-only references propagate the *caller's* subst —
                // the method site itself has no type-args we can pin to a
                // type's params.
                worklist.push((owner.clone(), Vec::new(), caller.clone()));
            }
        }
    }

    ClosureResult { chosen, conflicts }
}

/// Record a `(idx, subst)` pair, detecting conflicts with previously-recorded
/// substs for the same idx.
fn record_subst(
    idx: usize,
    name: &str,
    new_subst: Subst,
    chosen: &mut HashMap<usize, Subst>,
    conflicts: &mut Vec<InstantiationConflict>,
) {
    match chosen.get(&idx) {
        Some(old) if old.agrees_with(&new_subst) => {}
        Some(old) => {
            conflicts.push(InstantiationConflict {
                item_idx: idx,
                item_name: name.to_string(),
                first: old.clone(),
                second: new_subst,
            });
        }
        None => {
            chosen.insert(idx, new_subst);
        }
    }
}

/// Given an `impl<V> Stack<V>` block and the type-level subst `{V→u64}`
/// inferred from the type def, compute the impl's subst. Walks the impl's
/// Self type, matches its type-args positionally against the type def's
/// params, and substitutes back. Conservative: if the Self type is anything
/// other than a single-segment path, returns the type's subst unchanged.
fn derive_impl_subst(impl_params: &[Ident], impl_item: &Item, type_subst: &Subst) -> Subst {
    let Item::Impl(im) = impl_item else {
        return type_subst.clone();
    };
    // For inherent impls, the impl's type-params are conventionally listed
    // in the same order as the type's. Just propagate the subst's keys
    // re-mapped to the impl's own param names if they differ — but since
    // verus_syn impls usually re-use the same names (`impl<V> Stack<V>`),
    // this almost always reduces to subst pass-through.
    // The robust thing: read the impl's Self type-args; for each `Type::Path`
    // arg whose name matches an impl_param, bind that impl_param to the
    // corresponding key from type_subst.
    if let Type::Path(tp) = im.self_ty.as_ref() {
        if tp.qself.is_none() && tp.path.segments.len() == 1 {
            let seg = &tp.path.segments[0];
            if let PathArguments::AngleBracketed(ab) = &seg.arguments {
                let args: Vec<&GenericArgument> = ab.args.iter().collect();
                let mut map = HashMap::new();
                let type_keys: Vec<String> = {
                    let mut k: Vec<String> = type_subst.map.keys().cloned().collect();
                    k.sort();
                    k
                };
                // Best-effort: assume Self's type-args are referenced in the
                // declaration order of the type's params.
                let mut concrete_for_pos: Vec<Option<Type>> = Vec::new();
                for arg in &args {
                    match arg {
                        GenericArgument::Type(Type::Path(p))
                            if p.qself.is_none()
                                && p.path.segments.len() == 1
                                && matches!(
                                    p.path.segments[0].arguments,
                                    PathArguments::None
                                ) =>
                        {
                            // Fetch type_subst entry by ident name.
                            let n = p.path.segments[0].ident.to_string();
                            concrete_for_pos.push(type_subst.map.get(&n).cloned());
                        }
                        _ => concrete_for_pos.push(None),
                    }
                }
                let _ = type_keys;
                for (p, opt) in impl_params.iter().zip(concrete_for_pos) {
                    if let Some(t) = opt {
                        map.insert(p.to_string(), t);
                    }
                }
                return Subst { map, consts: type_subst.consts.clone() };
            }
        }
    }
    // Fallback: for impls whose params share names with the type, the type's
    // subst applies as-is.
    let mut map = HashMap::new();
    for p in impl_params {
        if let Some(t) = type_subst.map.get(&p.to_string()) {
            map.insert(p.to_string(), t.clone());
        }
    }
    Subst { map, consts: type_subst.consts.clone() }
}

/// Given a set of referenced identifiers, compute the transitive closure of
/// sibling item indices to pull into the engine block: type defs, their
/// inherent impls, and free spec fns — recursing into spec-fn bodies and
/// type fields.
fn compute_closure(
    seed_idents: HashSet<String>,
    items: &[Item],
    index: &SiblingIndex,
) -> HashSet<usize> {
    let mut chosen: HashSet<usize> = HashSet::new();
    let mut chosen_types: HashSet<String> = HashSet::new();
    let mut worklist: Vec<String> = seed_idents.into_iter().collect();
    let mut seen_idents: HashSet<String> = HashSet::new();

    while let Some(name) = worklist.pop() {
        if !seen_idents.insert(name.clone()) {
            continue;
        }

        // A referenced type: pull its def + all inherent impls.
        if let Some(&def_idx) = index.type_defs.get(&name) {
            if chosen.insert(def_idx) {
                // recurse into field types
                let mut refs = HashSet::new();
                collect_type_field_idents(&items[def_idx], &mut refs);
                worklist.extend(refs);
            }
            chosen_types.insert(name.clone());
            if let Some(impl_idxs) = index.type_impls.get(&name) {
                for &ix in impl_idxs {
                    if chosen.insert(ix) {
                        let mut refs = HashSet::new();
                        collect_impl_spec_idents(&items[ix], &mut refs);
                        worklist.extend(refs);
                    }
                }
            }
        }

        // A referenced free spec fn: pull it + recurse into its body.
        if let Some(&fn_idx) = index.free_fns.get(&name) {
            if chosen.insert(fn_idx) {
                let mut refs = HashSet::new();
                collect_fn_spec_idents(&items[fn_idx], &mut refs);
                worklist.extend(refs);
            }
        }

        // A referenced spec method name: pull the owning type(s) so the impl
        // (and thus the method) is included.
        if let Some(owners) = index.method_owners.get(&name) {
            for owner in owners {
                if !seen_idents.contains(owner) {
                    worklist.push(owner.clone());
                }
            }
        }
    }

    chosen
}

/// Collect identifiers referenced by a struct/enum's field types.
fn collect_type_field_idents(item: &Item, out: &mut HashSet<String>) {
    match item {
        Item::Struct(s) => {
            for f in &s.fields {
                collect_idents_in_type(&f.ty, out);
            }
        }
        Item::Enum(e) => {
            for v in &e.variants {
                for f in &v.fields {
                    collect_idents_in_type(&f.ty, out);
                }
            }
        }
        _ => {}
    }
}

fn collect_type_field_typed_refs(item: &Item, out: &mut Vec<(String, Vec<Type>)>) {
    match item {
        Item::Struct(s) => {
            for f in &s.fields {
                collect_typed_refs_in_type(&f.ty, out);
            }
        }
        Item::Enum(e) => {
            for v in &e.variants {
                for f in &v.fields {
                    collect_typed_refs_in_type(&f.ty, out);
                }
            }
        }
        _ => {}
    }
}

/// Collect identifiers referenced by the spec fns of an inherent impl block
/// (bodies + signature types).
fn collect_impl_spec_idents(item: &Item, out: &mut HashSet<String>) {
    if let Item::Impl(im) = item {
        for ii in &im.items {
            if let ImplItem::Fn(f) = ii {
                collect_sig_idents(&f.sig, out);
                if matches!(f.sig.mode, FnMode::Spec(..)) {
                    collect_block_idents(&f.block, out);
                }
            }
        }
    }
}

fn collect_impl_spec_typed_refs(item: &Item, out: &mut Vec<(String, Vec<Type>)>) {
    if let Item::Impl(im) = item {
        for ii in &im.items {
            if let ImplItem::Fn(f) = ii {
                collect_sig_typed_refs(&f.sig, out);
                if matches!(f.sig.mode, FnMode::Spec(..)) {
                    collect_block_typed_refs(&f.block, out);
                }
            }
        }
    }
}

/// Collect identifiers referenced by a free fn (body if spec + signature).
fn collect_fn_spec_idents(item: &Item, out: &mut HashSet<String>) {
    if let Item::Fn(f) = item {
        collect_sig_idents(&f.sig, out);
        if matches!(f.sig.mode, FnMode::Spec(..)) {
            collect_block_idents(&f.block, out);
        }
    }
}

fn collect_fn_spec_typed_refs(item: &Item, out: &mut Vec<(String, Vec<Type>)>) {
    if let Item::Fn(f) = item {
        collect_sig_typed_refs(&f.sig, out);
        if matches!(f.sig.mode, FnMode::Spec(..)) {
            collect_block_typed_refs(&f.block, out);
        }
    }
}

fn collect_sig_idents(sig: &verus_syn::Signature, out: &mut HashSet<String>) {
    for input in &sig.inputs {
        if let verus_syn::FnArgKind::Typed(pt) = &input.kind {
            collect_idents_in_type(&pt.ty, out);
        }
    }
    if let verus_syn::ReturnType::Type(_, _, _, ty) = &sig.output {
        collect_idents_in_type(ty, out);
    }
}

fn collect_sig_typed_refs(sig: &verus_syn::Signature, out: &mut Vec<(String, Vec<Type>)>) {
    for input in &sig.inputs {
        if let verus_syn::FnArgKind::Typed(pt) = &input.kind {
            collect_typed_refs_in_type(&pt.ty, out);
        }
    }
    if let verus_syn::ReturnType::Type(_, _, _, ty) = &sig.output {
        collect_typed_refs_in_type(ty, out);
    }
}

fn collect_block_idents(block: &verus_syn::Block, out: &mut HashSet<String>) {
    struct C<'a> {
        out: &'a mut HashSet<String>,
    }
    impl<'ast, 'a> Visit<'ast> for C<'a> {
        fn visit_expr(&mut self, e: &'ast Expr) {
            collect_idents_in_expr(e, self.out);
            verus_syn::visit::visit_expr(self, e);
        }
        fn visit_type(&mut self, t: &'ast Type) {
            collect_idents_in_type(t, self.out);
        }
    }
    let mut c = C { out };
    c.visit_block(block);
}

fn collect_block_typed_refs(block: &verus_syn::Block, out: &mut Vec<(String, Vec<Type>)>) {
    struct C<'a> {
        out: &'a mut Vec<(String, Vec<Type>)>,
    }
    impl<'ast, 'a> Visit<'ast> for C<'a> {
        fn visit_expr(&mut self, e: &'ast Expr) {
            collect_typed_refs_in_expr(e, self.out);
            verus_syn::visit::visit_expr(self, e);
        }
        fn visit_type(&mut self, t: &'ast Type) {
            collect_typed_refs_in_type(t, self.out);
        }
    }
    let mut c = C { out };
    c.visit_block(block);
}

/// Seed identifiers from a `#[pbt]` exec fn's contract (requires/ensures).
fn collect_contract_idents(sig: &verus_syn::Signature, out: &mut HashSet<String>) {
    if let Some(req) = &sig.spec.requires {
        for e in req.exprs.exprs.iter() {
            collect_idents_in_expr(e, out);
        }
    }
    if let Some(ens) = &sig.spec.ensures {
        for e in ens.exprs.exprs.iter() {
            collect_idents_in_expr(e, out);
        }
    }
    // Also the signature's own parameter/return types (e.g. `&User`).
    collect_sig_idents(sig, out);
}

fn collect_contract_typed_refs(sig: &verus_syn::Signature, out: &mut Vec<(String, Vec<Type>)>) {
    if let Some(req) = &sig.spec.requires {
        for e in req.exprs.exprs.iter() {
            collect_typed_refs_in_expr(e, out);
        }
    }
    if let Some(ens) = &sig.spec.ensures {
        for e in ens.exprs.exprs.iter() {
            collect_typed_refs_in_expr(e, out);
        }
    }
    collect_sig_typed_refs(sig, out);
}

// ---------------------------------------------------------------------------
// Step 1: tier-aware diagnostic for unresolved external spec fns
// ---------------------------------------------------------------------------

/// Collect names of *free function calls* `f(..)` appearing in a `#[pbt]`
/// contract. These are the only references whose resolution this pass is
/// responsible for: a free spec-fn call lowers to `exec_f(..)` in the harness,
/// so if `f` is defined in another file/crate it has no in-block companion and
/// nothing resolves it across files (unlike method calls on user types, which
/// resolve through the `ToExecModel`/`PbtSpecCompanion` traits at test time).
///
/// We deliberately ignore method calls (`x.m(..)`) — they go through traits —
/// and constructor-shaped calls (`Some(..)`, `Ok(..)`, `Permission::Read`),
/// which are paths into known types, not spec fns. The lowercase-initial
/// heuristic on a single-segment path name distinguishes a spec fn `is_small`
/// from an enum/tuple-struct constructor `Some`/`Pair`.
fn collect_free_call_names(sig: &verus_syn::Signature, out: &mut HashSet<String>) {
    struct C<'a> {
        out: &'a mut HashSet<String>,
    }
    impl<'ast, 'a> Visit<'ast> for C<'a> {
        fn visit_expr_call(&mut self, call: &'ast verus_syn::ExprCall) {
            if let Expr::Path(ExprPath { path, qself: None, .. }) = call.func.as_ref() {
                if path.leading_colon.is_none() && path.segments.len() == 1 {
                    let seg = &path.segments[0];
                    if matches!(seg.arguments, PathArguments::None) {
                        let name = seg.ident.to_string();
                        if name.starts_with(|c: char| c.is_lowercase() || c == '_') {
                            self.out.insert(name);
                        }
                    }
                }
            }
            verus_syn::visit::visit_expr_call(self, call);
        }
    }
    let mut c = C { out };
    if let Some(req) = &sig.spec.requires {
        for e in req.exprs.exprs.iter() {
            c.visit_expr(e);
        }
    }
    if let Some(ens) = &sig.spec.ensures {
        for e in ens.exprs.exprs.iter() {
            c.visit_expr(e);
        }
    }
}

/// Walk a `use` tree and record, for every leaf identifier, the dotted path
/// that leads to it (using the leaf's *effective* name — the rename if any).
/// `prefix` is the accumulated `a::b::` path so far. The result maps the
/// in-scope name a contract would write (e.g. `is_sorted`) to its full path
/// (e.g. `crate::seqlib::is_sorted`), so the diagnostic can suggest the real
/// definition site rather than a bare name.
fn record_use_tree(tree: &UseTree, prefix: &str, out: &mut HashMap<String, String>) {
    match tree {
        UseTree::Path(p) => {
            let next = if prefix.is_empty() {
                p.ident.to_string()
            } else {
                format!("{}::{}", prefix, p.ident)
            };
            record_use_tree(&p.tree, &next, out);
        }
        UseTree::Name(n) => {
            let full = if prefix.is_empty() {
                n.ident.to_string()
            } else {
                format!("{}::{}", prefix, n.ident)
            };
            out.insert(n.ident.to_string(), full);
        }
        UseTree::Rename(r) => {
            let full = if prefix.is_empty() {
                r.ident.to_string()
            } else {
                format!("{}::{}", prefix, r.ident)
            };
            // The contract refers to the renamed name; the definition lives at
            // the original path.
            out.insert(r.rename.to_string(), full);
        }
        UseTree::Glob(_) => {
            // `use a::b::*;` — record the module prefix under a synthetic key so
            // we can still suggest the module, even though we don't know the
            // leaf name. Keyed by "*" appended to prefix; consulted as a last
            // resort by `infer_path_for`.
            if !prefix.is_empty() {
                out.insert(format!("{}::*", prefix), format!("{}::*", prefix));
            }
        }
        UseTree::Group(g) => {
            for item in &g.items {
                record_use_tree(item, prefix, out);
            }
        }
    }
}

/// Build the name→path index from all sibling `use` items in the block.
fn build_use_index(items: &[Item]) -> HashMap<String, String> {
    let mut out = HashMap::new();
    for item in items {
        if let Item::Use(u) = item {
            record_use_tree(&u.tree, "", &mut out);
        }
    }
    out
}

/// Free spec-fn-like names that are built into the engine / Verus prelude and
/// therefore always resolvable without a sibling definition or `#[pbt_provide]`.
/// These must not be flagged as unresolved external specs.
fn is_builtin_free_spec_fn(name: &str) -> bool {
    matches!(
        name,
        // Verus prelude spec builtins that can appear in a contract.
        "arbitrary" | "spec_affirm" | "old"
    )
}

/// Infer the most plausible fully-qualified path for an unresolved free spec
/// fn `name`, using the sibling `use` index. Falls back to any glob-imported
/// module, then to the bare name.
fn infer_path_for(name: &str, use_index: &HashMap<String, String>) -> String {
    if let Some(p) = use_index.get(name) {
        return p.clone();
    }
    // Glob fallback: if exactly one `a::b::*` is in scope, suggest `a::b::name`.
    let globs: Vec<&String> =
        use_index.keys().filter(|k| k.ends_with("::*")).collect();
    if globs.len() == 1 {
        let base = globs[0].trim_end_matches("::*");
        return format!("{}::{}", base, name);
    }
    name.to_string()
}

/// Construct the tier-aware diagnostic message for an unresolved free spec fn.
fn unresolved_spec_fn_message(name: &str, inferred_path: &str) -> String {
    let path_is_known = inferred_path != name;
    let location = if path_is_known {
        format!("`{}` (resolved from a `use` in this file)", inferred_path)
    } else {
        format!("`{}`", name)
    };
    format!(
        "verus_pbt: the spec function {loc} is used in a `#[pbt]` contract but is \
defined outside this `verus!` block, so no exec companion can be generated for it.\n\
\n\
Resolve it at the first applicable tier:\n\
  1. If it is a container method (Seq/Map/Set/Multiset/Option), rewrite the \
contract to use the method form so the engine compiles it directly.\n\
  2. If you own its definition, add `#[pbt_provide]` to it (and the spec fns it \
calls) at its definition site so a companion is generated and resolved by path.\n\
  3. If it is a public-bodied spec fn in a crate you build with `cargo verus`, \
run `cargo verus pbt-gen` to emit its exec companion from the exported `.vir`.\n\
  4. Otherwise, supply a trusted exec stub next to your `#[pbt]` fn:\n\
       external_pbt_provide! {{ fn {path}(/* args */) -> /* ret */ {{ /* exec body */ }} }}\n\
\n\
(Method calls on `#[pbt_provide]`'d types resolve across files automatically; \
only free spec-fn calls need one of the tiers above.)",
        loc = location,
        path = inferred_path,
    )
}

// ---------------------------------------------------------------------------
// The unified pass
// ---------------------------------------------------------------------------

/// Synthesize an `#[verifier::external_body]` exec wrapper fn from an
/// `assume_specification` item. The wrapper preserves the marker attributes
/// (`#[pbt]` / `#[pbt_provide]`), the generic params, the parameter list, the
/// return type, and the contract; its body is a trusted call into the path
/// the assume_specification names. Once the rest of the pass sees an ordinary
/// `Item::Fn` with `#[pbt]`, the existing pipeline (closure, harness emit,
/// strategy sizing, etc.) carries the rest.
///
/// Returns `None` for shapes the synthesis can't handle (currently:
/// assume_specification with a `qself` projection — `<Vec<T> as Clone>::clone`
/// — that we don't yet emit a synthetic body for).
fn synthesize_pbt_wrapper_from_assume_spec(
    asp: &verus_syn::AssumeSpecification,
) -> Option<verus_syn::ItemFn> {
    use verus_syn::token::{Brace, Paren};
    use verus_syn::{
        Block, Expr, ExprCall, ExprPath, FnArg, FnArgKind, FnMode, ModeExec, Pat,
        PatType, Signature, SignatureSpec, Stmt, Token,
    };

    // Build the call expression that goes in the wrapper body.
    let func_path: Expr = Expr::Path(ExprPath {
        attrs: Vec::new(),
        qself: asp.qself.clone(),
        path: asp.path.clone(),
    });

    // Collect the wrapper's parameter list and the call-site arguments.
    // We renumber unnamed receivers (`&self`) to `__pbt_self` so the
    // synthesized body has a name to pass through.
    let mut wrapper_inputs: verus_syn::punctuated::Punctuated<FnArg, Token![,]> =
        verus_syn::punctuated::Punctuated::new();
    let mut call_args: Vec<Expr> = Vec::new();
    let mut had_self = false;
    if let Some((_, inputs)) = &asp.inputs {
        for arg in inputs.iter() {
            match &arg.kind {
                FnArgKind::Receiver(rcv) => {
                    // Synthesize a typed-style first argument: `__pbt_self: <Self type>`.
                    // For an `assume_specification`, the receiver's type is
                    // recoverable from the path's qself or first segment.
                    had_self = true;
                    let synth_name = Ident::new("__pbt_self", rcv.self_token.span);
                    // Best-effort Self type recovery: if the path is
                    // `T::method`, the type is `T`. Use the qself if present;
                    // otherwise build a `Type::Path` from all-but-the-last
                    // segment.
                    let recv_ty = recover_receiver_type(asp);
                    let ref_ty: Type = if rcv.reference.is_some() {
                        if rcv.mutability.is_some() {
                            verus_syn::parse_quote! { &mut #recv_ty }
                        } else {
                            verus_syn::parse_quote! { &#recv_ty }
                        }
                    } else {
                        recv_ty
                    };
                    let pat: Pat = verus_syn::parse_quote! { #synth_name };
                    wrapper_inputs.push(FnArg {
                        kind: FnArgKind::Typed(PatType {
                            attrs: Vec::new(),
                            pat: Box::new(pat),
                            colon_token: Token![:](rcv.self_token.span),
                            ty: Box::new(ref_ty),
                        }),
                        tracked: None,
                    });
                    call_args.push(verus_syn::parse_quote! { #synth_name });
                }
                FnArgKind::Typed(pt) => {
                    // Special-case `&Container<E>` parameters: my harness
                    // pipeline doesn't support `&Vec<T>` / `&Option<T>` /
                    // etc. as parameters yet (the current `classify_param_type`
                    // only handles `&[E]` and `&UserType`). Adapt by
                    // stripping the outer reference and passing `&name` at
                    // the call site, so the harness samples the owned form
                    // and the trusted body still receives a borrow.
                    let mut adapted = arg.clone();
                    let mut needs_borrow = false;
                    if let FnArgKind::Typed(adapted_pt) = &mut adapted.kind {
                        if let Type::Reference(rty) = adapted_pt.ty.as_ref() {
                            if let Type::Path(tp) = rty.elem.as_ref() {
                                if tp.qself.is_none()
                                    && !tp.path.segments.is_empty()
                                {
                                    let last = tp
                                        .path
                                        .segments
                                        .last()
                                        .unwrap()
                                        .ident
                                        .to_string();
                                    if matches!(
                                        last.as_str(),
                                        "Vec"
                                            | "Option"
                                            | "Result"
                                            | "HashMap"
                                            | "HashSet"
                                            | "Multiset"
                                    ) {
                                        // Strip the outer `&`.
                                        let inner = (*rty.elem).clone();
                                        adapted_pt.ty = Box::new(inner);
                                        needs_borrow = true;
                                    }
                                }
                            }
                        }
                    }
                    wrapper_inputs.push(adapted);
                    if let Some(name) = simple_pat_ident(&pt.pat) {
                        if needs_borrow {
                            call_args.push(verus_syn::parse_quote! { &#name });
                        } else {
                            call_args.push(verus_syn::parse_quote! { #name });
                        }
                    } else {
                        // Unnamed/complex pattern: we can't synthesize a
                        // call-arg ident.
                        return None;
                    }
                }
            }
        }
    }
    let _ = had_self; // currently unused but kept for clarity

    let body_call: Expr = Expr::Call(ExprCall {
        attrs: Vec::new(),
        func: Box::new(func_path),
        paren_token: Paren::default(),
        args: call_args.into_iter().collect(),
    });

    let block = Block {
        brace_token: Brace::default(),
        stmts: vec![Stmt::Expr(body_call, None)],
    };

    // Build the wrapper fn name. A unique counter wouldn't be stable across
    // engine emissions; instead, derive from the path's last segment plus a
    // hash of the full path so multiple wrappers don't collide.
    let last_seg_name = asp
        .path
        .segments
        .last()
        .map(|s| s.ident.to_string())
        .unwrap_or_else(|| "fn".to_string());
    let wrapper_ident = format_ident!("__pbt_assume_{}", last_seg_name);

    // Construct the SignatureSpec from the assume_spec's clauses.
    let spec = SignatureSpec {
        prover: None,
        requires: asp.requires.clone(),
        recommends: None,
        ensures: asp.ensures.clone(),
        default_ensures: asp.default_ensures.clone(),
        returns: asp.returns.clone(),
        decreases: None,
        invariants: asp.invariants.clone(),
        unwind: asp.unwind.clone(),
        with: None,
    };

    let sig = Signature {
        publish: verus_syn::Publish::Default,
        constness: None,
        asyncness: None,
        unsafety: None,
        abi: None,
        broadcast: None,
        mode: FnMode::Exec(ModeExec {
            exec_token: Token![exec](proc_macro2::Span::call_site()),
        }),
        fn_token: Token![fn](proc_macro2::Span::call_site()),
        ident: wrapper_ident,
        generics: asp.generics.clone(),
        paren_token: Paren::default(),
        inputs: wrapper_inputs,
        spec,
        variadic: None,
        output: asp.output.clone(),
    };

    // Carry the marker attributes through, plus stamp `#[verifier::external_body]`
    // so verification doesn't try to check the body matches the contract.
    let mut attrs = asp.attrs.clone();
    let ext_body: Attribute = verus_syn::parse_quote! {
        #[verifier::external_body]
    };
    if !attrs.iter().any(|a| {
        let p = a.path();
        p.segments.len() == 2
            && p.segments[0].ident == "verifier"
            && p.segments[1].ident == "external_body"
    }) {
        attrs.push(ext_body);
    }

    Some(verus_syn::ItemFn {
        attrs,
        vis: asp.vis.clone(),
        sig,
        block: Box::new(block),
        semi_token: None,
    })
}

/// Recover the receiver type for a method-shaped assume_specification path.
fn simple_pat_ident(pat: &verus_syn::Pat) -> Option<Ident> {
    use verus_syn::Pat;
    match pat {
        Pat::Ident(pi) => Some(pi.ident.clone()),
        Pat::Type(pt) => simple_pat_ident(&pt.pat),
        _ => None,
    }
}

/// Rewrite a marked trait impl `impl<T> Trait for X<T> { ... }` into an
/// inherent impl `impl<T> X<T> { ... }`, mangling each method name with the
/// trait's identifier (e.g. `view` becomes `View_view`) so multiple traits
/// implemented for the same Self type don't collide. Removes the trait
/// header in place. Best-effort: if the trait path is qualified, uses the
/// last segment as the prefix.
fn rewrite_trait_impl_to_inherent(im: &mut verus_syn::ItemImpl) {
    let trait_prefix = match &im.trait_ {
        Some((_, path, _)) => path
            .segments
            .last()
            .map(|s| s.ident.to_string())
            .unwrap_or_else(|| "_".to_string()),
        None => return,
    };
    // Drop the `Trait for` part.
    im.trait_ = None;
    // Mangle method names.
    for ii in &mut im.items {
        if let ImplItem::Fn(f) = ii {
            let new_name = format_ident!("{}_{}", trait_prefix, f.sig.ident);
            f.sig.ident = new_name;
        }
    }
}

/// Recover the receiver type for a method-shaped assume_specification path.
/// `Vec::<T>::push` -> `Vec::<T>`. `<Vec<T> as Clone>::clone` -> `Vec<T>`
/// (recovered from the qself).
fn recover_receiver_type(asp: &verus_syn::AssumeSpecification) -> Type {
    if let Some(qself) = &asp.qself {
        return (*qself.ty).clone();
    }
    // Drop the last path segment and reconstitute as a Type.
    let mut path = asp.path.clone();
    if path.segments.len() >= 2 {
        // Pop the last segment; rebuild the punctuated list because there's
        // no public API to flush trailing punctuation cleanly.
        let mut segs: Vec<verus_syn::PathSegment> =
            path.segments.iter().cloned().collect();
        segs.pop();
        path.segments = segs.into_iter().collect();
    }
    Type::Path(verus_syn::TypePath { qself: None, path })
}

/// Diagnostic for a body-less / `uninterp spec fn` reached from a `#[pbt]`
/// closure. The exec_spec engine cannot generate a runnable companion for
/// it, so the harness has nothing to evaluate the contract against.
fn uninterp_spec_message(qualified_name: &str) -> String {
    format!(
        "verus_pbt: the spec function `{name}` has no body (it is `uninterp` or otherwise \
body-less), so the engine cannot generate a runnable `exec_*` companion for it.\n\
\n\
A `#[pbt]` contract that reaches an uninterpreted spec fn cannot be property-tested: \
proptest needs an executable definition to evaluate the requires/ensures clauses against.\n\
\n\
Resolve it at the first applicable tier:\n\
\u{20} 1. Replace the `uninterp spec fn` with an `open spec fn` that has a body, when you can \
provide one;\n\
\u{20} 2. Or wrap the property test so it does not depend on the uninterp spec fn (rewrite \
the `#[pbt]` contract to use only spec fns with bodies);\n\
\u{20} 3. Or supply a trusted exec stub next to your `#[pbt]` fn:\n\
\u{20}      external_pbt_provide! {{ fn {name}(/* args */) -> /* ret */ {{ /* exec body */ }} }}\n\
\u{20}    The trusted body is `#[cfg(test)]`-only and never participates in verification.",
        name = qualified_name
    )
}

/// Whole-block preprocessing for `#[pbt]` and `#[pbt_provide]`. Returns true
/// if it rewrote `items`.
pub(crate) fn pbt_provide_preprocess(items: &mut Vec<Item>) -> bool {
    // Detect any markers up front.
    let mut any_marker = false;
    for item in items.iter() {
        if item_has_attr(item, "pbt_provide") || item_has_attr(item, "pbt") {
            any_marker = true;
        }
        if external_provide_names(item).is_some() {
            any_marker = true;
        }
        if let Item::Impl(im) = item {
            for ii in &im.items {
                if let ImplItem::Fn(f) = ii {
                    if impl_fn_has_attr(f, "pbt") || impl_fn_has_attr(f, "pbt_provide") {
                        any_marker = true;
                    }
                }
            }
        }
    }
    if !any_marker {
        return false;
    }

    // Pre-pass: rewrite each `assume_specification` item that carries a
    // `#[pbt]` or `#[pbt_provide]` marker into a synthesized exec wrapper fn
    // bearing the same marker. The wrapper has `#[verifier::external_body]`
    // (its body is a trusted call into the specified path) and the same
    // requires/ensures, so the rest of the pipeline can treat it as an
    // ordinary contract-bearing exec fn.
    for item in items.iter_mut() {
        if let Item::AssumeSpecification(_) = item {
            if item_has_attr(item, "pbt") || item_has_attr(item, "pbt_provide") {
                if let Item::AssumeSpecification(asp) = item {
                    if let Some(synthesized) = synthesize_pbt_wrapper_from_assume_spec(asp) {
                        *item = Item::Fn(synthesized);
                    }
                }
            }
        }
    }

    // Note: `int` / `nat` quantifier-bound variable types are handled
    // narrowly inside the harness's lifted-clause synthesis, not block-
    // wide. A block-wide rewrite would touch spec-fn bodies in a way that
    // breaks Verus's spec semantics (Seq::index expects `int`, etc.). The
    // engine still rejects `int`-bound quantifiers in spec-fn bodies; users
    // should use runtime-primitive bounds (`usize`, `u32`, ...) there.

    // Pre-pass: rewrite each marked trait impl `impl<T> Trait for X<T>` into
    // an inherent-shape impl block whose method names are mangled with the
    // trait's identifier (so multiple traits implemented for the same Self
    // type don't collide). After this pass the engine sees only
    // `impl X<T> { fn <Trait>_<method>(...) ... }`-style items.
    {
        // Compute per-index marker presence first so we don't have aliasing
        // borrows when we mutate the items in place.
        let marker_at: Vec<bool> = items
            .iter()
            .map(|item| {
                let item_marker = item_has_attr(item, "pbt_provide")
                    || item_has_attr(item, "pbt");
                let method_marker = match item {
                    Item::Impl(im) => im.items.iter().any(|ii| match ii {
                        ImplItem::Fn(f) => {
                            impl_fn_has_attr(f, "pbt") || impl_fn_has_attr(f, "pbt_provide")
                        }
                        _ => false,
                    }),
                    _ => false,
                };
                item_marker || method_marker
            })
            .collect();
        for (i, item) in items.iter_mut().enumerate() {
            if !marker_at[i] {
                continue;
            }
            if let Item::Impl(im) = item {
                if im.trait_.is_some() {
                    rewrite_trait_impl_to_inherent(im);
                }
            }
        }
    }

    // 0. Reject misplaced markers up front with actionable errors. We do this
    // BEFORE building the index so we can give precise placement guidance
    // ("put `#[pbt_provide]` on the struct/enum, free fn, or its method").
    let mut placement_errors: Vec<TokenStream2> = Vec::new();
    for item in items.iter() {
        // `#[pbt_provide]` on an item kind we can't fold.
        if item_has_attr(item, "pbt_provide") {
            if let Some(kind) = pbt_provide_unsupported_item_kind(item) {
                let span = item_attr_span(item, "pbt_provide")
                    .unwrap_or_else(proc_macro2::Span::call_site);
                let msg = format!(
                    "verus_pbt: `#[pbt_provide]` was placed on {kind}, but it can only be \
applied to:\n\
\u{20} - a `struct` or `enum` definition (folds the type and its inherent impls into the engine);\n\
\u{20} - a free `spec fn` definition (folds just that spec fn);\n\
\u{20} - a method inside a non-generic inherent `impl Type {{ ... }}` block (folds the surrounding impl).\n\
\n\
Move `#[pbt_provide]` to the top of the relevant `struct`/`enum`, free `spec fn`, \
or impl method instead.",
                    kind = kind
                );
                placement_errors.push(quote::quote_spanned! { span =>
                    const _: () = { compile_error!(#msg); };
                });
            }
        }
        // `#[pbt_provide]` / `#[pbt]` on a method inside an impl: previously
        // we rejected trait impls, but with feature-4 trait-impl folding the
        // pre-pass below pre-rewrites them into inherent-shape impls. Defer
        // the soundness check (associated-type projections, etc.) to the
        // engine, which will produce a precise diagnostic when it can't
        // lower a body. We still reject markers we can't make sense of:
        // none currently — every shape is folded.
        let _ = item;
    }
    if !placement_errors.is_empty() {
        let mut error_items: Vec<Item> = Vec::new();
        for ts in placement_errors {
            if let Ok(item) = verus_syn::parse2::<Item>(ts) {
                error_items.push(item);
            }
        }
        // Stripping markers on the existing items so they don't reach rustc as
        // unknown attributes alongside our diagnostics.
        let mut sanitized = std::mem::take(items);
        for item in &mut sanitized {
            strip_attr_item(item, "pbt_provide");
            strip_attr_item(item, "pbt"); strip_attr_item(item, "pbt_cov_mutate");
            if let Item::Impl(im) = item {
                for ii in &mut im.items {
                    if let ImplItem::Fn(f) = ii {
                        strip_attr_impl_fn(f, "pbt"); strip_attr_impl_fn(f, "pbt_cov_mutate");
                        strip_attr_impl_fn(f, "pbt_provide");
                    }
                }
            }
        }
        error_items.extend(sanitized);
        *items = error_items;
        return true;
    }

    let index = build_index(items);

    // 1. Seed sets:
    //   - engine_idxs: indices that MUST go into the engine block (markers
    //     and `external_pbt_provide!` invocations).
    //   - explicit_substs: the subst attached to each marker the user wrote.
    //   - generic_seeds: typed seeds for the generics-aware closure pass.
    //   - seed_idents: simpler ident-only seeds for the legacy closure (the
    //     name-only path is still used to keep diagnostics for free spec-fn
    //     calls cheap and unambiguous).
    let mut engine_idxs: HashSet<usize> = HashSet::new();
    let mut explicit_substs: HashMap<usize, Subst> = HashMap::new();
    // Names referenced by #[pbt] contracts → closure seeds (legacy).
    let mut seed_idents: HashSet<String> = HashSet::new();
    // Typed seeds for the generics-aware closure: (name, type-args, subst).
    let mut generic_seeds: Vec<(String, Vec<Type>, Subst)> = Vec::new();
    // Free-function calls in #[pbt] contracts (Step 1: tier-aware diagnostic).
    // These must resolve to a sibling free spec fn; if not, they're external
    // and need one of the resolution tiers.
    let mut pbt_free_calls: HashSet<String> = HashSet::new();
    // Names provided by `external_pbt_provide!` (Tier 4): these resolve, so
    // they suppress the Step-1 diagnostic.
    let mut externally_provided: HashSet<String> = HashSet::new();
    // Explicit #[pbt_provide] types contribute themselves + their impls.
    let mut explicit_provided_types: HashSet<String> = HashSet::new();

    for (i, item) in items.iter().enumerate() {
        // external_pbt_provide! { ... } → fold into the engine block (its
        // `exec_<name>` companions land in the harness module) and register
        // the provided names.
        if let Some(names) = external_provide_names(item) {
            engine_idxs.insert(i);
            for n in names {
                externally_provided.insert(n);
            }
        }
        // #[pbt_provide] on a type / free fn.
        if item_has_attr(item, "pbt_provide") {
            engine_idxs.insert(i);
            if let Some(s) = item_marker_subst(item, "pbt_provide") {
                explicit_substs.insert(i, s);
            }
            if let Some(n) = type_def_name(item) {
                explicit_provided_types.insert(n.to_string());
            }
            // #[pbt_provide] on a free fn: include it. If it's a free spec fn,
            // also recurse into its body so nested calls are folded too.
            if let Item::Fn(f) = item {
                collect_sig_idents(&f.sig, &mut seed_idents);
                if matches!(f.sig.mode, FnMode::Spec(..)) {
                    collect_block_idents(&f.block, &mut seed_idents);
                }
            }
        }
        // #[pbt] on a free fn: include the fn, seed closure from its contract.
        if item_has_attr(item, "pbt") {
            if let Item::Fn(f) = item {
                engine_idxs.insert(i);
                let pbt_subst = item_marker_subst(item, "pbt").unwrap_or_default();
                if !pbt_subst.is_empty() {
                    explicit_substs.insert(i, pbt_subst.clone());
                }
                collect_contract_idents(&f.sig, &mut seed_idents);
                collect_free_call_names(&f.sig, &mut pbt_free_calls);
                // Also seed the generics-aware walker.
                let mut typed = Vec::<(String, Vec<Type>)>::new();
                collect_contract_typed_refs(&f.sig, &mut typed);
                for (n, a) in typed {
                    generic_seeds.push((n, a, pbt_subst.clone()));
                }
            }
        }
        // #[pbt] / #[pbt_provide] on a method inside an impl: include the
        // whole impl block (only non-generic inherent ones — others were
        // rejected in step 0) and the impl's Self type. For #[pbt] also seed
        // from the method's contract; for #[pbt_provide] inside an impl, mark
        // the Self type as explicitly provided so its other inherent impl
        // blocks come in too.
        if let Item::Impl(im) = item {
            let mut impl_has_marker = false;
            // Subst priority for an impl with #[pbt] inside: explicit attr on
            // the impl item, else the first method-level subst we find.
            let impl_attr_subst = item_marker_subst(item, "pbt")
                .or_else(|| item_marker_subst(item, "pbt_provide"));
            let mut method_subst: Option<Subst> = None;
            for ii in &im.items {
                if let ImplItem::Fn(f) = ii {
                    if impl_fn_has_attr(f, "pbt") {
                        impl_has_marker = true;
                        if method_subst.is_none() {
                            method_subst = impl_fn_marker_subst(f, "pbt");
                        }
                        collect_contract_idents(&f.sig, &mut seed_idents);
                        collect_free_call_names(&f.sig, &mut pbt_free_calls);
                        let mut typed = Vec::<(String, Vec<Type>)>::new();
                        collect_contract_typed_refs(&f.sig, &mut typed);
                        let s_for_seed = impl_fn_marker_subst(f, "pbt")
                            .or_else(|| impl_attr_subst.clone())
                            .unwrap_or_default();
                        for (n, a) in typed {
                            generic_seeds.push((n, a, s_for_seed.clone()));
                        }
                    }
                    if impl_fn_has_attr(f, "pbt_provide") {
                        impl_has_marker = true;
                        if method_subst.is_none() {
                            method_subst = impl_fn_marker_subst(f, "pbt_provide");
                        }
                        // For a spec method, seed from its body so nested
                        // references are folded.
                        collect_sig_idents(&f.sig, &mut seed_idents);
                        if matches!(f.sig.mode, FnMode::Spec(..)) {
                            collect_block_idents(&f.block, &mut seed_idents);
                        }
                        if let Some(self_name) = inherent_impl_self_name(item) {
                            explicit_provided_types.insert(self_name.to_string());
                        }
                    }
                }
            }
            if impl_has_marker {
                engine_idxs.insert(i);
                if let Some(s) = impl_attr_subst.clone().or(method_subst) {
                    explicit_substs.insert(i, s);
                }
                if let Some(self_name) = inherent_impl_self_name(item) {
                    seed_idents.insert(self_name.to_string());
                    // Seed the generics-aware walker with the Self type and
                    // its type-args, picking up the impl's marker subst.
                    let s_for_seed = explicit_substs.get(&i).cloned().unwrap_or_default();
                    let self_args: Vec<Type> = if let Item::Impl(im) = item {
                        if let Type::Path(tp) = im.self_ty.as_ref() {
                            if tp.qself.is_none() && tp.path.segments.len() == 1 {
                                path_seg_type_args(&tp.path.segments[0].arguments)
                            } else {
                                Vec::new()
                            }
                        } else {
                            Vec::new()
                        }
                    } else {
                        Vec::new()
                    };
                    generic_seeds.push((self_name.to_string(), self_args, s_for_seed));
                }
            }
        }
    }

    // 1b. Tier-aware diagnostic: any free spec-fn call in a #[pbt] contract
    // that does NOT resolve to a sibling free fn is defined outside this block
    // and has no exec companion. Surface an actionable, path-inferred error
    // rather than letting the engine emit a broken `exec_<name>(..)` call.
    let unresolved: Vec<String> = pbt_free_calls
        .iter()
        .filter(|name| {
            !index.free_fns.contains_key(*name)
                && !is_builtin_free_spec_fn(name)
                && !externally_provided.contains(*name)
        })
        .cloned()
        .collect();
    if !unresolved.is_empty() {
        let use_index = build_use_index(items);
        let mut names: Vec<String> = unresolved;
        names.sort();
        let mut error_items: Vec<Item> = Vec::new();
        for name in &names {
            let inferred = infer_path_for(name, &use_index);
            let msg = unresolved_spec_fn_message(name, &inferred);
            let err_tokens: TokenStream2 = quote! {
                const _: () = { compile_error!(#msg); };
            };
            if let Ok(item) = verus_syn::parse2::<Item>(err_tokens) {
                error_items.push(item);
            }
        }
        // Replace the block with only the diagnostics. Keeping the user's
        // `#[pbt]` fn would cause a cascade: its contract calls the undefined
        // `exec_<name>` / spec fn, producing a second (E-coded) resolution
        // error that obscures our actionable message. The compile_error stops
        // the build cleanly with just the tier-aware guidance.
        *items = error_items;
        return true;
    }

    // 2. Pull in inherent impls of explicitly-provided types.
    for ty in &explicit_provided_types {
        if let Some(impl_idxs) = index.type_impls.get(ty) {
            for &ix in impl_idxs {
                engine_idxs.insert(ix);
            }
        }
    }

    // 3. Compute the closure from the seeds and union it in.
    let closure = compute_closure(seed_idents, items, &index);
    engine_idxs.extend(closure);

    // 3a. Generics-aware closure: produces per-item substs by walking type-
    // args along the call/reference graph from each `#[pbt]` callsite.
    let generic_closure = compute_closure_with_substs(generic_seeds, items, &index);
    // Merge: indices from the typed walker join engine_idxs.
    for &idx in generic_closure.chosen.keys() {
        engine_idxs.insert(idx);
    }
    // Build the final per-item subst map. Priority:
    //   1. explicit_substs (a marker on the item itself).
    //   2. generic_closure subst (inherited from a #[pbt] callsite).
    //   3. empty (item is non-generic).
    // Conflicts between (1) and (2), or among multiple (2)s, are surfaced as
    // diagnostics below.
    let mut item_substs: HashMap<usize, Subst> = HashMap::new();
    let mut item_subst_conflicts: Vec<InstantiationConflict> = generic_closure.conflicts;
    for (idx, generic_subst) in generic_closure.chosen {
        if let Some(explicit) = explicit_substs.get(&idx) {
            if !generic_subst.is_empty() && !explicit.agrees_with(&generic_subst) {
                let name = item_display_name(&items[idx]);
                item_subst_conflicts.push(InstantiationConflict {
                    item_idx: idx,
                    item_name: name,
                    first: explicit.clone(),
                    second: generic_subst,
                });
                item_substs.insert(idx, explicit.clone());
            } else {
                item_substs.insert(idx, explicit.clone());
            }
        } else {
            item_substs.insert(idx, generic_subst);
        }
    }
    // Items in engine_idxs but not in generic_closure.chosen: pick up explicit
    // marker subst if any (else default).
    for &idx in &engine_idxs {
        if !item_substs.contains_key(&idx) {
            if let Some(explicit) = explicit_substs.get(&idx) {
                item_substs.insert(idx, explicit.clone());
            } else {
                item_substs.insert(idx, Subst::default());
            }
        }
    }

    // 3a-conflicts: emit a diagnostic per disagreeing instantiation.
    if !item_subst_conflicts.is_empty() {
        let mut error_items: Vec<Item> = Vec::new();
        for c in &item_subst_conflicts {
            let span = items
                .get(c.item_idx)
                .map(|it| {
                    item_attr_span(it, "pbt_provide")
                        .or_else(|| item_attr_span(it, "pbt"))
                        .unwrap_or_else(proc_macro2::Span::call_site)
                })
                .unwrap_or_else(proc_macro2::Span::call_site);
            let msg = format!(
                "verus_pbt: `{name}` is reached by `#[pbt]` callsites with conflicting \
instantiations:\n\
\u{20} - first: {{ {first} }}\n\
\u{20} - second: {{ {second} }}\n\
\n\
Property-based testing currently emits one engine block per provider, so a single \
provider can't be folded under two different concrete instantiations. Either:\n\
\u{20} - factor the conflicting `#[pbt]` callsites into separate Verus blocks/files, or\n\
\u{20} - duplicate the provider with explicit `#[pbt_provide(...)]` markers that fix \
the instantiation locally.",
                name = c.item_name,
                first = c.first.render(),
                second = c.second.render(),
            );
            error_items.push(verus_syn::parse2::<Item>(quote::quote_spanned! { span =>
                const _: () = { compile_error!(#msg); };
            }).expect("conflict diagnostic must parse"));
        }
        // Strip markers and surface diagnostics + sanitized items.
        let mut sanitized = std::mem::take(items);
        for item in &mut sanitized {
            strip_attr_item(item, "pbt_provide");
            strip_attr_item(item, "pbt"); strip_attr_item(item, "pbt_cov_mutate");
            if let Item::Impl(im) = item {
                for ii in &mut im.items {
                    if let ImplItem::Fn(f) = ii {
                        strip_attr_impl_fn(f, "pbt"); strip_attr_impl_fn(f, "pbt_cov_mutate");
                        strip_attr_impl_fn(f, "pbt_provide");
                    }
                }
            }
        }
        error_items.extend(sanitized);
        *items = error_items;
        return true;
    }

    // 3a-unbound: any folded item with declared type-params and no subst (or
    // a subst that doesn't bind every param) means the user wrote a
    // generic `#[pbt]` or `#[pbt_provide]` without supplying enough
    // instantiation. Emit a tailored diagnostic per item.
    let mut unbound_errors: Vec<TokenStream2> = Vec::new();
    for &idx in &engine_idxs {
        let params = match index.type_params_by_idx.get(&idx) {
            Some(p) if !p.is_empty() => p.clone(),
            _ => continue,
        };
        let subst = item_substs.get(&idx).cloned().unwrap_or_default();
        let unbound_types: Vec<&Ident> = params
            .iter()
            .filter(|p| !subst.map.contains_key(&p.to_string()))
            .collect();
        let const_params = item_const_params(&items[idx]);
        let unbound_consts: Vec<&Ident> = const_params
            .iter()
            .filter(|p| !subst.consts.contains_key(&p.to_string()))
            .collect();
        if unbound_types.is_empty() && unbound_consts.is_empty() {
            continue;
        }
        let item = &items[idx];
        let name = item_display_name(item);
        let span = item_attr_span(item, "pbt_provide")
            .or_else(|| item_attr_span(item, "pbt"))
            .or_else(|| {
                if let Item::Impl(im) = item {
                    for ii in &im.items {
                        if let ImplItem::Fn(f) = ii {
                            if let Some(s) = impl_fn_attr_span(f, "pbt") {
                                return Some(s);
                            }
                            if let Some(s) = impl_fn_attr_span(f, "pbt_provide") {
                                return Some(s);
                            }
                        }
                    }
                }
                None
            })
            .unwrap_or_else(proc_macro2::Span::call_site);
        let unbound_str = unbound_types
            .iter()
            .map(|i| i.to_string())
            .chain(unbound_consts.iter().map(|i| format!("const {}", i)))
            .collect::<Vec<_>>()
            .join(", ");
        let suggestion = unbound_types
            .iter()
            .map(|i| {
                let t = suggest_default_type(i, &[]);
                format!("{} = {}", i, quote!(#t))
            })
            .chain(
                unbound_consts
                    .iter()
                    .map(|i| format!("{} = 4", i)),
            )
            .collect::<Vec<_>>()
            .join(", ");
        let attr_kind = if item_has_attr(item, "pbt_provide") {
            "pbt_provide"
        } else if item_has_attr(item, "pbt") {
            "pbt"
        } else {
            "pbt"
        };
        let msg = format!(
            "verus_pbt: `{name}` is generic in <{unbound}> but no concrete instantiation \
was found.\n\
\n\
Property-based testing needs concrete types to sample. Either:\n\
\u{20} - put `#[{attr_kind}({suggestion})]` on this item to fix an instantiation \
explicitly, or\n\
\u{20} - attach a `#[pbt]` to a (non-generic, or already-instantiated) function whose \
contract reaches `{name}`, and the instantiation will be inherited automatically.",
            name = name,
            unbound = unbound_str,
            attr_kind = attr_kind,
            suggestion = suggestion,
        );
        unbound_errors.push(quote::quote_spanned! { span =>
            const _: () = { compile_error!(#msg); };
        });
    }
    if !unbound_errors.is_empty() {
        let mut error_items: Vec<Item> = Vec::new();
        for ts in unbound_errors {
            if let Ok(item) = verus_syn::parse2::<Item>(ts) {
                error_items.push(item);
            }
        }
        let mut sanitized = std::mem::take(items);
        for item in &mut sanitized {
            strip_attr_item(item, "pbt_provide");
            strip_attr_item(item, "pbt"); strip_attr_item(item, "pbt_cov_mutate");
            if let Item::Impl(im) = item {
                for ii in &mut im.items {
                    if let ImplItem::Fn(f) = ii {
                        strip_attr_impl_fn(f, "pbt"); strip_attr_impl_fn(f, "pbt_cov_mutate");
                        strip_attr_impl_fn(f, "pbt_provide");
                    }
                }
            }
        }
        error_items.extend(sanitized);
        *items = error_items;
        return true;
    }

    // 3b. Diagnostic: any uninterp spec fn (or body-less spec fn) folded into
    // the engine block has no body the engine can lower into a runnable
    // companion. Surface a tailored error rather than letting `exec_spec`
    // produce a "missing return expression" or "unsupported statement" error
    // on the empty body.
    let mut uninterp_errors: Vec<TokenStream2> = Vec::new();
    for &idx in &engine_idxs {
        let item = &items[idx];
        match item {
            Item::Fn(f) if is_uninterp_spec_fn(f) => {
                let span = f.sig.ident.span();
                let name = f.sig.ident.to_string();
                let msg = uninterp_spec_message(&name);
                uninterp_errors.push(quote::quote_spanned! { span =>
                    const _: () = { compile_error!(#msg); };
                });
            }
            Item::Impl(im) => {
                for ii in &im.items {
                    if let ImplItem::Fn(f) = ii {
                        if impl_fn_is_uninterp_spec(f) {
                            let span = f.sig.ident.span();
                            let owner = inherent_impl_self_name(item)
                                .map(|n| n.to_string())
                                .unwrap_or_else(|| "?".to_string());
                            let qualified = format!("{}::{}", owner, f.sig.ident);
                            let msg = uninterp_spec_message(&qualified);
                            uninterp_errors.push(quote::quote_spanned! { span =>
                                const _: () = { compile_error!(#msg); };
                            });
                        }
                    }
                }
            }
            _ => {}
        }
    }
    if !uninterp_errors.is_empty() {
        let mut error_items: Vec<Item> = Vec::new();
        for ts in uninterp_errors {
            if let Ok(item) = verus_syn::parse2::<Item>(ts) {
                error_items.push(item);
            }
        }
        // Strip markers from the existing items so they don't reach rustc as
        // unknown attributes alongside our diagnostics, and don't fold into
        // the engine block (which would re-trigger the engine error).
        let mut sanitized = std::mem::take(items);
        for item in &mut sanitized {
            strip_attr_item(item, "pbt_provide");
            strip_attr_item(item, "pbt"); strip_attr_item(item, "pbt_cov_mutate");
            if let Item::Impl(im) = item {
                for ii in &mut im.items {
                    if let ImplItem::Fn(f) = ii {
                        strip_attr_impl_fn(f, "pbt"); strip_attr_impl_fn(f, "pbt_cov_mutate");
                        strip_attr_impl_fn(f, "pbt_provide");
                    }
                }
            }
        }
        error_items.extend(sanitized);
        *items = error_items;
        return true;
    }

    // 4. Partition: chosen indices (marker-stripped, substituted) → engine
    // block; rest stay. Per-item substitutions come from `item_substs`,
    // computed by combining explicit markers and the generics-aware closure.
    let mut engine_items: Vec<Item> = Vec::new();
    let mut remaining: Vec<Item> = Vec::new();
    // Track which sibling types had their type-params stripped, so we can
    // also strip type-args from in-block references to them. e.g. once
    // `Cell<V>` becomes `Cell`, every `Cell<u64>` in fields/impls becomes
    // `Cell` too.
    let mut stripped_type_names: HashSet<String> = HashSet::new();
    for (i, item) in items.iter().enumerate() {
        if engine_idxs.contains(&i) {
            if let Some(s) = item_substs.get(&i) {
                if !s.is_empty() {
                    if let Some(name) = type_def_name(item) {
                        stripped_type_names.insert(name.to_string());
                    }
                }
            }
        }
    }
    for (i, mut item) in items.drain(..).enumerate() {
        if engine_idxs.contains(&i) {
            strip_attr_item(&mut item, "pbt_provide");
            strip_attr_item(&mut item, "pbt");
            if let Item::Impl(im) = &mut item {
                for ii in &mut im.items {
                    if let ImplItem::Fn(f) = ii {
                        strip_attr_impl_fn(f, "pbt");
                        strip_attr_impl_fn(f, "pbt_provide");
                        // NOTE: deliberately do NOT strip `pbt_cov_mutate`
                        // from items going to the engine. The verus_pbt
                        // classify step inside the engine block needs the
                        // attribute to capture metadata; it strips after
                        // capture.
                    }
                }
            }
            // Apply the resolved substitution before handing the item to the
            // engine. For non-generic items this is a no-op.
            if let Some(s) = item_substs.get(&i) {
                if !s.is_empty() {
                    substitute_item(&mut item, s);
                }
            }
            // Strip type-args from references to monomorphized siblings.
            strip_type_args_for_names(&mut item, &stripped_type_names);
            engine_items.push(item);
        } else {
            // Defensive: a stray `#[pbt]` / `#[pbt_provide]` on an item we did
            // not fold (e.g. an unsupported item kind) must still be stripped
            // so it never reaches rustc as an unknown attribute.
            strip_attr_item(&mut item, "pbt_provide");
            strip_attr_item(&mut item, "pbt");
            if let Item::Impl(im) = &mut item {
                for ii in &mut im.items {
                    if let ImplItem::Fn(f) = ii {
                        strip_attr_impl_fn(f, "pbt"); strip_attr_impl_fn(f, "pbt_cov_mutate");
                        strip_attr_impl_fn(f, "pbt_provide");
                    }
                }
            }
            remaining.push(item);
        }
    }

    // If no items were folded despite a marker being present, the markers
    // were on unsupported item kinds. We've already stripped them; emitting
    // an empty engine block would be harmless but pointless, so skip it.
    if engine_items.is_empty() {
        *items = remaining;
        return true;
    }
    // 5. Fold the engine group into one verus_pbt_unverified! invocation.
    let vstd = crate::syntax::Vstd(proc_macro2::Span::call_site());
    let macro_call: TokenStream2 = quote! {
        #vstd::contrib::verus_pbt::verus_pbt_unverified! {
            #(#engine_items)*
        }
    };
    let macro_item: Item =
        verus_syn::parse2(macro_call).expect("pbt: synthesized macro item must parse");
    remaining.push(macro_item);

    *items = remaining;
    true
}
