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
use quote::quote;
use std::collections::{HashMap, HashSet};
use verus_syn::visit::Visit;
use verus_syn::{
    Attribute, Expr, ExprPath, FnMode, Ident, ImplItem, Item, PathArguments, Type, UseTree,
};

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
        _ => None,
    }
}

fn item_attrs(item: &Item) -> Option<&Vec<Attribute>> {
    match item {
        Item::Enum(i) => Some(&i.attrs),
        Item::Struct(i) => Some(&i.attrs),
        Item::Impl(i) => Some(&i.attrs),
        Item::Fn(i) => Some(&i.attrs),
        _ => None,
    }
}

fn item_has_attr(item: &Item, name: &str) -> bool {
    item_attrs(item).map_or(false, |attrs| attrs.iter().any(|a| attr_is(a, name)))
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
}

fn build_index(items: &[Item]) -> SiblingIndex {
    let mut type_defs = HashMap::new();
    let mut type_impls: HashMap<String, Vec<usize>> = HashMap::new();
    let mut free_fns = HashMap::new();
    let mut method_owners: HashMap<String, HashSet<String>> = HashMap::new();

    for (i, item) in items.iter().enumerate() {
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

    SiblingIndex { type_defs, type_impls, free_fns, method_owners }
}

// ---------------------------------------------------------------------------
// Closure computation
// ---------------------------------------------------------------------------

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

/// Collect identifiers referenced by a free fn (body if spec + signature).
fn collect_fn_spec_idents(item: &Item, out: &mut HashSet<String>) {
    if let Item::Fn(f) = item {
        collect_sig_idents(&f.sig, out);
        if matches!(f.sig.mode, FnMode::Spec(..)) {
            collect_block_idents(&f.block, out);
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

    let index = build_index(items);

    // 1. Seed set: indices that MUST go into the engine block.
    let mut engine_idxs: HashSet<usize> = HashSet::new();
    // Names referenced by #[pbt] contracts → closure seeds.
    let mut seed_idents: HashSet<String> = HashSet::new();
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
            if let Some(n) = type_def_name(item) {
                explicit_provided_types.insert(n.to_string());
            }
        }
        // #[pbt] on a free fn: include the fn, seed closure from its contract.
        if item_has_attr(item, "pbt") {
            if let Item::Fn(f) = item {
                engine_idxs.insert(i);
                collect_contract_idents(&f.sig, &mut seed_idents);
                collect_free_call_names(&f.sig, &mut pbt_free_calls);
            }
        }
        // #[pbt] on a method inside an impl: include the whole impl block,
        // and the impl's Self type; seed from the method's contract.
        if let Item::Impl(im) = item {
            let mut impl_has_pbt = false;
            for ii in &im.items {
                if let ImplItem::Fn(f) = ii {
                    if impl_fn_has_attr(f, "pbt") {
                        impl_has_pbt = true;
                        collect_contract_idents(&f.sig, &mut seed_idents);
                        collect_free_call_names(&f.sig, &mut pbt_free_calls);
                    }
                }
            }
            if impl_has_pbt {
                engine_idxs.insert(i);
                if let Some(self_name) = inherent_impl_self_name(item) {
                    seed_idents.insert(self_name.to_string());
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

    // 4. Partition: chosen indices (marker-stripped) → engine block; rest stay.
    let mut engine_items: Vec<Item> = Vec::new();
    let mut remaining: Vec<Item> = Vec::new();
    for (i, mut item) in items.drain(..).enumerate() {
        if engine_idxs.contains(&i) {
            strip_attr_item(&mut item, "pbt_provide");
            strip_attr_item(&mut item, "pbt");
            if let Item::Impl(im) = &mut item {
                for ii in &mut im.items {
                    if let ImplItem::Fn(f) = ii {
                        strip_attr_impl_fn(f, "pbt");
                        strip_attr_impl_fn(f, "pbt_provide");
                    }
                }
            }
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
                        strip_attr_impl_fn(f, "pbt");
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
