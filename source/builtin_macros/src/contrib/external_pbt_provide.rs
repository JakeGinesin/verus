//! `external_pbt_provide!` — Tier 4 trusted exec stub for property-based
//! testing of spec functions defined **outside** the current `verus!` block
//! (in another crate you don't control, e.g. `vstd`, or a public spec fn whose
//! body isn't recoverable).
//!
//! ## What it is for
//!
//! `#[pbt]` generates a proptest harness that evaluates a contract by calling
//! an `exec_<name>` companion for every spec fn the contract mentions. For
//! spec fns defined *in the same block* the companion is generated
//! automatically by the engine. For spec fns defined elsewhere there is no
//! companion — and across crates nothing can synthesize one. Tiers 1–3 cover
//! the cases that *can* be resolved automatically; `external_pbt_provide!` is
//! the explicit escape hatch when none apply: the developer supplies a trusted
//! executable body once, next to the `#[pbt]` function.
//!
//! ## Shape
//!
//! ```ignore
//! verus! {
//!     external_pbt_provide! {
//!         // Signature uses the SPEC types of the external spec fn; the body
//!         // is ordinary exec Rust operating on their lowered exec forms
//!         // (Seq<T> -> &[T], Map<K,V> -> &HashMap<K,V>, Set<T> -> &HashSet<T>,
//!         //  Multiset<T> -> &ExecMultiset<T>, user types -> &ExecUser, etc.).
//!         fn is_sorted(s: Seq<i64>) -> bool {
//!             s.windows(2).all(|w| w[0] <= w[1])
//!         }
//!     }
//!
//!     #[pbt]
//!     fn sort_it(s: &[i64]) -> (r: Vec<i64>)
//!         ensures is_sorted(r.deep_view()),
//!     { /* ... */ }
//! }
//! ```
//!
//! The declaration must sit in the same `verus!` block as the `#[pbt]` fn so
//! the whole-block `#[pbt]` pass can (a) treat `is_sorted` as resolved — it
//! will not emit the Tier-aware "external spec fn" diagnostic — and (b) thread
//! the provided name into the harness so `is_sorted(..)` lowers to
//! `exec_is_sorted(..)`. The trusted body is `#[cfg(test)]`-only (it lives in
//! the generated harness module), so it never participates in verification.

use proc_macro2::TokenStream as TokenStream2;
use quote::quote;
use verus_syn::parse::{Parse, ParseStream};
use verus_syn::{Error, FnArgKind, Ident, ItemFn, ReturnType};

use super::exec_spec::{compile_type, TypeKind};

/// Parsed `external_pbt_provide! { fn ...; fn ...; }` body: a sequence of
/// trusted exec stub functions written with spec-level signatures.
pub(crate) struct ExternalProvide {
    pub fns: Vec<ItemFn>,
}

impl Parse for ExternalProvide {
    fn parse(input: ParseStream) -> verus_syn::parse::Result<ExternalProvide> {
        let mut fns = Vec::new();
        while !input.is_empty() {
            fns.push(input.parse::<ItemFn>()?);
        }
        Ok(ExternalProvide { fns })
    }
}

/// The names of the spec fns provided by an `external_pbt_provide!` body, used
/// by the `#[pbt]` whole-block pass to (a) suppress the Tier-aware diagnostic
/// and (b) register them as harness-renamable spec fns.
pub(crate) fn provided_names(tokens: TokenStream2) -> Vec<String> {
    match verus_syn::parse2::<ExternalProvide>(tokens) {
        Ok(p) => p.fns.iter().map(|f| f.sig.ident.to_string()).collect(),
        Err(_) => Vec::new(),
    }
}

/// Compile a single trusted stub into its `exec_<name>` companion. Parameters
/// are lowered to their exec *reference* form and the return type to its exec
/// *owned* form — exactly mirroring what the engine emits for an in-block spec
/// fn — so the harness's `exec_<name>(<stripped deep_view args>)` call type-
/// checks identically whether the spec fn is in-block or externally provided.
fn emit_one(f: &ItemFn) -> Result<TokenStream2, Error> {
    if let Some(recv) = f.sig.inputs.iter().find_map(|p| match &p.kind {
        FnArgKind::Receiver(r) => Some(r),
        _ => None,
    }) {
        return Err(Error::new_spanned(
            recv,
            "external_pbt_provide! supports only free functions (no `self` receiver); \
             a method on an external type should be provided as a free fn taking the \
             receiver explicitly",
        ));
    }

    let spec_name = &f.sig.ident;
    let exec_name = Ident::new(&format!("exec_{spec_name}"), spec_name.span());

    let mut params: Vec<TokenStream2> = Vec::new();
    for input in &f.sig.inputs {
        if let FnArgKind::Typed(pt) = &input.kind {
            let pat = &pt.pat;
            let ty = compile_type(&pt.ty, TypeKind::Ref)?;
            params.push(quote! { #pat: #ty });
        }
    }

    let ret = match &f.sig.output {
        ReturnType::Default => quote! { () },
        ReturnType::Type(_, _, _, ty) => {
            let lowered = compile_type(ty, TypeKind::Owned)?;
            quote! { #lowered }
        }
    };

    let body = &f.block;

    Ok(quote! {
        #[allow(dead_code)]
        #[allow(unused_variables)]
        fn #exec_name(#(#params),*) -> #ret #body
    })
}

/// Emit the `exec_<name>` companions for every stub in an
/// `external_pbt_provide!` body. Returned tokens are placed inside the
/// generated `#[cfg(test)]` harness module by `verus_pbt::expand`, so they are
/// invisible to verification and reachable by the harness without any `super::`
/// qualification.
pub(crate) fn emit_companions(tokens: TokenStream2) -> Result<TokenStream2, Error> {
    let parsed = verus_syn::parse2::<ExternalProvide>(tokens)?;
    let mut out = TokenStream2::new();
    for f in &parsed.fns {
        out.extend(emit_one(f)?);
    }
    Ok(out)
}
