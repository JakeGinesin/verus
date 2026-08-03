#!/usr/bin/env python3
"""Per-site classification of vstd's trusted-assumption sites.

Builds on the scan in scan_pbt.py, but with a *strict* attachment rule
for #[pbt] (only the contiguous attribute/comment block around the item
counts, so an annotation on a neighboring item is never miscounted), and
an explicit per-site rules database assigning every uncovered site a
status and reason.

Statuses:
  DIRECT      annotated with #[pbt] (a real vstd trusted site)
  HARNESS     an added pbt_* wrapper fn carrying #[pbt] (test evidence,
              not itself a trusted vstd claim)
  WRAPPER     uncovered textually, but its contract is restated by a
              named composite wrapper harness
  TODO        coverable with the current engine; not yet done
  ENGINE      needs verus-pbt engine work to cover
  DESCOPED    concurrency/async: sequential replay could check value
              semantics, but the interesting claims are concurrent
  UNTESTABLE  the contract claims nothing evaluable by construction
  INFRA       not a trusted vstd claim (exec_spec shims, pbt helpers,
              scanner false positives)

Usage: python3 tools/classify_pbt.py [--sites] [path-to-vstd]
  --sites   also dump every non-covered site with its classification
"""
import os, re, sys, collections

DEFAULT_ROOT = os.path.normpath(
    os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "source", "vstd")
)

# ---------------------------------------------------------------------------
# Strict scanner
# ---------------------------------------------------------------------------

def is_attr(l):
    return l.lstrip().startswith("#[")

def is_comment(l):
    return l.lstrip().startswith("//")

def scan_file(path):
    with open(path) as f:
        lines = f.readlines()
    n = len(lines)
    out = []
    i = 0
    while i < n:
        ls = lines[i].rstrip()
        stripped = ls.lstrip()
        kind = ident = None
        item_line = i
        if re.search(r"\baxiom fn \w+", ls) and not is_comment(ls):
            # `(broadcast) axiom fn name(...)` — a trusted axiom declaration.
            kind = "axiom"
            acc = []
            for x in lines[i : min(i + 15, n)]:
                acc.append(x.strip())
                if x.rstrip().endswith(";") or x.rstrip().endswith("{"):
                    break
            ident = " ".join(acc)[:420]
        elif re.search(r"\bproof fn \w+", ls) and not is_comment(ls) and "axiom fn" not in ls:
            # `proof fn` whose body admits: same trust level as an axiom.
            # Heuristic body scan: forward until the next item header.
            has_admit = False
            for j in range(i, min(i + 45, n)):
                l2 = lines[j]
                if j > i and re.match(r"\s*(pub |#\[|macro_rules|impl |struct |enum )?\s*(broadcast )?(proof |axiom |exec |open spec |spec )?fn \w+", l2) and "fn" in l2 and j != i:
                    if re.search(r"\bfn \w+", l2) and not is_comment(l2):
                        break
                if "admit()" in l2 or "admit ()" in l2:
                    has_admit = True
                    break
            if has_admit:
                kind = "axiom"
                acc = []
                for x in lines[i : min(i + 15, n)]:
                    acc.append(x.strip())
                    if x.rstrip().endswith("{"):
                        break
                ident = " ".join(acc)[:420]
        if kind is None and ("pub assume_specification" in ls or "assume_specification[" in ls):
            if not is_comment(ls):
                kind = "assume_spec"
                # an assume_specification item ends at the first *line*
                # ending with ';' (a mid-line ';' can be type-level [T; N])
                acc = []
                for x in lines[i : min(i + 25, n)]:
                    acc.append(x.strip())
                    if x.rstrip().endswith(";"):
                        break
                ident = " ".join(acc)[:420]
        elif "#[verifier::external_body]" in ls and is_attr(ls):
            for j in range(i + 1, min(i + 16, n)):
                nxt = lines[j].rstrip()
                s2 = nxt.lstrip()
                if not s2 or is_comment(nxt) or is_attr(nxt):
                    continue
                m = re.match(
                    r"(pub\s+(\([^)]+\)\s+)?)?(unsafe\s+)?(exec\s+)?fn\s+(\w+)", s2
                )
                if m:
                    kind = "external_body"
                    ident = " ".join(
                        x.strip() for x in lines[j : min(j + 6, n)]
                    )[:220]
                    item_line = j
                break
        if kind is not None:
            # strict attachment: walk back from the *attribute block* start
            has_pbt = False
            k = i - 1
            while k >= 0 and (is_attr(lines[k]) or is_comment(lines[k]) or "#[pbt" in lines[k]):
                if not is_comment(lines[k]) and "#[pbt" in lines[k]:
                    has_pbt = True
                k -= 1
            if "#[pbt" in lines[i]:
                has_pbt = True
            # forward through the contiguous attribute block
            k = i + 1
            while k < n and (is_attr(lines[k]) or is_comment(lines[k])):
                if not is_comment(lines[k]) and "#[pbt" in lines[k]:
                    has_pbt = True
                k += 1
            out.append((i + 1, kind, has_pbt, ident))
        i += 1
    return out

# ---------------------------------------------------------------------------
# Rules database: (file suffix, regex over the flattened ident, status, note)
# First match wins. Applied only to sites without an attached #[pbt].
# ---------------------------------------------------------------------------

R = [
    # ---- infrastructure -------------------------------------------------
    ("contrib/exec_spec/", r".", "INFRA", "verus-pbt exec-spec shim (test machinery, not a vstd claim)"),
    ("", r"^fn pbt_\w+|^pub fn pbt_\w+", "INFRA", "pbt wrapper helper (build/matches replay fns)"),

    # ---- axioms (checked before the file catch-alls; idents contain
    # ---- "axiom fn" / "proof fn") ---------------------------------------
    # ghost-only content: resolution, decreases, tracked tokens, prophecy
    ("", r"(axiom|proof) fn \w*(has_resolved|decreases)", "UNTESTABLE", "ghost resolution/termination axiom — no runtime content"),
    ("", r"(axiom|proof) fn \w*ext_equal", "UNTESTABLE", "extensionality axiom — equality of spec objects is not exec-observable"),
    ("layout.rs", r"axiom fn (layout_of_|align_properties)", "WRAPPER", "pbt_layout_*/pbt_align_properties harnesses evaluate the axiom claims at concrete types"),
    ("std_specs/range.rs", r"proof fn \$axiom", "WRAPPER", "pbt_range_next_* per-width composites check the 12 spec_range_next admits"),
    ("std_specs/range.rs", r"axiom fn axiom_spec_range_inclusive_new", "WRAPPER", "pinned via fresh-construction composites (bounds/contains)"),
    ("std_specs/nonzero.rs", r"axiom fn axiom_", "WRAPPER", "view pinned through new in the pbt_nonzero_* composites"),
    ("std_specs/control_flow.rs", r"proof fn spec_from_blanket_identity", "WRAPPER", "composed into pbt_result_from_residual (identity From at F = E)"),
    ("/vstd/slice.rs", r"axiom fn axiom_spec_len", "WRAPPER", "pbt_slice_len composite"),
    ("/vstd/slice.rs", r"axiom fn axiom_(slice_get_usize|spec_slice_update|spec_slice_index)", "WRAPPER", "exercised by the direct-labeled slice exec twins (slice_index_get/slice_update/slice_subrange)"),
    ("array.rs", r"axiom fn axiom_spec_array_as_slice", "WRAPPER", "pbt_array_as_slice composite"),
    ("array.rs", r"axiom fn axiom_spec_array_fill_for_copy_type", "WRAPPER", "pbt_array_fill_for_copy_types composite"),
    ("array.rs", r"axiom fn axiom_spec_array_update", "WRAPPER", "pbt_array_update (exec assignment vs elementwise view update)"),
    ("string.rs", r"axiom fn axiom_str_literal_", "UNTESTABLE", "pins the uninterp strslice_len/get_char (definitional for the verifier's literal encoding; no exec consumer exists)"),
    ("string.rs", r"proof fn to_string_from_display_ensures_for_str", "ENGINE", "routes through the uninterp Display-ensures model (to_string generic gap)"),
    ("string.rs", r"proof fn axiom_spec_iter", "ENGINE", "iterator spec model (descoped)"),
    ("array.rs", r"proof fn axiom_spec_array_iter", "ENGINE", "iterator spec model (descoped)"),
    ("hash_map.rs", r"axiom fn axiom_hash_map_with_view_spec_len|axiom fn axiom_string_hash_map_spec_len", "WRAPPER", "len pinned in the replay+probe composites"),
    ("hash_set.rs", r"axiom fn axiom_hash_set_with_view_spec_len|axiom fn axiom_string_hash_set_spec_len", "WRAPPER", "len pinned in the replay+probe composites"),
    ("std_specs/vec.rs", r"proof fn axiom_spec_len", "WRAPPER", "pbt_vec_len composite"),
    ("std_specs/vec.rs", r"proof fn axiom_spec_into_iter", "ENGINE", "iterator spec model (descoped)"),
    ("std_specs/vecdeque.rs", r"proof fn axiom_spec_len", "WRAPPER", "pbt_vecdeque_len composite"),
    ("std_specs/vecdeque.rs", r"proof fn axiom_spec_iter", "ENGINE", "iterator spec model (descoped)"),
    ("std_specs/slice.rs", r"proof fn axiom_spec_slice_iter", "ENGINE", "iterator spec model (descoped)"),
    ("std_specs/hash.rs", r"proof fn axiom_\w+_obeys_hash_table_key_model|proof fn axiom_random_state_builds_valid_hashers", "UNTESTABLE", "uninterp guard predicate (trusted hashing-determinism assumption; nothing evaluable)"),
    ("std_specs/hash.rs", r"proof fn axiom_(maps|set)_deref_key_", "WRAPPER", "inlined at Key = Q = u32 in the pbt_hash_* mutator composites"),
    ("std_specs/hash.rs", r"proof fn axiom_(maps|set)_box_key_|proof fn axiom_(map|set)_(box|contains_box)", "WRAPPER", "pbt_hash_box_key_ops (Key = Box<u32>, Q = u32)"),
    ("std_specs/hash.rs", r"proof fn axiom_(spec_hash_map_len|spec_hash_set_len)", "WRAPPER", "pbt_hash_map_len/pbt_hash_set_len composites"),
    ("std_specs/hash.rs", r"proof fn axiom_spec_(hash_map_iter|hash_keys_iter|keys_iter|values_iter|hash_set_iter)", "ENGINE", "iterator spec model (descoped)"),
    ("std_specs/hash.rs", r"(axiom|proof) fn ", "UNTESTABLE", "ghost entry-resolution/deepview axiom"),
    ("std_specs/btree.rs", r"proof fn axiom_(key_obeys_cmp_spec_meaning|increasing_seq_meaning)", "UNTESTABLE", "uninterp guard predicate (trusted comparator-determinism assumption)"),
    ("std_specs/btree.rs", r"(axiom|proof) fn axiom_\w*(deref_key|removed_key|inserted_key|contains_deref)", "WRAPPER", "inlined at Key = Q = u32 in the pbt_btree_* mutator composites"),
    ("std_specs/btree.rs", r"(axiom|proof) fn axiom_\w*box", "WRAPPER", "pbt_btree_box_key_ops (Key = Box<u32>, Q = u32)"),
    ("std_specs/btree.rs", r"(axiom|proof) fn axiom_spec_btree_(map|set)_len", "WRAPPER", "pbt_btree_*_len composites"),
    ("std_specs/btree.rs", r"(axiom|proof) fn axiom_\w*(iter|keys|values)", "ENGINE", "iterator spec model (descoped)"),
    ("std_specs/btree.rs", r"(axiom|proof) fn ", "UNTESTABLE", "ghost deepview/borrow axiom"),
    ("std_specs/option.rs", r"axiom fn tracked_take", "UNTESTABLE", "tracked ghost token operation"),
    ("std_specs/iter.rs", r"(axiom|proof) fn ", "ENGINE", "iterator module descoped (deep prophetic model)"),
    ("raw_ptr.rs", r"(axiom|proof) fn (is_nonnull|is_aligned|is_disjoint)", "WRAPPER", "pbt_alloc_nonnull_aligned_disjoint (restated over real allocations)"),
    ("raw_ptr.rs", r"(axiom|proof) fn null\b", "WRAPPER", "pbt_expose_provenance_roundtrip exercises exposed provenance; null provenance is its ghost base case"),
    ("raw_ptr.rs", r"(axiom|proof) fn (leak_contents|points_to|empty|split|join|into_typed|into_raw)", "UNTESTABLE", "ghost permission transformation (proof-mode domain bookkeeping, no runtime state)"),
    ("raw_ptr.rs", r"(axiom|proof) fn (axiom_ptr_mut_from_data|ptrs_mut_eq)", "UNTESTABLE", "view-inverse axiom over the uninterp pointer model (definitional, no exec observation)"),
    ("raw_ptr.rs", r"(axiom|proof) fn ", "UNTESTABLE", "ghost pointer-model axiom"),
    ("map.rs", r"axiom fn tracked_", "UNTESTABLE", "tracked ghost map token operation — no runtime state"),
    ("map.rs", r"(axiom|proof) fn ", "ENGINE", "spec-theory axiom; probed 2026-07-31 — #[pbt_axiom] from *inside vstd* needs engine work (in-crate routed-carrier lowering, Map params, spec constructors empty/singleton)"),
    ("multiset.rs", r"(axiom|proof) fn \w*(choose|filter|dom_finite)", "UNTESTABLE", "choice/finiteness axiom — not exec-observable"),
    ("multiset.rs", r"(axiom|proof) fn ", "ENGINE", "spec-theory axiom; probed 2026-07-31 — #[pbt_axiom] from *inside vstd* needs engine work (in-crate routed-carrier lowering, spec constructors empty/singleton)"),
    ("/vstd/set.rs", r"axiom fn axiom_is_finite", "UNTESTABLE", "finiteness axiom — not exec-observable"),
    ("/vstd/set.rs", r"(axiom|proof) fn ", "ENGINE", "spec-theory axiom; same in-crate routing gap as multiset/map (probed 2026-07-31)"),
    ("/vstd/seq.rs", r"(axiom|proof) fn ", "UNTESTABLE", "ghost decreases axiom"),
    ("iset", r"(axiom|proof) fn ", "UNTESTABLE", "infinite-set theory — no finite exec model"),
    ("imap.rs", r"(axiom|proof) fn ", "UNTESTABLE", "infinite-map theory — no finite exec model"),
    ("function.rs", r"(axiom|proof) fn ", "UNTESTABLE", "proof-fn/FnOnce call-contract axioms — spec-level closure theory"),
    ("modes.rs", r"(axiom|proof) fn ", "UNTESTABLE", "ghost/tracked mode coercion axioms"),
    ("resource/", r"(axiom|proof) fn ", "UNTESTABLE", "abstract resource-algebra laws over trait carriers (no concrete exec model)"),
    ("thread.rs", r"(axiom|proof) fn ", "UNTESTABLE", "ghost thread-identity tokens"),
    ("proph.rs", r"(axiom|proof) fn ", "UNTESTABLE", "prophecy resolution — ghost event"),
    ("invariant.rs", r"(axiom|proof) fn ", "UNTESTABLE", "ghost invariant tokens"),
    ("pervasive.rs", r"(axiom|proof) fn (assume|proof_from_false)", "UNTESTABLE", "requires-false / assume primitive — unreachable by contract"),
    ("cell/pcell.rs", r"axiom fn is_exclusive", "UNTESTABLE", "ghost permission-exclusivity axiom"),

    # ---- float ----------------------------------------------------------
    ("float.rs", r"as Clone>::clone", "WRAPPER", "pbt_f32_clone/pbt_f64_clone (manual structural-eq encoding: ieee-equal || both-NaN; direct == would false-alarm on NaN)"),
    ("float.rs", r"fn float_cast", "UNTESTABLE", "ensures is uninterp float_cast_spec (possibly nondeterministic cast per RFC); also ghost-only cfg"),

    # ---- layout ----------------------------------------------------------
    ("layout.rs", r"core::mem::(size_of|align_of)::", "WRAPPER", "pbt_layout_* axiom harnesses check the composite (assume_spec + broadcast axioms) at concrete primitive/ref/ptr types; generic V not samplable"),
    ("layout.rs", r"core::mem::(size_of_val|align_of_val)", "WRAPPER", "pbt_size_align_of_val_slices (slice/str instantiations, the only ones with pinning axioms)"),

    # ---- crate slice / string / array -----------------------------------
    ("/vstd/slice.rs", r"<\[T\]>::len", "WRAPPER", "pbt_slice_len (composite with axiom_spec_len)"),
    ("/vstd/slice.rs", r"<\[T\]>::get", "UNTESTABLE", "ensures routes through uninterp spec_slice_get — claims nothing evaluable"),
    ("string.rs", r"ToString>::to_string", "ENGINE", "generic `T: Display` param has no sampling story (needs sampled trait-impl families)"),
    ("string.rs", r"str::chars", "ENGINE", "returns a Chars iterator — needs the iterator spec model (iter.rs, descoped)"),
    ("string.rs", r"fn substring_ascii", "WRAPPER", "pbt_substring_ascii — direct #[pbt] probed 2026-07-31: method-form spec calls (self.is_ascii()) route to a nonexistent .exec_is_ascii() instead of the free-fn twin (engine gap)"),
    ("array.rs", r"IntoIterator>::into_iter", "ENGINE", "iterator spec model (iter.rs, descoped)"),
    ("array.rs", r"fn array_as_slice", "WRAPPER", "pbt_array_as_slice (generic fn items cannot take direct #[pbt])"),
    ("array.rs", r"fn array_fill_for_copy_types", "WRAPPER", "pbt_array_fill_for_copy_types (composed with the pinning axiom)"),
    ("array.rs", r"fn ref_mut_array_unsizing_coercion", "ENGINE", "&mut-return write-through (harness cannot observe the coupled mutation)"),

    # ---- pointers & memory ----------------------------------------------
    ("raw_ptr.rs", r"core::ptr::null(_mut)?", "WRAPPER", "pbt_ptr_null (addr-zero observation)"),
    ("raw_ptr.rs", r"PartialEq.*::eq", "WRAPPER", "pbt_ptr_eq (allocation replay; equality is address equality)"),
    ("raw_ptr.rs", r"::(addr|with_addr)", "WRAPPER", "pbt_ptr_addr_with_addr"),
    ("raw_ptr.rs", r"fn ptr_mut_ref\b", "WRAPPER", "pbt_ptr_mut_ref_u32 (&mut return, observed by value). ptr_mut_read/ptr_ref/ptr_mut_write are DIRECT via mono wrappers (whole-opt_value comparisons now decompose to projections)"),
    ("raw_ptr.rs", r"fn cast_\w+", "WRAPPER", "pbt_ptr_casts (addr/metadata/readability observed via core::ptr::metadata)"),
    ("raw_ptr.rs", r"fn (expose_provenance|with_exposed_provenance)", "WRAPPER", "pbt_expose_provenance_roundtrip"),
    ("raw_ptr.rs", r"fn (allocate|deallocate)", "WRAPPER", "pbt_allocate_deallocate (non-null/aligned/in-range + write-read round-trip + coupled dealloc)"),
    ("raw_ptr.rs", r"fn (new|as_ref|as_ptr|ptr_ref2|clone)\b", "WRAPPER", "pbt_shared_reference (value/addr round-trips)"),
    ("simple_pptr.rs", r".", "TODO", "pointer workstream leftovers"),
    ("cell/pcell.rs", r"fn into_inner", "WRAPPER", "pbt_pcell_into_inner (owned permission constructed inside the wrapper)"),
    ("cell/pcell.rs", r".", "WRAPPER", "pbt_pcell_* composites (coupled pair constructed via new)"),
    ("/vstd/cell.rs", r".", "WRAPPER", "pbt_cell_* composites (coupled pair constructed via new/empty)"),
    ("maybe_uninit.rs", r"::uninit", "UNTESTABLE", "ensures is a ghost mem_contents()-is-Uninit claim — unobservable in exec"),
    ("maybe_uninit.rs", r".", "WRAPPER", "pbt_maybe_uninit_* round-trip composites (ghost mem_contents pinned through new)"),
    ("manually_drop.rs", r".", "WRAPPER", "pbt_manually_drop_* (view pinned through new; no sampling strategy for the carrier)"),

    # ---- concurrency / async ---------------------------------------------
    ("std_specs/atomic.rs", r".", "DESCOPED", "atomics: sequential value semantics checkable in principle; ordering claims inherently concurrent"),
    ("/vstd/atomic.rs", r".", "DESCOPED", "tracked-permission atomics (concurrency workstream)"),
    ("thread.rs", r".", "DESCOPED", "thread spawn/join (needs FnOnce sampling + concurrency); thread_id spec is ghost IsThread"),
    ("future.rs", r".", "DESCOPED", "async executor model out of scope"),
    ("proph.rs", r".", "UNTESTABLE", "prophecy variables: resolution is a ghost event with no exec-observable claim"),
    ("invariant.rs", r".", "UNTESTABLE", "pure ghost credit token (no runtime content)"),
    ("pervasive.rs", r"fn exec_nonstatic_call", "ENGINE", "generic FnOnce param (needs sampled closure families)"),
    ("pervasive.rs", r"fn unreached", "UNTESTABLE", "diverging fn with `requires false` — unreachable by contract"),
    ("pervasive.rs", r"fn print_u64", "UNTESTABLE", "no ensures (I/O side effect only)"),
    ("pervasive.rs", r"fn runtime_assert", "UNTESTABLE", "requires-only contract (no ensures to check)"),
    ("pervasive.rs", r"fn (set|set_and_swap)", "DIRECT", ""),

    # ---- alloc internals --------------------------------------------------
    ("std_specs/alloc.rs", r"new_uninit", "UNTESTABLE", "no ensures beyond ghost uninit state — unobservable"),
    ("std_specs/alloc.rs", r".", "WRAPPER", "pbt_box_init_into_vec (module un-gated; liballoc_internals unconditional)"),

    # ---- std_specs: numeric / bits / cmp ---------------------------------
    ("std_specs/num.rs", r"(PartialEq|PartialOrd|Ord)", "WRAPPER", "pbt_cmp_* family restates the *SpecImpl contracts at every width"),
    ("std_specs/num.rs", r"checked_next_multiple_of", "DIRECT", ""),
    ("std_specs/num.rs", r"checked_(div|rem)", "DIRECT", ""),
    ("std_specs/bits.rs", r"leading_(ones|zeros)", "DIRECT", ""),
    ("std_specs/vec.rs", r"Vec::<T, A>::new_in", "WRAPPER", "pbt_vec_new_in_global (allocator param has no sampling strategy)"),
    ("std_specs/cmp.rs", r"<f(32|64) as ", "UNTESTABLE", "ensures routes through uninterp eq_ensures/cmp_ensures (float-nondeterminism RFC) — claims nothing evaluable"),
    ("std_specs/cmp.rs", r"bool as PartialEq", "WRAPPER", "pbt_bool_eq/pbt_bool_ne"),
    ("std_specs/cmp.rs", r"&'a A as (PartialEq|PartialOrd|Ord)|<&'a A as", "WRAPPER", "pbt_ref_eq_ne/pbt_ref_partial_ord/pbt_ref_ord_cmp (forwarding restated at u32)"),

    # ---- std_specs: ops ----------------------------------------------------
    ("std_specs/ops.rs", r"<f(32|64) as core::ops", "UNTESTABLE", "ensures routes through uninterp float-op spec fns (users supply axioms)"),
    ("std_specs/ops.rs", r".", "WRAPPER", "pbt_int_ops_* per-width harnesses (i128/bit-loop oracles + op_assign consistency)"),

    # ---- std_specs: control_flow / range / nonzero / default --------------
    ("control_flow.rs", r".", "WRAPPER", "pbt_result_branch/pbt_option_branch/pbt_*_from_residual composites"),
    ("std_specs/range.rs", r"RangeInclusive<T> as RangeBounds<T>>::end_bound", "WRAPPER", "pbt_range_inclusive_bounds (fresh) + pbt_range_inclusive_end_bound_exhausted — the latter FAILS by design (open finding: spec misses the exhausted->Excluded switch)"),
    ("std_specs/range.rs", r"RangeBounds", "WRAPPER", "per-type pbt_range_*_bounds wrappers"),
    ("std_specs/range.rs", r"::contains", "WRAPPER", "pbt_range_contains / pbt_range_inclusive_new_contains / exhausted composite"),
    ("std_specs/range.rs", r"RangeInclusive::<Idx>::new", "WRAPPER", "pinned via fresh-construction composites (bounds/contains)"),
    ("std_specs/range.rs", r"Iterator>::next", "WRAPPER", "pbt_range_next_* per-width composites (also cover the 12 trusted spec_range_next admits)"),
    ("std_specs/nonzero.rs", r".", "WRAPPER", "pbt_nonzero_* composites (view pinned through new)"),
    ("std_specs/default.rs", r"&'a str as", "DIRECT", ""),
    ("std_specs/default.rs", r"PhantomData", "WRAPPER", "pbt_phantom_and_tuple_defaults"),
    ("std_specs/default.rs", r".", "WRAPPER", "pbt_phantom_and_tuple_defaults pins the concrete composite; the generic call_ensures claim itself stays unlowerable"),

    # ---- stragglers -------------------------------------------------------
    ("string.rs", r"from_utf8_unchecked", "DIRECT", ""),
    ("std_specs/core.rs", r"bool::then", "ENGINE", "FnOnce param — needs sampled closure families"),
    ("std_specs/option.rs", r"Option::<T>::map\b|Option::<T>::map ", "ENGINE", "FnOnce param — needs sampled closure families"),
    ("std_specs/option.rs", r"(as_mut\b|as_mut_slice)", "ENGINE", "&mut-return write-through (aliases the &mut Option param)"),
    ("std_specs/slice.rs", r"(first_mut|split_at_mut)", "ENGINE", "&mut-return write-through"),
    ("std_specs/vec.rs", r"(as_mut_slice|deref_mut)", "ENGINE", "&mut-return write-through"),
    ("std_specs/vec.rs", r"::resize", "WRAPPER", "pbt_vec_resize_bounded (u16 domain)"),
    ("std_specs/vecdeque.rs", r"::resize", "WRAPPER", "pbt_vecdeque_resize_bounded (u16 domain)"),
    ("std_specs/clone.rs", r"&'b T as Clone|&'b T as Clone>::clone|<&'b T as", "WRAPPER", "pbt_ref_clone (same-referent check via ptr::eq)"),

    # ---- std_specs: convert / clone / option / result ---------------------
    ("std_specs/convert.rs", r"as (Into<U>|TryInto<U>)>|TryFrom<U>", "ENGINE", "blanket impls: ensures routes through generic call_ensures / obeys_from_spec of the underlying From"),
    ("std_specs/convert.rs", r".", "WRAPPER", "pbt_from_*/pbt_try_from_* wrapper macro families restate the per-type From/TryFrom contracts"),
    ("std_specs/clone.rs", r"\[T; N\] as Clone", "ENGINE", "quantified ensures uses an untyped binder (forall|i|) — quantifier lowering requires typed binders"),
    ("std_specs/clone.rs", r"(Tracked|Ghost)<T> as Clone", "UNTESTABLE", "ghost carriers — no runtime content"),
    ("std_specs/option.rs", r"Option::<&'a T>::cloned", "WRAPPER", "pbt_option_cloned_clone"),
    ("std_specs/option.rs", r"(and_then|ok_or_else|unwrap_or_else)", "ENGINE", "FnOnce param — needs sampled closure families"),
    ("std_specs/option.rs", r"unwrap_or_default", "ENGINE", "T::default.ensures needs generic-fn call_ensures lowering"),
    ("std_specs/option.rs", r"Option<T> as Clone", "WRAPPER", "pbt_option_cloned_clone"),
    ("std_specs/option.rs", r"as PartialEq", "WRAPPER", "pbt_option_eq"),
    ("std_specs/option.rs", r"as Ord>::cmp|as PartialOrd", "WRAPPER", "pbt_option_cmp (Ord); partial_cmp is TODO — see next rule"),
    ("std_specs/option.rs", r"Option::(insert|get_or_insert)", "ENGINE", "&mut T return aliases the &mut Option param (borrow conflict in harness final-state reads)"),
    ("std_specs/result.rs", r"(map|map_err)", "ENGINE", "FnOnce param — needs sampled closure families"),

    # ---- std_specs: sequences ----------------------------------------------
    ("std_specs/vec.rs", r"Vec::<T, A>::len", "WRAPPER", "pbt_vec_len (composite with axiom_spec_len; spec_vec_len uninterp)"),
    ("std_specs/vec.rs", r"(with_capacity|reserve|try_reserve)", "WRAPPER", "pbt_vec_*_bounded wrappers over u16 size domain (allocation-abort hazard at usize)"),
    ("std_specs/vec.rs", r"from_elem", "WRAPPER", "pbt_vec_from_elem_bounded"),
    ("std_specs/vec.rs", r"extend_from_slice", "ENGINE", "quantified final(vec)@[i] if-else shape outside the quantifier lowering"),
    ("std_specs/vec.rs", r"as Clone>::clone", "ENGINE", "ensures references vec_clone_trigger (Vec-typed spec fn)"),
    ("std_specs/vec.rs", r"as PartialEq", "WRAPPER", "pbt_vec_eq (bare spec; elementwise restatement)"),
    ("std_specs/vec.rs", r"SliceIndex", "ENGINE", "generic SliceIndex plumbing (index_req/&Output returns)"),
    ("std_specs/vec.rs", r"(into_iter|IntoIterator)", "ENGINE", "iterator spec model (iter.rs, descoped)"),
    ("std_specs/vec.rs", r"fn vec_index\b", "DIRECT", ""),
    ("std_specs/vec.rs", r"fn vec_index_mut", "ENGINE", "&mut-return write-through"),
    ("std_specs/vecdeque.rs", r"::len", "WRAPPER", "pbt_vecdeque_len"),
    ("std_specs/vecdeque.rs", r"(with_capacity|reserve)", "WRAPPER", "pbt_vecdeque_*_bounded (u16 domain)"),
    ("std_specs/vecdeque.rs", r"as Clone>::clone", "ENGINE", "cloned::<T> cross-module quantified ensures"),
    ("std_specs/vecdeque.rs", r"::iter", "ENGINE", "iterator spec model"),
    ("std_specs/vecdeque.rs", r"index_mut", "ENGINE", "&mut-return write-through"),
    ("std_specs/vecdeque.rs", r"::index", "WRAPPER", "pbt_vecdeque_index (guarded element read)"),
    ("std_specs/slice.rs", r"unreachable_unchecked", "UNTESTABLE", "diverging, requires false"),
    ("std_specs/slice.rs", r"(::iter|IntoIterator)", "ENGINE", "iterator spec model"),
    ("std_specs/slice.rs", r"(index_mut|last_mut)", "ENGINE", "&mut-return write-through"),
    ("std_specs/slice.rs", r"SliceIndex|as Index", "ENGINE", "SliceIndex assoc-type plumbing (uninterp index_req / &Output returns)"),
    ("std_specs/slice.rs", r"split_at_checked", "WRAPPER", "pbt_slice_split_at_checked"),
    ("std_specs/slice.rs", r"copy_from_slice", "WRAPPER", "pbt_slice_copy_from_slice"),
    ("std_specs/slice.rs", r"copy_within", "WRAPPER", "pbt_slice_copy_within (checked against copy_within_result)"),
    ("std_specs/slice.rs", r"\[T; N\]>::index", "ENGINE", "SliceIndex plumbing at const-generic arrays"),

    # ---- std_specs: containers ---------------------------------------------
    ("std_specs/btree.rs", r"(::iter|::keys|::values)", "ENGINE", "returns spec-modeled iterators (iterator model, descoped)"),
    ("std_specs/btree.rs", r"::len", "WRAPPER", "pbt_btree_map_len/pbt_btree_set_len"),
    ("std_specs/btree.rs", r"BTreeSet.*>::get|>::get.*BTreeSet", "WRAPPER", "pbt_btree_set_get"),
    ("std_specs/btree.rs", r".", "WRAPPER", "pbt_btree_* mutator composites (insert/remove/get/contains at Key=Q=u32, obeys_cmp guard inlined)"),
    ("std_specs/hash.rs", r"DefaultHasher", "UNTESTABLE", "opaque hasher model (uninterp view/finish relation)"),
    ("std_specs/hash.rs", r"(::iter|::keys|::values)", "ENGINE", "iterator spec model (descoped)"),
    ("std_specs/hash.rs", r"HashMap.*>::len|HashSet.*>::len|::len", "WRAPPER", "pbt_hash_map_len/pbt_hash_set_len"),
    ("std_specs/hash.rs", r"::reserve", "WRAPPER", "pbt_hash_capacity_reserve_bounded"),
    ("std_specs/hash.rs", r"HashSet.*::get|>::get.*HashSet", "WRAPPER", "pbt_hash_set_get"),
    ("std_specs/hash.rs", r"HashSet.*::clear", "WRAPPER", "pbt_hash_set_clear"),
    ("std_specs/hash.rs", r"as Clone>::clone", "ENGINE", "quantified ensures references cloned::<T> cross-module spec fn"),
    ("std_specs/hash.rs", r"::entry", "WRAPPER", "entry-flow composites (or_insert value + prophecy write + key)"),
    ("std_specs/hash.rs", r"OccupiedEntry::", "WRAPPER", "pbt_hash_map_occupied_entry_flows"),
    ("std_specs/hash.rs", r"VacantEntry::", "WRAPPER", "pbt_hash_map_vacant_entry_flows"),
    ("std_specs/hash.rs", r"\bEntry::key", "WRAPPER", "pbt_hash_map_entry_key"),
    ("std_specs/hash.rs", r"\bEntry::or_insert", "WRAPPER", "pbt_hash_map_entry_or_insert(+_write)"),
    ("std_specs/hash.rs", r"\bEntry::insert_entry", "WRAPPER", "pbt_hash_map_vacant_entry_flows (insert_entry leg)"),
    ("std_specs/hash.rs", r"with_capacity", "WRAPPER", "pbt_hash_capacity_reserve_bounded"),
    ("std_specs/hash.rs", r".", "WRAPPER", "pbt_hash_* mutator composites (insert/remove/get/contains at Key=Q=u32, obeys_key_model guard inlined)"),
    ("std_specs/iter.rs", r".", "ENGINE", "iterator module descoped (deep prophetic model)"),

    # ---- std_specs: smart_ptrs ---------------------------------------------
    ("std_specs/smart_ptrs.rs", r"Default>::default", "ENGINE", "ensures via generic T::default.ensures (call_ensures)"),
    ("std_specs/smart_ptrs.rs", r".", "WRAPPER", "pbt_box/rc/arc_* composites (deref-comparing contracts not directly annotatable)"),

    # ---- hash_map / hash_set wrapper types ----------------------------------
    ("/vstd/hash_map.rs", r".", "WRAPPER", "pbt_hmwv_*/pbt_shm_* replay+probe composites"),
    ("/vstd/hash_set.rs", r".", "WRAPPER", "pbt_hswv_*/pbt_shs_* replay+probe composites"),
]

# Special-case: option partial_cmp — bare spec whose contract lives in
# PartialOrdSpecImpl; only eq and cmp have wrappers today.
R.insert(0, ("std_specs/option.rs", r"as PartialOrd>::partial_cmp", "WRAPPER",
             "pbt_option_partial_cmp"))


def classify(rel, ident, has_pbt):
    name_m = re.search(r"fn (\w+)", ident or "")
    name = name_m.group(1) if name_m else ""
    if has_pbt:
        return ("HARNESS", "added wrapper harness") if name.startswith("pbt_") else ("DIRECT", "")
    for suffix, pat, status, note in R:
        if suffix and suffix not in rel:
            continue
        if re.search(pat, ident or ""):
            return (status, note)
    return ("UNCLASSIFIED", "")


def main():
    root = sys.argv[-1] if len(sys.argv) > 1 and os.path.isdir(sys.argv[-1]) else DEFAULT_ROOT
    show_sites = "--sites" in sys.argv
    per_file = collections.defaultdict(lambda: collections.Counter())
    notes = collections.defaultdict(lambda: collections.defaultdict(list))
    uncls = []
    for dirpath, _, files in os.walk(root):
        if "/target" in dirpath:
            continue
        for fn in files:
            if not fn.endswith(".rs"):
                continue
            p = os.path.join(dirpath, fn)
            rel = os.path.relpath(p, root)
            for line, kind, has_pbt, ident in scan_file(p):
                status, note = classify("/vstd/" + rel, ident, has_pbt)
                per_file[rel][status] += 1
                if show_sites:
                    print(
                        f"{rel}:{line}  [{kind}]  {status}"
                        f"{'  — ' + note if note else ''}\n    {ident[:150]}"
                    )
                if status not in ("DIRECT", "HARNESS", "INFRA"):
                    notes[rel][(status, note)].append(f"{line}")
                if status == "UNCLASSIFIED":
                    uncls.append(f"{rel}:{line}  {ident[:120]}")

    ORDER = ["DIRECT", "WRAPPER", "TODO", "ENGINE", "DESCOPED", "UNTESTABLE", "HARNESS", "INFRA", "UNCLASSIFIED"]
    tot = collections.Counter()
    print("| file | sites | direct | wrapper | todo | engine | descoped | untestable | %testable | %all |")
    print("|---|---|---|---|---|---|---|---|---|---|")
    rows = []
    for rel, ctr in per_file.items():
        sites = sum(ctr[s] for s in ("DIRECT", "WRAPPER", "TODO", "ENGINE", "DESCOPED", "UNTESTABLE", "UNCLASSIFIED"))
        if sites == 0:
            continue
        cov = ctr["DIRECT"] + ctr["WRAPPER"]
        testable = sites - ctr["UNTESTABLE"]
        pt = f"{100*cov/testable:.0f}%" if testable else "n/a"
        pa = f"{100*cov/sites:.0f}%"
        rows.append((rel, sites, ctr, cov, pt, pa))
    for ctr in per_file.values():
        for s in ORDER:
            tot[s] += ctr[s]
    rows.sort(key=lambda r: (-r[1], r[0]))
    for rel, sites, ctr, cov, pt, pa in rows:
        print(f"| {rel} | {sites} | {ctr['DIRECT']} | {ctr['WRAPPER']} | {ctr['TODO']} | {ctr['ENGINE']} | {ctr['DESCOPED']} | {ctr['UNTESTABLE']} | {pt} | {pa} |")
    sites = sum(tot[s] for s in ("DIRECT", "WRAPPER", "TODO", "ENGINE", "DESCOPED", "UNTESTABLE", "UNCLASSIFIED"))
    cov = tot["DIRECT"] + tot["WRAPPER"]
    testable = sites - tot["UNTESTABLE"]
    print(f"| **TOTAL** | {sites} | {tot['DIRECT']} | {tot['WRAPPER']} | {tot['TODO']} | {tot['ENGINE']} | {tot['DESCOPED']} | {tot['UNTESTABLE']} | {100*cov/testable:.0f}% | {100*cov/sites:.0f}% |")
    print(f"\n(harness fns: {tot['HARNESS']}, infra: {tot['INFRA']}, unclassified: {tot['UNCLASSIFIED']})")

    print("\n\n# Per-file notes (non-covered sites)\n")
    for rel, sites, ctr, cov, pt, pa in rows:
        keyed = notes[rel]
        interesting = {k: v for k, v in keyed.items() if k[0] not in ("DIRECT", "WRAPPER")}
        wrappers = {k: v for k, v in keyed.items() if k[0] == "WRAPPER"}
        if not keyed:
            continue
        print(f"## {rel}")
        for (status, note), lns in sorted(keyed.items()):
            print(f"- {status} x{len(lns)} (lines {','.join(lns[:8])}{'...' if len(lns) > 8 else ''}): {note}")
        print()

    if uncls:
        print("\n# UNCLASSIFIED sites (fix the rules!)\n")
        for u in uncls:
            print(" ", u)


if __name__ == "__main__":
    main()
