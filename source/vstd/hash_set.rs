// altered from HashMap
use core::marker;
use std::borrow::Borrow;

#[allow(unused_imports)]
use super::pervasive::*;
use super::prelude::*;
#[allow(unused_imports)]
use super::set::*;
#[cfg(verus_keep_ghost)]
use super::std_specs::hash::obeys_key_model;
#[allow(unused_imports)]
use core::hash::Hash;
use std::collections::HashSet;

verus! {

/// `HashSetWithView` is a trusted wrapper around `std::collections::HashSet` with `View` implemented for the type `vstd::map::Set<<Key as View>::V>`.
///
/// See the Rust documentation for [`HashSet`](https://doc.rust-lang.org/std/collections/struct.HashSet.html)
/// for details about its implementation.
///
/// If you are using `std::collections::HashSet` directly, see [`ExHashSet`](https://verus-lang.github.io/verus/verusdoc/vstd/std_specs/hash/struct.ExHashSet.html)
/// for information on the Verus specifications for this type.
#[verifier::ext_equal]
#[verifier::reject_recursive_types(Key)]
pub struct HashSetWithView<Key> where Key: View + Eq + Hash {
    m: HashSet<Key>,
}

impl<Key> View for HashSetWithView<Key> where Key: View + Eq + Hash {
    type V = Set<<Key as View>::V>;

    uninterp spec fn view(&self) -> Self::V;
}

impl<Key> HashSetWithView<Key> where Key: View + Eq + Hash {
    /// Creates an empty `HashSetWithView` with capacity 0.
    ///
    /// See [`obeys_key_model()`](https://verus-lang.github.io/verus/verusdoc/vstd/std_specs/hash/fn.obeys_key_model.html)
    /// for information on use with primitive types and other types.
    /// See Rust's [`HashSet::new()`](https://doc.rust-lang.org/std/collections/struct.HashSet.html#method.new) for implementation details.
    #[verifier::external_body]
    pub fn new() -> (result: Self)
        requires
            obeys_key_model::<Key>(),
            forall|k1: Key, k2: Key| k1@ == k2@ ==> k1 == k2,
        ensures
            result@ == Set::<<Key as View>::V>::empty(),
    {
        Self { m: HashSet::new() }
    }

    /// Creates an empty `HashSetWithView` with at least capacity for the specified number of elements.
    ///
    /// See [`obeys_key_model()`](https://verus-lang.github.io/verus/verusdoc/vstd/std_specs/hash/fn.obeys_key_model.html)
    /// for information on use with primitive types and other types.
    /// See Rust's [`HashSet::with_capacity()`](https://doc.rust-lang.org/std/collections/struct.HashSet.html#method.with_capacity) for implementation details.
    #[verifier::external_body]
    pub fn with_capacity(capacity: usize) -> (result: Self)
        requires
            obeys_key_model::<Key>(),
            forall|k1: Key, k2: Key| k1@ == k2@ ==> k1 == k2,
        ensures
            result@ == Set::<<Key as View>::V>::empty(),
    {
        Self { m: HashSet::with_capacity(capacity) }
    }

    /// Reserves capacity for at least `additional` number of elements in the set.
    ///
    /// See Rust's [`HashSet::reserve()`](https://doc.rust-lang.org/std/collections/struct.HashSet.html#method.reserve) for implementation details.
    #[verifier::external_body]
    pub fn reserve(&mut self, additional: usize)
        ensures
            final(self)@ == old(self)@,
    {
        self.m.reserve(additional);
    }

    /// Returns the number of elements in the set.
    pub uninterp spec fn spec_len(&self) -> usize;

    /// Returns the number of elements in the set.
    #[verifier::external_body]
    #[verifier::when_used_as_spec(spec_len)]
    pub fn len(&self) -> (result: usize)
        ensures
            result == self@.len(),
    {
        self.m.len()
    }

    /// Returns true if the set is empty.
    #[verifier::external_body]
    pub fn is_empty(&self) -> (result: bool)
        ensures
            result == self@.is_empty(),
    {
        self.m.is_empty()
    }

    /// Inserts the given value into the set. Returns true if the value was not previously in the set, false otherwise.
    ///
    /// See Rust's [`HashSet::insert()`](https://doc.rust-lang.org/std/collections/struct.HashSet.html#method.insert) for implementation details.
    #[verifier::external_body]
    pub fn insert(&mut self, k: Key) -> (result: bool)
        ensures
            final(self)@ == old(self)@.insert(k@) && result == !old(self)@.contains(k@),
    {
        self.m.insert(k)
    }

    /// Removes the given value from the set. Returns true if the value was previously in the set, false otherwise.
    ///
    /// See Rust's [`HashSet::remove()`](https://doc.rust-lang.org/std/collections/struct.HashSet.html#method.remove) for implementation details.
    #[verifier::external_body]
    pub fn remove(&mut self, k: &Key) -> (result: bool)
        ensures
            final(self)@ == old(self)@.remove(k@) && result == old(self)@.contains(k@),
    {
        self.m.remove(k)
    }

    /// Returns true if the set contains the given value.
    ///
    /// See Rust's [`HashSet::contains()`](https://doc.rust-lang.org/std/collections/struct.HashSet.html#method.contains) for implementation details.
    #[verifier::external_body]
    pub fn contains(&self, k: &Key) -> (result: bool)
        ensures
            result == self@.contains(k@),
    {
        self.m.contains(k)
    }

    /// Returns a reference to the value in the set that is equal to the given value. If the value is not present in the set, returns `None`.
    ///
    /// See Rust's [`HashSet::get()`](https://doc.rust-lang.org/std/collections/struct.HashSet.html#method.get) for implementation details.
    #[verifier::external_body]
    pub fn get<'a>(&'a self, k: &Key) -> (result: Option<&'a Key>)
        ensures
            match result {
                Some(v) => self@.contains(k@) && v == &k,
                None => !self@.contains(k@),
            },
    {
        self.m.get(k)
    }

    /// Clears all values from the set.
    ///
    /// See Rust's [`HashSet::clear()`](https://doc.rust-lang.org/std/collections/struct.HashSet.html#method.clear) for implementation details.
    #[verifier::external_body]
    pub fn clear(&mut self)
        ensures
            final(self)@ == Set::<<Key as View>::V>::empty(),
    {
        self.m.clear()
    }
}

pub broadcast axiom fn axiom_hash_set_with_view_spec_len<Key>(m: &HashSetWithView<Key>) where
    Key: View + Eq + Hash,

    ensures
        #[trigger] m.spec_len() == m@.len(),
;

/// `StringHashSet` is a trusted wrapper around `std::collections::HashSet<String>` with `View` implemented for the type `vstd::map::Set<Seq<char>>`.
///
/// This type was created for ease of use with `String` as it uses `&str` instead of `&String` for methods that require shared references.
/// Also, it assumes that [`obeys_key_model::<String>()`](https://verus-lang.github.io/verus/verusdoc/vstd/std_specs/hash/fn.obeys_key_model.html) holds.
///
/// See the Rust documentation for [`HashSet`](https://doc.rust-lang.org/std/collections/struct.HashSet.html)
/// for details about its implementation.
///
/// If you are using `std::collections::HashSet` directly, see [`ExHashSet`](https://verus-lang.github.io/verus/verusdoc/vstd/std_specs/hash/struct.ExHashSet.html)
/// for information on the Verus specifications for this type.
#[verifier::ext_equal]
pub struct StringHashSet {
    m: HashSet<String>,
}

impl View for StringHashSet {
    type V = Set<Seq<char>>;

    uninterp spec fn view(&self) -> Self::V;
}

impl StringHashSet {
    /// Creates an empty `StringHashSet` with capacity 0.
    ///
    /// See Rust's [`HashSet::new()`](https://doc.rust-lang.org/std/collections/struct.HashSet.html#method.new) for implementation details.
    #[verifier::external_body]
    pub fn new() -> (result: Self)
        ensures
            result@ == Set::<Seq<char>>::empty(),
    {
        Self { m: HashSet::new() }
    }

    /// Creates an empty `StringHashSet` with at least capacity for the specified number of elements.
    ///
    /// See Rust's [`HashSet::with_capacity()`](https://doc.rust-lang.org/std/collections/struct.HashSet.html#method.with_capacity) for implementation details.
    #[verifier::external_body]
    pub fn with_capacity(capacity: usize) -> (result: Self)
        ensures
            result@ == Set::<Seq<char>>::empty(),
    {
        Self { m: HashSet::with_capacity(capacity) }
    }

    /// Reserves capacity for at least `additional` number of elements in the set.
    ///
    /// See Rust's [`HashSet::reserve()`](https://doc.rust-lang.org/std/collections/struct.HashSet.html#method.reserve) for implementation details.
    #[verifier::external_body]
    pub fn reserve(&mut self, additional: usize)
        ensures
            final(self)@ == old(self)@,
    {
        self.m.reserve(additional);
    }

    /// Returns true if the set is empty.
    #[verifier::external_body]
    pub fn is_empty(&self) -> (result: bool)
        ensures
            result == self@.is_empty(),
    {
        self.m.is_empty()
    }

    /// Returns the number of elements in the set.
    pub uninterp spec fn spec_len(&self) -> usize;

    /// Returns the number of elements in the set.
    #[verifier::external_body]
    #[verifier::when_used_as_spec(spec_len)]
    pub fn len(&self) -> (result: usize)
        ensures
            result == self@.len(),
    {
        self.m.len()
    }

    /// Inserts the given value into the set. Returns true if the value was not previously in the set, false otherwise.
    ///
    /// See Rust's [`HashSet::insert()`](https://doc.rust-lang.org/std/collections/struct.HashSet.html#method.insert) for implementation details.
    #[verifier::external_body]
    pub fn insert(&mut self, k: String) -> (result: bool)
        ensures
            final(self)@ == old(self)@.insert(k@) && result == !old(self)@.contains(k@),
    {
        self.m.insert(k)
    }

    /// Removes the given value from the set. Returns true if the value was previously in the set, false otherwise.
    ///
    /// See Rust's [`HashSet::remove()`](https://doc.rust-lang.org/std/collections/struct.HashSet.html#method.remove) for implementation details.
    #[verifier::external_body]
    pub fn remove(&mut self, k: &str) -> (result: bool)
        ensures
            final(self)@ == old(self)@.remove(k@) && result == old(self)@.contains(k@),
    {
        self.m.remove(k)
    }

    /// Returns true if the set contains the given value.
    ///
    /// See Rust's [`HashSet::contains()`](https://doc.rust-lang.org/std/collections/struct.HashSet.html#method.contains) for implementation details.
    #[verifier::external_body]
    pub fn contains(&self, k: &str) -> (result: bool)
        ensures
            result == self@.contains(k@),
    {
        self.m.contains(k)
    }

    /// Returns a reference to the value in the set that is equal to the given value. If the value is not present in the set, returns `None`.
    ///
    /// See Rust's [`HashSet::get()`](https://doc.rust-lang.org/std/collections/struct.HashSet.html#method.get) for implementation details.
    #[verifier::external_body]
    pub fn get<'a>(&'a self, k: &str) -> (result: Option<&'a String>)
        ensures
            match result {
                Some(v) => self@.contains(k@) && v@ == k@,
                None => !self@.contains(k@),
            },
    {
        self.m.get(k)
    }

    /// Clears all values from the set.
    ///
    /// See Rust's [`HashSet::clear()`](https://doc.rust-lang.org/std/collections/struct.HashSet.html#method.clear) for implementation details.
    #[verifier::external_body]
    pub fn clear(&mut self)
        ensures
            final(self)@ == Set::<Seq<char>>::empty(),
    {
        self.m.clear()
    }
}

pub broadcast axiom fn axiom_string_hash_set_spec_len(m: &StringHashSet)
    ensures
        #[trigger] m.spec_len() == m@.len(),
;

pub broadcast group group_hash_set_axioms {
    axiom_hash_set_with_view_spec_len,
    axiom_string_hash_set_spec_len,
}

// ---------------------------------------------------------------------------
// Composite PBT wrappers for the `HashSetWithView` / `StringHashSet` method
// contracts. Same design as the map wrappers in hash_map.rs: sample a plain
// `HashSet` model, replay-construct the receiver, run the method, check the
// claim via `len`-plus-`contains` probing (sound and complete for set
// equality given the wrapper exposes no iteration).
// ---------------------------------------------------------------------------

/// Replay-construct a `HashSetWithView<u32>` from a model.
#[cfg(all(feature = "std", not(verus_verify_core)))]
#[verifier::external_body]
fn pbt_hswv_build(model: &std::collections::HashSet<u32>) -> HashSetWithView<u32> {
    let mut s = HashSetWithView::<u32>::new();
    for k in model.iter() {
        s.insert(*k);
    }
    s
}

/// Probe-based set equality: `len` + pointwise `contains`.
#[cfg(all(feature = "std", not(verus_verify_core)))]
#[verifier::external_body]
fn pbt_hswv_matches(s: &HashSetWithView<u32>, expected: &std::collections::HashSet<u32>) -> bool {
    s.len() == expected.len() && expected.iter().all(|k| s.contains(k))
}

/// Replay-construct a `StringHashSet` from a model.
#[cfg(all(feature = "std", not(verus_verify_core)))]
#[verifier::external_body]
fn pbt_shs_build(model: &std::collections::HashSet<String>) -> StringHashSet {
    let mut s = StringHashSet::new();
    for k in model.iter() {
        s.insert(k.clone());
    }
    s
}

/// Probe-based set equality for the string-keyed wrapper.
#[cfg(all(feature = "std", not(verus_verify_core)))]
#[verifier::external_body]
fn pbt_shs_matches(s: &StringHashSet, expected: &std::collections::HashSet<String>) -> bool {
    s.len() == expected.len() && expected.iter().all(|k| s.contains(k.as_str()))
}

/// `new` / `is_empty` / `len` on the empty set.
#[cfg(all(feature = "std", not(verus_verify_core)))]
#[verifier::external_body]
#[pbt]
pub fn pbt_hswv_new() -> (ret: bool)
    ensures ret,
{
    let s = HashSetWithView::<u32>::new();
    s.is_empty() && s.len() == 0
}

/// `with_capacity` over a bounded size domain.
#[cfg(all(feature = "std", not(verus_verify_core)))]
#[verifier::external_body]
#[pbt]
pub fn pbt_hswv_with_capacity_bounded(capacity: u16) -> (ret: bool)
    ensures ret,
{
    let s = HashSetWithView::<u32>::with_capacity(capacity as usize);
    s.is_empty() && s.len() == 0
}

/// `reserve` leaves the set unchanged (bounded size domain).
#[cfg(all(feature = "std", not(verus_verify_core)))]
#[verifier::external_body]
#[pbt]
pub fn pbt_hswv_reserve_bounded(model: std::collections::HashSet<u32>, additional: u16) -> (ret: bool)
    ensures ret,
{
    let mut s = pbt_hswv_build(&model);
    s.reserve(additional as usize);
    pbt_hswv_matches(&s, &model)
}

/// `len` / `is_empty` agree with the model.
#[cfg(all(feature = "std", not(verus_verify_core)))]
#[verifier::external_body]
#[pbt]
pub fn pbt_hswv_len_is_empty(model: std::collections::HashSet<u32>) -> (ret: bool)
    ensures ret,
{
    let s = pbt_hswv_build(&model);
    s.len() == model.len() && s.is_empty() == model.is_empty()
}

/// `insert`: result is "newly inserted"; post-state adds the element.
#[cfg(all(feature = "std", not(verus_verify_core)))]
#[verifier::external_body]
#[pbt]
pub fn pbt_hswv_insert(model: std::collections::HashSet<u32>, k: u32) -> (ret: bool)
    ensures ret,
{
    let mut s = pbt_hswv_build(&model);
    let result = s.insert(k);
    let mut expected = model;
    let expected_result = expected.insert(k);
    result == expected_result && pbt_hswv_matches(&s, &expected)
}

/// `remove`: result is "was present"; post-state drops the element.
#[cfg(all(feature = "std", not(verus_verify_core)))]
#[verifier::external_body]
#[pbt]
pub fn pbt_hswv_remove(model: std::collections::HashSet<u32>, k: u32) -> (ret: bool)
    ensures ret,
{
    let mut s = pbt_hswv_build(&model);
    let result = s.remove(&k);
    let mut expected = model;
    let expected_result = expected.remove(&k);
    result == expected_result && pbt_hswv_matches(&s, &expected)
}

/// `contains` / `get` agree with the model (`get` returns the set's own
/// element, which for `u32` must equal the probe key itself).
#[cfg(all(feature = "std", not(verus_verify_core)))]
#[verifier::external_body]
#[pbt]
pub fn pbt_hswv_contains_get(model: std::collections::HashSet<u32>, k: u32) -> (ret: bool)
    ensures ret,
{
    let s = pbt_hswv_build(&model);
    s.contains(&k) == model.contains(&k)
        && s.get(&k).copied() == (if model.contains(&k) { Some(k) } else { None })
}

/// `clear`: post-state is empty.
#[cfg(all(feature = "std", not(verus_verify_core)))]
#[verifier::external_body]
#[pbt]
pub fn pbt_hswv_clear(model: std::collections::HashSet<u32>) -> (ret: bool)
    ensures ret,
{
    let mut s = pbt_hswv_build(&model);
    s.clear();
    s.is_empty() && s.len() == 0
}

/// StringHashSet: `new` plus the insert/remove/contains/get family.
#[cfg(all(feature = "std", not(verus_verify_core)))]
#[verifier::external_body]
#[pbt]
pub fn pbt_shs_new() -> (ret: bool)
    ensures ret,
{
    let s = StringHashSet::new();
    s.is_empty() && s.len() == 0
}

#[cfg(all(feature = "std", not(verus_verify_core)))]
#[verifier::external_body]
#[pbt]
pub fn pbt_shs_insert(model: std::collections::HashSet<String>, k: String) -> (ret: bool)
    ensures ret,
{
    let mut s = pbt_shs_build(&model);
    let result = s.insert(k.clone());
    let mut expected = model;
    let expected_result = expected.insert(k);
    result == expected_result && pbt_shs_matches(&s, &expected)
}

#[cfg(all(feature = "std", not(verus_verify_core)))]
#[verifier::external_body]
#[pbt]
pub fn pbt_shs_remove(model: std::collections::HashSet<String>, k: String) -> (ret: bool)
    ensures ret,
{
    let mut s = pbt_shs_build(&model);
    let result = s.remove(k.as_str());
    let mut expected = model;
    let expected_result = expected.remove(&k);
    result == expected_result && pbt_shs_matches(&s, &expected)
}

#[cfg(all(feature = "std", not(verus_verify_core)))]
#[verifier::external_body]
#[pbt]
pub fn pbt_shs_contains_get(model: std::collections::HashSet<String>, k: String) -> (ret: bool)
    ensures ret,
{
    let s = pbt_shs_build(&model);
    s.len() == model.len() && s.is_empty() == model.is_empty()
        && s.contains(k.as_str()) == model.contains(&k)
        && s.get(k.as_str()).cloned() == (if model.contains(&k) { Some(k) } else { None })
}

#[cfg(all(feature = "std", not(verus_verify_core)))]
#[verifier::external_body]
#[pbt]
pub fn pbt_shs_clear(model: std::collections::HashSet<String>) -> (ret: bool)
    ensures ret,
{
    let mut s = pbt_shs_build(&model);
    s.clear();
    s.is_empty() && s.len() == 0
}

} // verus!
