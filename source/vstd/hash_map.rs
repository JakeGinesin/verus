use core::marker;

#[allow(unused_imports)]
use super::map::*;
#[allow(unused_imports)]
use super::pervasive::*;
use super::prelude::*;
#[cfg(verus_keep_ghost)]
use super::std_specs::hash::obeys_key_model;
#[allow(unused_imports)]
use core::hash::Hash;
use std::collections::HashMap;

verus! {

/// `HashMapWithView` is a trusted wrapper around `std::collections::HashMap` with `View` implemented for the type `vstd::map::Map<<Key as View>::V, Value>`.
///
/// See the Rust documentation for [`HashMap`](https://doc.rust-lang.org/std/collections/struct.HashMap.html)
/// for details about its implementation.
///
/// If you are using `std::collections::HashMap` directly, see [`ExHashMap`](https://verus-lang.github.io/verus/verusdoc/vstd/std_specs/hash/struct.ExHashMap.html)
/// for information on the Verus specifications for this type.
#[verifier::ext_equal]
#[verifier::reject_recursive_types(Key)]
#[verifier::reject_recursive_types(Value)]
pub struct HashMapWithView<Key, Value> where Key: View + Eq + Hash {
    m: HashMap<Key, Value>,
}

impl<Key, Value> View for HashMapWithView<Key, Value> where Key: View + Eq + Hash {
    type V = Map<<Key as View>::V, Value>;

    uninterp spec fn view(&self) -> Self::V;
}

impl<Key, Value> HashMapWithView<Key, Value> where Key: View + Eq + Hash {
    /// Creates an empty `HashMapWithView` with a capacity of 0.
    ///
    /// See [`obeys_key_model()`](https://verus-lang.github.io/verus/verusdoc/vstd/std_specs/hash/fn.obeys_key_model.html)
    /// for information on use with primitive types and other types.
    /// See Rust's [`HashMap::new()`](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.new) for implementation details.
    #[verifier::external_body]
    pub fn new() -> (result: Self)
        requires
            obeys_key_model::<Key>(),
            forall|k1: Key, k2: Key| k1@ == k2@ ==> k1 == k2,
        ensures
            result@ == Map::<<Key as View>::V, Value>::empty(),
    {
        Self { m: HashMap::new() }
    }

    /// Creates an empty `HashMapWithView` with at least capacity for the specified number of elements.
    ///
    /// See [`obeys_key_model()`](https://verus-lang.github.io/verus/verusdoc/vstd/std_specs/hash/fn.obeys_key_model.html)
    /// for information on use with primitive types and other types.
    /// See Rust's [`HashMap::with_capacity()`](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.with_capacity) for implementation details.
    #[verifier::external_body]
    pub fn with_capacity(capacity: usize) -> (result: Self)
        requires
            obeys_key_model::<Key>(),
            forall|k1: Key, k2: Key| k1@ == k2@ ==> k1 == k2,
        ensures
            result@ == Map::<<Key as View>::V, Value>::empty(),
    {
        Self { m: HashMap::with_capacity(capacity) }
    }

    /// Reserves capacity for at least `additional` number of elements in the map.
    ///
    /// See Rust's [`HashMap::reserve()`](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.reserve) for implementation details.
    #[verifier::external_body]
    pub fn reserve(&mut self, additional: usize)
        ensures
            final(self)@ == old(self)@,
    {
        self.m.reserve(additional);
    }

    /// Returns true if the map is empty.
    #[verifier::external_body]
    pub fn is_empty(&self) -> (result: bool)
        ensures
            result == self@.is_empty(),
    {
        self.m.is_empty()
    }

    /// Returns the number of elements in the map.
    pub uninterp spec fn spec_len(&self) -> usize;

    /// Returns the number of elements in the map.
    #[verifier::external_body]
    #[verifier::when_used_as_spec(spec_len)]
    pub fn len(&self) -> (result: usize)
        ensures
            result == self@.len(),
    {
        self.m.len()
    }

    /// Inserts the given key and value in the map.
    ///
    /// See Rust's [`HashMap::insert()`](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.insert) for implementation details.
    #[verifier::external_body]
    pub fn insert(&mut self, k: Key, v: Value)
        ensures
            final(self)@ == old(self)@.insert(k@, v),
    {
        self.m.insert(k, v);
    }

    /// Removes the given key from the map and returns the value. If the key is not present in the map, returns `None`
    /// and the map is unmodified.
    ///
    /// See Rust's [`HashMap::remove()`](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.remove) for implementation details.
    #[verifier::external_body]
    pub fn remove(&mut self, k: &Key) -> (out: Option<Value>)
        ensures
            match out {
                Some(v) => old(self)@.contains_key(k@) && v == old(self)@[k@] && final(self)@
                    == old(self)@.remove(k@),
                None => !old(self)@.contains_key(k@) && final(self)@ == old(self)@,
            },
    {
        self.m.remove(k)
    }

    /// Returns true if the map contains the given key.
    ///
    /// See Rust's [`HashMap::contains_key()`](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.contains_key) for implementation details.
    #[verifier::external_body]
    pub fn contains_key(&self, k: &Key) -> (result: bool)
        ensures
            result == self@.contains_key(k@),
    {
        self.m.contains_key(k)
    }

    /// Returns a reference to the value corresponding to the given key in the map. If the key is not present in the map, returns `None`.
    ///
    /// See Rust's [`HashMap::get()`](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.get) for implementation details.
    #[verifier::external_body]
    pub fn get<'a>(&'a self, k: &Key) -> (result: Option<&'a Value>)
        ensures
            match result {
                Some(v) => self@.contains_key(k@) && *v == self@[k@],
                None => !self@.contains_key(k@),
            },
    {
        self.m.get(k)
    }

    /// Clears all key-value pairs in the map. Retains the allocated memory for reuse.
    ///
    /// See Rust's [`HashMap::clear()`](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.clear) for implementation details.
    #[verifier::external_body]
    pub fn clear(&mut self)
        ensures
            final(self)@ == Map::<<Key as View>::V, Value>::empty(),
    {
        self.m.clear()
    }

    /// Returns the union of the two maps. If a key is present in both maps, then the value in the right map (`other`) is retained.
    #[verifier::external_body]
    pub fn union_prefer_right(&mut self, other: Self)
        ensures
            final(self)@ == old(self)@.union_prefer_right(other@),
    {
        self.m.extend(other.m)
    }
}

pub broadcast axiom fn axiom_hash_map_with_view_spec_len<Key, Value>(
    m: &HashMapWithView<Key, Value>,
) where Key: View + Eq + Hash
    ensures
        #[trigger] m.spec_len() == m@.len(),
;

/// `StringHashMap` is a trusted wrapper around `std::collections::HashMap<String, Value>` with `View` implemented for the type `vstd::map::Map<Seq<char>, Value>`.
///
/// This type was created for ease of use with `String` as it uses `&str` instead of `&String` for methods that require shared references.
/// Also, it assumes that [`obeys_key_model::<String>()`](https://verus-lang.github.io/verus/verusdoc/vstd/std_specs/hash/fn.obeys_key_model.html) holds.
///
/// See the Rust documentation for [`HashMap`](https://doc.rust-lang.org/std/collections/struct.HashMap.html)
/// for details about its implementation.
///
/// If you are using `std::collections::HashMap` directly, see [`ExHashMap`](https://verus-lang.github.io/verus/verusdoc/vstd/std_specs/hash/struct.ExHashMap.html)
/// for information on the Verus specifications for this type.
#[verifier::ext_equal]
#[verifier::reject_recursive_types(Value)]
pub struct StringHashMap<Value> {
    m: HashMap<String, Value>,
}

impl<Value> View for StringHashMap<Value> {
    type V = Map<Seq<char>, Value>;

    uninterp spec fn view(&self) -> Self::V;
}

impl<Value> StringHashMap<Value> {
    /// Creates an empty `StringHashMap` with a capacity of 0.
    ///
    /// See Rust's [`HashMap::new()`](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.new) for implementation details.
    #[verifier::external_body]
    pub fn new() -> (result: Self)
        ensures
            result@ == Map::<Seq<char>, Value>::empty(),
    {
        Self { m: HashMap::new() }
    }

    /// Creates an empty `StringHashMap` with at least capacity for the specified number of elements.
    ///
    /// See Rust's [`HashMap::with_capacity()`](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.with_capacity) for implementation details.
    #[verifier::external_body]
    pub fn with_capacity(capacity: usize) -> (result: Self)
        ensures
            result@ == Map::<Seq<char>, Value>::empty(),
    {
        Self { m: HashMap::with_capacity(capacity) }
    }

    /// Reserves capacity for at least `additional` number of elements in the map.
    ///
    /// See Rust's [`HashMap::reserve()`](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.reserve) for implementation details.
    #[verifier::external_body]
    pub fn reserve(&mut self, additional: usize)
        ensures
            final(self)@ == old(self)@,
    {
        self.m.reserve(additional);
    }

    /// Returns true if the map is empty.
    #[verifier::external_body]
    pub fn is_empty(&self) -> (result: bool)
        ensures
            result == self@.is_empty(),
    {
        self.m.is_empty()
    }

    /// Returns the number of elements in the map.
    pub uninterp spec fn spec_len(&self) -> usize;

    /// Returns the number of elements in the map.
    #[verifier::external_body]
    #[verifier::when_used_as_spec(spec_len)]
    pub fn len(&self) -> (result: usize)
        ensures
            result == self@.len(),
    {
        self.m.len()
    }

    /// Inserts the given key and value in the map.
    ///
    /// See Rust's [`HashMap::insert()`](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.insert) for implementation details.
    #[verifier::external_body]
    pub fn insert(&mut self, k: String, v: Value)
        ensures
            final(self)@ == old(self)@.insert(k@, v),
    {
        self.m.insert(k, v);
    }

    /// Removes the given key from the map. If the key is not present in the map, the map is unmodified.
    ///
    /// See Rust's [`HashMap::remove()`](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.remove) for implementation details.
    #[verifier::external_body]
    pub fn remove(&mut self, k: &str)
        ensures
            final(self)@ == old(self)@.remove(k@),
    {
        self.m.remove(k);
    }

    /// Returns true if the map contains the given key.
    ///
    /// See Rust's [`HashMap::contains_key()`](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.contains_key) for implementation details.
    #[verifier::external_body]
    pub fn contains_key(&self, k: &str) -> (result: bool)
        ensures
            result == self@.contains_key(k@),
    {
        self.m.contains_key(k)
    }

    /// Returns a reference to the value corresponding to the given key in the map. If the key is not present in the map, returns `None`.
    ///
    /// See Rust's [`HashMap::get()`](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.get) for implementation details.
    #[verifier::external_body]
    pub fn get<'a>(&'a self, k: &str) -> (result: Option<&'a Value>)
        ensures
            match result {
                Some(v) => self@.contains_key(k@) && *v == self@[k@],
                None => !self@.contains_key(k@),
            },
    {
        self.m.get(k)
    }

    /// Clears all key-value pairs in the map. Retains the allocated memory for reuse.
    ///
    /// See Rust's [`HashMap::clear()`](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.clear) for implementation details.
    #[verifier::external_body]
    pub fn clear(&mut self)
        ensures
            final(self)@ == Map::<Seq<char>, Value>::empty(),
    {
        self.m.clear()
    }

    /// Returns the union of the two maps. If a key is present in both maps, then the value in the right map (`other`) is retained.
    #[verifier::external_body]
    pub fn union_prefer_right(&mut self, other: Self)
        ensures
            final(self)@ == old(self)@.union_prefer_right(other@),
    {
        self.m.extend(other.m)
    }
}

pub broadcast axiom fn axiom_string_hash_map_spec_len<Value>(m: &StringHashMap<Value>)
    ensures
        #[trigger] m.spec_len() == m@.len(),
;

pub broadcast group group_hash_map_axioms {
    axiom_hash_map_with_view_spec_len,
    axiom_string_hash_map_spec_len,
}

// ---------------------------------------------------------------------------
// Composite PBT wrappers for the `HashMapWithView` / `StringHashMap` method
// contracts.
//
// The receivers can't be sampled directly: the wrapped field is private and
// the `View` is uninterp, so a model can't be projected out of a receiver. 
// Each wrapper (1) samples a plain `HashMap` model, (2) replay-constructs 
// the receiver via `new()` + `insert`, (3) runs the method under test, and 
// (4) checks the contract's claim against an independently computed expected model using
// `len`-plus-`get` probing. 
//
// Known bootstrap circularity: `insert` builds the receiver whose methods
// are under test. A broken `insert` perturbs the constructed state and
// fails the expected-vs-probed relation at some sample, but constructor
// coverage is weaker than an engine-side treatment would give.
// ---------------------------------------------------------------------------

/// Replay-construct a `HashMapWithView<u32, u32>` from a model.
#[cfg(all(feature = "std", not(verus_verify_core)))]
#[verifier::external_body]
fn pbt_hmwv_build(model: &std::collections::HashMap<u32, u32>) -> HashMapWithView<u32, u32> {
    let mut m = HashMapWithView::<u32, u32>::new();
    for (k, v) in model.iter() {
        m.insert(*k, *v);
    }
    m
}

/// Probe-based map equality: `len` + pointwise `get` over the expected keys.
#[cfg(all(feature = "std", not(verus_verify_core)))]
#[verifier::external_body]
fn pbt_hmwv_matches(
    m: &HashMapWithView<u32, u32>,
    expected: &std::collections::HashMap<u32, u32>,
) -> bool {
    m.len() == expected.len() && expected.iter().all(|(k, v)| m.get(k) == Some(v))
}

/// Replay-construct a `StringHashMap<u32>` from a model.
#[cfg(all(feature = "std", not(verus_verify_core)))]
#[verifier::external_body]
fn pbt_shm_build(model: &std::collections::HashMap<String, u32>) -> StringHashMap<u32> {
    let mut m = StringHashMap::<u32>::new();
    for (k, v) in model.iter() {
        m.insert(k.clone(), *v);
    }
    m
}

/// Probe-based map equality for the string-keyed wrapper.
#[cfg(all(feature = "std", not(verus_verify_core)))]
#[verifier::external_body]
fn pbt_shm_matches(
    m: &StringHashMap<u32>,
    expected: &std::collections::HashMap<String, u32>,
) -> bool {
    m.len() == expected.len() && expected.iter().all(|(k, v)| m.get(k.as_str()) == Some(v))
}

/// `new` / `is_empty` / `len` on the empty map.
#[cfg(all(feature = "std", not(verus_verify_core)))]
#[verifier::external_body]
#[pbt]
pub fn pbt_hmwv_new() -> (ret: bool)
    ensures ret,
{
    let m = HashMapWithView::<u32, u32>::new();
    m.is_empty() && m.len() == 0
}

/// `with_capacity` over a bounded size domain (see vec.rs `pbt_*_bounded`).
#[cfg(all(feature = "std", not(verus_verify_core)))]
#[verifier::external_body]
#[pbt]
pub fn pbt_hmwv_with_capacity_bounded(capacity: u16) -> (ret: bool)
    ensures ret,
{
    let m = HashMapWithView::<u32, u32>::with_capacity(capacity as usize);
    m.is_empty() && m.len() == 0
}

/// `reserve` leaves the map unchanged (bounded size domain).
#[cfg(all(feature = "std", not(verus_verify_core)))]
#[verifier::external_body]
#[pbt]
pub fn pbt_hmwv_reserve_bounded(model: std::collections::HashMap<u32, u32>, additional: u16) -> (ret: bool)
    ensures ret,
{
    let mut m = pbt_hmwv_build(&model);
    m.reserve(additional as usize);
    pbt_hmwv_matches(&m, &model)
}

/// `is_empty` / `len` agree with the model.
#[cfg(all(feature = "std", not(verus_verify_core)))]
#[verifier::external_body]
#[pbt]
pub fn pbt_hmwv_len_is_empty(model: std::collections::HashMap<u32, u32>) -> (ret: bool)
    ensures ret,
{
    let m = pbt_hmwv_build(&model);
    m.len() == model.len() && m.is_empty() == model.is_empty()
}

/// `insert`: post-state is the model plus the binding.
#[cfg(all(feature = "std", not(verus_verify_core)))]
#[verifier::external_body]
#[pbt]
pub fn pbt_hmwv_insert(model: std::collections::HashMap<u32, u32>, k: u32, v: u32) -> (ret: bool)
    ensures ret,
{
    let mut m = pbt_hmwv_build(&model);
    m.insert(k, v);
    let mut expected = model;
    expected.insert(k, v);
    pbt_hmwv_matches(&m, &expected)
}

/// `remove`: returned value matches the old binding; post-state drops it.
#[cfg(all(feature = "std", not(verus_verify_core)))]
#[verifier::external_body]
#[pbt]
pub fn pbt_hmwv_remove(model: std::collections::HashMap<u32, u32>, k: u32) -> (ret: bool)
    ensures ret,
{
    let mut m = pbt_hmwv_build(&model);
    let out = m.remove(&k);
    let mut expected = model;
    let expected_out = expected.remove(&k);
    out == expected_out && pbt_hmwv_matches(&m, &expected)
}

/// `contains_key` / `get` agree with the model.
#[cfg(all(feature = "std", not(verus_verify_core)))]
#[verifier::external_body]
#[pbt]
pub fn pbt_hmwv_contains_get(model: std::collections::HashMap<u32, u32>, k: u32) -> (ret: bool)
    ensures ret,
{
    let m = pbt_hmwv_build(&model);
    m.contains_key(&k) == model.contains_key(&k)
        && m.get(&k).copied() == model.get(&k).copied()
}

/// `clear`: post-state is empty.
#[cfg(all(feature = "std", not(verus_verify_core)))]
#[verifier::external_body]
#[pbt]
pub fn pbt_hmwv_clear(model: std::collections::HashMap<u32, u32>) -> (ret: bool)
    ensures ret,
{
    let mut m = pbt_hmwv_build(&model);
    m.clear();
    m.is_empty() && m.len() == 0
}

/// `union_prefer_right`: post-state is the left model overwritten by the
/// right (`Map::union_prefer_right` semantics).
#[cfg(all(feature = "std", not(verus_verify_core)))]
#[verifier::external_body]
#[pbt]
pub fn pbt_hmwv_union_prefer_right(
    left: std::collections::HashMap<u32, u32>,
    right: std::collections::HashMap<u32, u32>,
) -> (ret: bool)
    ensures ret,
{
    let mut m = pbt_hmwv_build(&left);
    let other = pbt_hmwv_build(&right);
    m.union_prefer_right(other);
    let mut expected = left;
    expected.extend(right.into_iter());
    pbt_hmwv_matches(&m, &expected)
}

/// StringHashMap: `new` / `is_empty` / `len` on the empty map.
#[cfg(all(feature = "std", not(verus_verify_core)))]
#[verifier::external_body]
#[pbt]
pub fn pbt_shm_new() -> (ret: bool)
    ensures ret,
{
    let m = StringHashMap::<u32>::new();
    m.is_empty() && m.len() == 0
}

/// StringHashMap `insert` (String keys: the `Seq<char>` key-view is
/// injective, so model-key equality mirrors view equality).
#[cfg(all(feature = "std", not(verus_verify_core)))]
#[verifier::external_body]
#[pbt]
pub fn pbt_shm_insert(model: std::collections::HashMap<String, u32>, k: String, v: u32) -> (ret: bool)
    ensures ret,
{
    let mut m = pbt_shm_build(&model);
    m.insert(k.clone(), v);
    let mut expected = model;
    expected.insert(k, v);
    pbt_shm_matches(&m, &expected)
}

/// StringHashMap `remove` (returns nothing; post-state only).
#[cfg(all(feature = "std", not(verus_verify_core)))]
#[verifier::external_body]
#[pbt]
pub fn pbt_shm_remove(model: std::collections::HashMap<String, u32>, k: String) -> (ret: bool)
    ensures ret,
{
    let mut m = pbt_shm_build(&model);
    m.remove(k.as_str());
    let mut expected = model;
    expected.remove(&k);
    pbt_shm_matches(&m, &expected)
}

/// StringHashMap `contains_key` / `get` / `len` / `is_empty`.
#[cfg(all(feature = "std", not(verus_verify_core)))]
#[verifier::external_body]
#[pbt]
pub fn pbt_shm_contains_get(model: std::collections::HashMap<String, u32>, k: String) -> (ret: bool)
    ensures ret,
{
    let m = pbt_shm_build(&model);
    m.len() == model.len() && m.is_empty() == model.is_empty()
        && m.contains_key(k.as_str()) == model.contains_key(&k)
        && m.get(k.as_str()).copied() == model.get(&k).copied()
}

/// StringHashMap `clear`.
#[cfg(all(feature = "std", not(verus_verify_core)))]
#[verifier::external_body]
#[pbt]
pub fn pbt_shm_clear(model: std::collections::HashMap<String, u32>) -> (ret: bool)
    ensures ret,
{
    let mut m = pbt_shm_build(&model);
    m.clear();
    m.is_empty() && m.len() == 0
}

/// StringHashMap `union_prefer_right`.
#[cfg(all(feature = "std", not(verus_verify_core)))]
#[verifier::external_body]
#[pbt]
pub fn pbt_shm_union_prefer_right(
    left: std::collections::HashMap<String, u32>,
    right: std::collections::HashMap<String, u32>,
) -> (ret: bool)
    ensures ret,
{
    let mut m = pbt_shm_build(&left);
    let other = pbt_shm_build(&right);
    m.union_prefer_right(other);
    let mut expected = left;
    expected.extend(right.into_iter());
    pbt_shm_matches(&m, &expected)
}

} // verus!
