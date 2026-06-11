//! PBT demo for vstd's string external_body fns.
//!
//! Mirrors the contracts of `vstd::string::*::{unicode_len, get_char,
//! substring_char, from_str, concat}` and runs them under proptest. The
//! `&str ↔ Seq<char>` view lowering means contracts written in terms of
//! `s@.len()`, `s@.index(i as int)`, and `s@.subrange(i as int, j as int)`
//! evaluate at runtime by collecting `s.chars()` into a `Vec<char>` and
//! applying the existing seq-method lowering.
//!
//! The bodies are marked `external_body` so Verus doesn't try to verify
//! them — that's the whole point of PBT'ing external_body fns.

use vstd::prelude::*;
use vstd::contrib::verus_pbt::*;

verus! {

#[pbt]
#[verifier::external_body]
pub exec fn unicode_len(s: &str) -> (l: usize)
    ensures
        l == s@.len(),
{
    s.chars().count()
}

#[pbt]
#[verifier::external_body]
pub exec fn get_char(s: &str, i: usize) -> (c: char)
    requires
        i < s@.len(),
    ensures
        c == s@.index(i as int),
{
    s.chars().nth(i).unwrap()
}

#[pbt]
#[verifier::external_body]
pub exec fn substring_char(s: &str, from: usize, to: usize) -> (ret: String)
    requires
        from <= to,
        to <= s@.len(),
    ensures
        ret@ == s@.subrange(from as int, to as int),
{
    let mut iter = s.chars();
    let mut out = String::new();
    let mut k: usize = 0;
    while k < to {
        let c = iter.next().unwrap();
        if k >= from {
            out.push(c);
        }
        k += 1;
    }
    out
}

#[pbt]
#[verifier::external_body]
pub exec fn from_str(s: &str) -> (ret: String)
    ensures
        s@ == ret@,
{
    s.to_string()
}

#[pbt]
#[verifier::external_body]
pub exec fn concat(a: String, b: &str) -> (ret: String)
    ensures
        ret@ == a@ + b@,
{
    let mut out = a;
    out.push_str(b);
    out
}

}
