use super::super::prelude::*;
// PBT in-place patch: spec fns are erased under plain `cargo build` /
// `cargo test`, so this named import only resolves in verifier builds.
// The `#[pbt]` harness evaluates `encode_scalar` against the trusted
// exec twin below.
#[cfg(verus_keep_ghost)]
use super::super::utf8::encode_scalar;

verus! {

// Trusted exec twin of the cross-module (`utf8.rs`) spec fn
// `encode_scalar`, mirroring its definition: the standard UTF-8
// encoding of a scalar value, with the width boundaries
// `has_width_{1,2,3,4}_encoding` (1 byte ≤ 0x7F, 2 bytes ≤ 0x7FF,
// 3 bytes ≤ 0xFFFF excluding surrogates, else 4). This lets the
// `#[pbt]` harness compare the real `char::len_utf8` against the
// vstd spec's byte-width arithmetic.
#[cfg(not(verus_verify_core))]
external_pbt_provide! {
    fn encode_scalar(scalar: u32) -> Seq<u8> {
        if scalar <= 0x7F {
            vec![scalar as u8]
        } else if scalar <= 0x7FF {
            vec![0xC0 | (scalar >> 6) as u8, 0x80 | (scalar & 0x3F) as u8]
        } else if scalar <= 0xFFFF {
            vec![
                0xE0 | (scalar >> 12) as u8,
                0x80 | ((scalar >> 6) & 0x3F) as u8,
                0x80 | (scalar & 0x3F) as u8,
            ]
        } else {
            vec![
                0xF0 | (scalar >> 18) as u8,
                0x80 | ((scalar >> 12) & 0x3F) as u8,
                0x80 | ((scalar >> 6) & 0x3F) as u8,
                0x80 | (scalar & 0x3F) as u8,
            ]
        }
    }
}

/// The byte width of `c`'s UTF-8 encoding, using the same scalar-value
/// boundaries as [`encode_scalar`].
#[pbt]
#[verifier::allow_in_spec]
pub assume_specification[ char::len_utf8 ](c: char) -> usize
    returns
        encode_scalar(c as u32).len() as usize,
;

/// Unicode's `White_Space` property:
/// <https://www.unicode.org/reports/tr44/#White_Space>.
pub open spec fn is_white_space(c: char) -> bool {
    c == '\u{9}' || c == '\u{A}' || c == '\u{B}' || c == '\u{C}' || c == '\u{D}' || c == '\u{20}'
        || c == '\u{85}' || c == '\u{A0}' || c == '\u{1680}' || c == '\u{2000}' || c == '\u{2001}'
        || c == '\u{2002}' || c == '\u{2003}' || c == '\u{2004}' || c == '\u{2005}' || c
        == '\u{2006}' || c == '\u{2007}' || c == '\u{2008}' || c == '\u{2009}' || c == '\u{200A}'
        || c == '\u{2028}' || c == '\u{2029}' || c == '\u{202F}' || c == '\u{205F}' || c
        == '\u{3000}'
}

#[pbt]
pub assume_specification[ char::is_whitespace ](c: char) -> (res: bool)
    returns
        is_white_space(c),
;

} // verus!
