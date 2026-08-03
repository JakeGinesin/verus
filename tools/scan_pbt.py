#!/usr/bin/env python3
"""Scan vstd for assume_specification and external_body fns that lack #[pbt].

Usage:
    python3 tools/scan_pbt.py [path-to-vstd]

Defaults to the vstd tree in this checkout (../source/vstd relative to
this script). Prints a per-kind summary of trusted-assumption sites
(`assume_specification` items and `#[verifier::external_body]` fns),
split by whether a `#[pbt]` annotation covers them.
"""
import os, re, sys

DEFAULT_ROOT = os.path.normpath(
    os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "source", "vstd")
)

PBT = "#[pbt"

def scan_file(path):
    with open(path) as f:
        lines = f.readlines()
    n = len(lines)
    out = []
    i = 0
    while i < n:
        ls = lines[i].rstrip()
        kind = None
        ident = None
        if "pub assume_specification" in ls or "assume_specification[" in ls:
            kind = "assume_specification"
            ident = ls.strip()
        elif "#[verifier::external_body]" in ls:
            # Walk forward up to 15 lines past attributes/comments to find
            # the actual fn signature line.
            for j in range(i + 1, min(i + 16, n)):
                nxt = lines[j].rstrip()
                stripped = nxt.lstrip()
                if (
                    not stripped
                    or stripped.startswith("//")
                    or stripped.startswith("#[")
                ):
                    continue
                m = re.match(r"(pub\s+(\([^)]+\)\s+)?)?(unsafe\s+)?(exec\s+)?fn\s+(\w+)", stripped)
                if m:
                    kind = "fn external_body"
                    ident = stripped
                else:
                    # It's external_body on something other than a fn (struct,
                    # impl, etc.). Skip — not a #[pbt] candidate.
                    kind = None
                    ident = None
                break
        if kind is not None:
            has_pbt = False
            # Look for #[pbt] in the surrounding attribute block: up to 10
            # lines back, plus forward attribute lines (an annotation may
            # sit after `#[verifier::external_body]`). Skip comment lines
            # so a `// (no #[pbt]: ...)` skip-rationale note doesn't count
            # as an annotation.
            for k in range(max(0, i - 10), i):
                if lines[k].lstrip().startswith("//"):
                    continue
                if PBT in lines[k]:
                    has_pbt = True
                    break
            if not has_pbt:
                for k in range(i + 1, min(i + 8, n)):
                    stripped = lines[k].lstrip()
                    if stripped.startswith("//"):
                        continue
                    if not stripped.startswith("#["):
                        break
                    if PBT in stripped:
                        has_pbt = True
                        break
            out.append((i + 1, kind, has_pbt, ident))
        i += 1
    return out


def main():
    root = sys.argv[1] if len(sys.argv) > 1 else DEFAULT_ROOT
    if not os.path.isdir(root):
        print(f"error: vstd directory not found: {root}", file=sys.stderr)
        sys.exit(1)
    rows = []
    for dirpath, _, files in os.walk(root):
        if "/target/" in dirpath or dirpath.endswith("/target"):
            continue
        for fn in files:
            if not fn.endswith(".rs"):
                continue
            p = os.path.join(dirpath, fn)
            for line, kind, has_pbt, ident in scan_file(p):
                rows.append((p, line, kind, has_pbt, ident))
    by_kind_status = {}
    for r in rows:
        path, line, kind, has_pbt, ident = r
        key = (kind, has_pbt)
        by_kind_status.setdefault(key, []).append(r)

    print(f"# Summary ({root})\n")
    for (kind, has_pbt), entries in sorted(by_kind_status.items()):
        status = "HAS_PBT" if has_pbt else "no_pbt"
        print(f"\n## {kind} — {status} ({len(entries)})\n")
        for p, line, _, _, ident in entries:
            rel = os.path.relpath(p, root)
            shown = ident[:140] if ident else ""
            print(f"  {rel}:{line}  {shown}")


if __name__ == "__main__":
    main()
