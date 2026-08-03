import sys, os, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from classify_pbt import scan_file, classify, DEFAULT_ROOT

groups = collections.defaultdict(list)
for dirpath, _, files in os.walk(DEFAULT_ROOT):
    if "/target" in dirpath:
        continue
    for fn in files:
        if not fn.endswith(".rs"):
            continue
        p = os.path.join(dirpath, fn)
        rel = os.path.relpath(p, DEFAULT_ROOT)
        for line, kind, has_pbt, ident in scan_file(p):
            status, note = classify("/vstd/" + rel, ident, has_pbt)
            if status == "ENGINE":
                groups[note].append(f"{rel}:{line}")

total = sum(len(v) for v in groups.values())
print(f"ENGINE-gated sites: {total}\n")
for note, sites in sorted(groups.items(), key=lambda kv: -len(kv[1])):
    print(f"x{len(sites):3d}  {note}")
    print(f"       {', '.join(sites[:12])}{' ...' if len(sites) > 12 else ''}\n")
