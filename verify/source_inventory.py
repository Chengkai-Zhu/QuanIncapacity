#!/usr/bin/env python3
"""Check local import coverage and record reproducible source identities."""
import hashlib
import json
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
sources = {"QuanIncapacity": ROOT / "QuanIncapacity.lean"}
sources.update({".".join(p.relative_to(ROOT).with_suffix("").parts): p
                for p in (ROOT / "QuanIncapacity").rglob("*.lean")})
reachable = set()
pending = ["QuanIncapacity"]
while pending:
    module = pending.pop()
    if module in reachable:
        continue
    reachable.add(module)
    text = sources[module].read_text()
    pending.extend(m for m in re.findall(r"^import\s+(QuanIncapacity[\w.]*)\s*$", text, re.M)
                   if m in sources)
missing = sorted(set(sources) - reachable)
if missing:
    raise SystemExit("Local modules absent from the root import closure: " + ", ".join(missing))

files = list(sources.values()) + [ROOT / p for p in (
    "lean-toolchain", "lakefile.toml", "lake-manifest.json", "verify/Check.lean",
    "verify/source_inventory.py", "verify/run_checks.sh",
    "verify/verify_matrices.py", "verify/requirements.txt",
    ".github/workflows/ci.yml")]
result = {
    "local_module_count": len(sources),
    "all_local_modules_reachable": True,
    "sha256": {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
               for p in sorted(files)},
}
output = json.dumps(result, ensure_ascii=False, indent=2) + "\n"
if len(sys.argv) == 2:
    pathlib.Path(sys.argv[1]).write_text(output)
else:
    print(output, end="")
