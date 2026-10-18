#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
evidence_dir="${1:-.lake/verification}"
mkdir -p "$evidence_dir"
python3 verify/source_inventory.py "$evidence_dir/source-before.json"
lake build QuanIncapacity > "$evidence_dir/build.log" 2>&1
lake env lean -DautoImplicit=false verify/Check.lean > "$evidence_dir/axioms.log" 2>&1
python3 verify/source_inventory.py "$evidence_dir/source-after.json"
cmp "$evidence_dir/source-before.json" "$evidence_dir/source-after.json"
echo "Import coverage, build, terminal checks, axiom audit, and source hashes passed."
