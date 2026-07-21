#!/usr/bin/env bash
set -euo pipefail

project_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
cd "$project_root"

audit_dir=$(mktemp -d)
trap 'rm -rf "$audit_dir"' EXIT

run_without_warnings() {
  local label=$1
  shift
  local log="$audit_dir/$label.log"
  "$@" 2>&1 | tee "$log"
  if rg -n '(^|: )warning:' "$log"; then
    echo "$label emitted warnings." >&2
    exit 1
  fi
}

run_without_warnings build lake build HadwigerNelsonBounds

forbidden='\b(sorry|admit|axiom|constant|unsafe|partial|opaque|native_decide|set_option|nolint)\b'
if rg -n --glob '*.lean' "$forbidden" HadwigerNelsonBounds.lean HadwigerNelsonBounds; then
  echo "Forbidden Lean construct found." >&2
  exit 1
fi

while IFS= read -r source_file; do
  line_count=$(wc -l <"$source_file")
  if ((line_count > 700)); then
    echo "$source_file has $line_count lines; limit is 700." >&2
    exit 1
  fi
done < <(find HadwigerNelsonBounds -name '*.lean' -type f -print)

run_without_warnings declarations lake exe runLinter HadwigerNelsonBounds
run_without_warnings style lake exe lint-style HadwigerNelsonBounds

cat >"$audit_dir/AxiomAudit.lean" <<'LEAN'
import HadwigerNelsonBounds

#print axioms HadwigerNelsonBounds.exists_lattice_point_within_circumradius
#print axioms HadwigerNelsonBounds.dist_between_same_color_lattice_points
#print axioms HadwigerNelsonBounds.isbell_isProperColoring
#print axioms HadwigerNelsonBounds.chromaticNumber_le_seven
LEAN

axiom_log="$audit_dir/axioms.log"
lake env lean "$audit_dir/AxiomAudit.lean" 2>&1 | tee "$axiom_log"
python3 - "$axiom_log" <<'PY'
import re
import sys

text = open(sys.argv[1], encoding="utf-8").read()
allowed = {"Classical.choice", "propext", "Quot.sound"}
payloads = re.findall(r"depends on axioms:\s*\[(.*?)\]", text, flags=re.DOTALL)
if len(payloads) != 4:
    raise SystemExit(f"expected four axiom reports, found {len(payloads)}")
for payload in payloads:
    found = {name.strip() for name in payload.split(",") if name.strip()}
    unexpected = found - allowed
    if unexpected:
        raise SystemExit(f"unexpected axioms: {sorted(unexpected)}")
print("Axiom audit passed; only Classical.choice, propext, and Quot.sound occur.")
PY
