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
done < <(find HadwigerNelsonBounds scripts -type f \
  \( -name '*.lean' -o -name '*.py' -o -name '*.sh' \) -print)

run_without_warnings declarations lake exe runLinter HadwigerNelsonBounds
run_without_warnings style lake exe lint-style HadwigerNelsonBounds

cat >"$audit_dir/AxiomAudit.lean" <<'LEAN'
import HadwigerNelsonBounds

#print axioms HadwigerNelsonBounds.exists_lattice_point_within_circumradius
#print axioms HadwigerNelsonBounds.dist_between_same_color_lattice_points
#print axioms HadwigerNelsonBounds.isbell_isProperColoring
#print axioms HadwigerNelsonBounds.chromaticNumber_le_seven
#print axioms HadwigerNelsonBounds.parts_canonical_triangle_not_monochromatic
#print axioms HadwigerNelsonBounds.parts_gadget_forces_monochromatic_pair
#print axioms HadwigerNelsonBounds.partsGadgetColoring_valid
#print axioms HadwigerNelsonBounds.unitDistanceGraph_not_colorable_four
#print axioms HadwigerNelsonBounds.five_le_chromaticNumber
#print axioms HadwigerNelsonBounds.hadwiger_nelson_known_bounds
#print axioms HadwigerNelsonBounds.unitDistanceHomOfEdgeRealization
#print axioms HadwigerNelsonBounds.unitDistanceGraph_not_colorable_five_of_witness
#print axioms HadwigerNelsonBounds.six_le_chromaticNumber_of_finite_witness
#print axioms Finset.rado_selection_constraints
#print axioms SimpleGraph.nonempty_hom_of_finite_induced
#print axioms SimpleGraph.nonempty_hom_iff_finite_induced
#print axioms SimpleGraph.not_nonempty_hom_iff_exists_finite_induced
#print axioms SimpleGraph.ListColoring
#print axioms SimpleGraph.ListColoring.induce
#print axioms SimpleGraph.nonempty_listColoring_of_finite_induced
#print axioms SimpleGraph.nonempty_listColoring_iff_finite_induced
#print axioms SimpleGraph.not_nonempty_listColoring_iff_exists_finite_induced
#print axioms SimpleGraph.colorable_of_finite_induced_colorable
#print axioms SimpleGraph.finite_induced_colorable_of_colorable
#print axioms SimpleGraph.colorable_iff_finite_induced_colorable
#print axioms SimpleGraph.not_colorable_iff_exists_finite_induced_not_colorable
#print axioms SimpleGraph.succ_le_chromaticNumber_iff_not_colorable
#print axioms SimpleGraph.succ_le_chromaticNumber_iff_exists_finite_induced
#print axioms SimpleGraph.exists_finite_induced_chromaticNumber_eq
#print axioms HadwigerNelsonBounds.unitDistanceGraph_colorable_five_iff_every_finite
#print axioms HadwigerNelsonBounds.six_le_chromaticNumber_iff_exists_finite_obstruction
#print axioms HadwigerNelsonBounds.hadwiger_nelson_finite_witness_trichotomy
LEAN

axiom_log="$audit_dir/axioms.log"
lake env lean "$audit_dir/AxiomAudit.lean" 2>&1 | tee "$axiom_log"
python3 - "$axiom_log" <<'PY'
import re
import sys

text = open(sys.argv[1], encoding="utf-8").read()
allowed = {"Classical.choice", "propext", "Quot.sound"}
payloads = re.findall(r"depends on axioms:\s*\[(.*?)\]", text, flags=re.DOTALL)
empty_reports = re.findall(r"does not depend on any axioms", text)
report_count = len(payloads) + len(empty_reports)
if report_count != 32:
    raise SystemExit(f"expected thirty-two axiom reports, found {report_count}")
for payload in payloads:
    found = {name.strip() for name in payload.split(",") if name.strip()}
    unexpected = found - allowed
    if unexpected:
        raise SystemExit(f"unexpected axioms: {sorted(unexpected)}")
print("Axiom audit passed; only Classical.choice, propext, and Quot.sound occur.")
PY
