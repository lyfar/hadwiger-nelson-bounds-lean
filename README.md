This project is part of an ongoing AI-assisted research workflow for formal mathematics: Lean checks each proof term against its stated assumptions, so a result either holds or it does not.

# Hadwiger–Nelson bounds in Lean

This repository formalizes the currently known bounds for the chromatic number of the Euclidean plane. Lean's kernel checks the complete proof.

## Verified result

The headline theorem is:

```lean
theorem HadwigerNelsonBounds.hadwiger_nelson_known_bounds :
    (5 : ℕ∞) ≤ HadwigerNelsonBounds.unitDistanceGraph.chromaticNumber ∧
      HadwigerNelsonBounds.unitDistanceGraph.chromaticNumber ≤ (7 : ℕ∞)
```

The lower bound is also exposed directly:

```lean
theorem HadwigerNelsonBounds.unitDistanceGraph_not_colorable_four :
    ¬ HadwigerNelsonBounds.unitDistanceGraph.Colorable 4
```

The proof has four checked layers:

1. An explicit Isbell-style seven-coloring proves `χ(ℝ²) ≤ 7`.
2. Parts' 481-vertex coordinates and coloring trees prove that a canonical equilateral triangle of side `√3` cannot be monochromatic in a proper four-coloring.
3. A generated 73-vertex finite closure of Parts' doubled-wheel argument proves that the opposite vertices of a distance-four pair have the same color. It contains 186 unit edges and 76 non-monochromatic-triangle constraints; all routing trees and leaves are checked by proved-sound Lean checkers.
4. Two rigid copies of that pair, with relative rotation having cosine `31/32`, form the final spindle. Their free endpoints are exactly one unit apart, contradicting properness.

The second-stage finite patch is not an extra mathematical assumption. Its edge geometry, triangle witnesses, certificate routing, color symmetries, and final rotations are all proved or reduced by kernel evaluation.

## What is not proved

The exact value of `χ(ℝ²)` is not known. This project proves only the bounds `5 ≤ χ(ℝ²) ≤ 7`; it does not decide whether the answer is 5, 6, or 7 and does not solve Erdős Problem 508.

## Source anchors

- [Jaan Parts, *A human-verifiable proof of the chromatic number of the plane being at least 5*](https://arxiv.org/abs/2010.12661) is the primary lower-bound source. `PartsCoordinates.lean` transcribes `JP/Pink/g481.vtx`; the stored trees correspond to the paper's `S` and `L1`–`L8` diagrams. The finite doubled patch follows the paper's non-monochromatic `√3` triples, rotation with cosine `7/8`, forced distance-four pair, and closing rotation with cosine `31/32`.
- [Polymath 16: Hadwiger–Nelson problem](http://michaelnielsen.org/polymath1/index.php?title=Hadwiger-Nelson_problem) is the data archive cited by Parts for `Polymath16/Code and data/dropbox/JP/Pink`.
- [Aubrey de Grey, *The chromatic number of the plane is at least 5*](https://arxiv.org/abs/1804.02385) is the original 2018 lower-bound breakthrough.
- [Paul Erdős, *Some old and new problems in various branches of combinatorics*](https://combinatorica.hu/~p_erdos/1981-16.pdf) is the historical problem source.
- [Erdős Problem 508](https://www.erdosproblems.com/508) records the open problem and the current bounds.

## Main modules

- `HadwigerNelsonBounds/IsbellColoring.lean` — explicit seven-color upper bound.
- `HadwigerNelsonBounds/PartsCertificate.lean` — sound checker for Parts coloring trees.
- `HadwigerNelsonBounds/PartsCanonicalTriangle.lean` — checked non-monochromatic canonical `√3` triangle.
- `HadwigerNelsonBounds/PartsGadgetForcedPair.lean` — finite combinatorial distance-four forcing theorem.
- `HadwigerNelsonBounds/PartsGadgetEmbedding.lean` — Euclidean realization of every finite constraint.
- `HadwigerNelsonBounds/PartsSpindle.lean` — four-color contradiction and headline known-bounds theorem.
- `HadwigerNelsonBounds.lean` — public entry module.

Generated files remain kernel-checked Lean source. `scripts/generate_parts_gadget.py` deterministically regenerates the finite second-stage data and certificates from integer axial-lattice arithmetic.

## Reproduce and audit

The project pins Lean and Mathlib to `v4.32.0-rc1`.

```bash
lake exe cache get
python3 scripts/generate_parts_gadget.py
lake build HadwigerNelsonBounds
bash scripts/audit.sh
```

The audit requires a warning-free build, runs Mathlib's declaration and style linters, checks the 700-line file limit, scans for forbidden proof shortcuts, and prints the axiom dependencies of the geometric core, both bound theorems, and the headline theorem. Only Mathlib's standard logical dependencies `Classical.choice`, `propext`, and `Quot.sound` are accepted.

There is no `sorry`, `admit`, custom axiom, unsafe declaration, partial or opaque definition, `native_decide`, linter waiver, warning suppression, or heartbeat override.

## AI provenance

The Lean implementation, certificate conversion, finite-patch search, and proof engineering were primarily produced by AI agents under Egor Lyfar's direction, source review, and publication control. The mathematical strategy and source data come from the cited human work. Kernel checking establishes the formal statements above; it is not a claim that AI solved the still-open exact problem.

Author and maintainer: Egor Lyfar <egor.lyfar@gmail.com>.

## Lean Pool status

The complete known-bounds theorem is a future Lean Pool candidate. No upstream PR has been opened from this snapshot.

## License

Apache License 2.0. See [LICENSE](LICENSE).
