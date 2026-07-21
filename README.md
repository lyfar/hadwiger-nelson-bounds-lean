Egor is building an independent AI research lab because his son Misha has rare genetic hearing loss. Every checked result tests and advances the research workflow. One rare disease is rare. Rare diseases together are not.

# Hadwiger–Nelson bounds in Lean

This repository is an honest public research snapshot of a completed, kernel-checked upper bound for the Hadwiger–Nelson problem, also catalogued as Erdős Problem 508.

## Verified result

The formalization constructs an explicit Isbell-style seven-coloring of the Euclidean plane:

```lean
theorem HadwigerNelsonBounds.chromaticNumber_le_seven :
    HadwigerNelsonBounds.unitDistanceGraph.Colorable 7
```

Equivalently, the unit-distance graph on `ℝ²` has chromatic number at most seven. The proof develops the triangular lattice, proves its Voronoi covering radius, proves the modular separation of same-colored lattice points, and bundles the resulting coloring as a Mathlib `SimpleGraph.Coloring`.

## What is not proved

This repository does **not** formalize the known lower bound `5 ≤ χ(ℝ²)`. It does **not** determine whether the chromatic number of the plane is 5, 6, or 7, and it does **not** solve Erdős Problem 508.

The missing lower-bound project is Jaan Parts' human-verifiable certificate: a 481-vertex base graph, 268 used vertices, nine coloring trees, and 787 non-root checks, followed by the geometric argument ruling out a four-coloring. That certificate has not been transcribed or verified here.

## Sources

- [Erdős Problem 508](https://www.erdosproblems.com/508) — canonical problem record and current bounds.
- [Paul Erdős, *Some old and new problems in various branches of combinatorics* (1981)](https://combinatorica.hu/~p_erdos/1981-16.pdf) — historical statement of the plane-coloring problem and the classical seven-color upper bound.
- [Aubrey de Grey, *The chromatic number of the plane is at least 5* (2018)](https://arxiv.org/abs/1804.02385) — current lower-bound breakthrough and historical attribution of the upper construction.
- [Jaan Parts, *A human-verifiable proof of the chromatic number of the plane being at least 5* (2020)](https://arxiv.org/abs/2010.12661) — source for the missing future lower-bound formalization.

## Reproduce

The project pins Lean and Mathlib to `v4.32.0-rc1`.

```bash
lake exe cache get
lake build HadwigerNelsonBounds
bash scripts/audit.sh
```

The audit performs a warning-free build, scans every Lean source for forbidden proof shortcuts, runs the Mathlib declaration and style linters, and prints the axiom dependencies of the geometric core and headline theorem. It accepts only:

```text
Classical.choice
propext
Quot.sound
```

No `sorry`, `admit`, custom axiom, unsafe declaration, partial or opaque definition, `native_decide`, linter waiver, warning suppression, or heartbeat override is used.

## AI provenance

The Lean proofs were primarily produced and ported by AI agents under Egor Lyfar's direction, source review, and publication control. Lean's kernel checks the proof terms; that is correctness evidence for the formal statements, not a claim that an AI solved the open problem or independently discovered the mathematics.

Author and maintainer: Egor Lyfar <egor.lyfar@gmail.com>.

## Future Lean Pool target

This snapshot is not submitted to Lean Pool as a completed project. The intended future target is a source-anchored formalization of the full known bounds `5 ≤ χ(ℝ²) ≤ 7`, adding the Parts lower-bound certificate to the verified Isbell upper construction.

## License

Apache License 2.0. See [LICENSE](LICENSE).
