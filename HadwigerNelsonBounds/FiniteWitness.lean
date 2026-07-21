/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import HadwigerNelsonBounds.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

/-!
# Finite-witness interface for a six-color lower bound

This module isolates the exact certificate boundary for improving the lower
bound in the Hadwiger--Nelson problem.  A finite graph that is not colorable
with five colors, together with a realization of every edge as a unit segment
in the Euclidean plane, would imply `6 ≤ χ(ℝ²)`.

No such witness is constructed here.  In particular, this module does not
improve the known lower bound and does not solve Erdős Problem 508.

Recon: `~/Knowledge/Construct/recon/erdos_508_hadwiger.md`.
Problem record: <https://www.erdosproblems.com/508>.
-/

namespace HadwigerNelsonBounds

open SimpleGraph

/-- Turn exact unit-length proofs for the edges of `G` into a graph homomorphism
from `G` to the unit-distance graph of the Euclidean plane.  Nonedges of `G`
are allowed to map to unit distance as well. -/
def unitDistanceHomOfEdgeRealization {V : Type*} (G : SimpleGraph V)
    (point : V → R2)
    (unit_edges : ∀ ⦃u v : V⦄, G.Adj u v → dist (point u) (point v) = 1) :
    G →g unitDistanceGraph where
  toFun := point
  map_rel' := by
    intro u v huv
    have hdist := unit_edges huv
    rw [unitDistanceGraph_adj]
    constructor
    · intro heq
      have hzero : dist (point u) (point v) = 0 := dist_eq_zero.mpr heq
      linarith
    · exact Or.inl hdist

/-- A non-5-colorable graph realized by unit segments in the plane makes the
plane unit-distance graph itself non-5-colorable. -/
theorem unitDistanceGraph_not_colorable_five_of_witness
    {V : Type*} (G : SimpleGraph V)
    (realization : G →g unitDistanceGraph)
    (not_five_colorable : ¬ G.Colorable 5) :
    ¬ unitDistanceGraph.Colorable 5 := by
  intro plane_five_colorable
  exact not_five_colorable (plane_five_colorable.of_hom realization)

/-- **Finite-witness bridge.** A finite non-5-colorable graph whose edges are
realized as unit segments in `ℝ²` certifies `6 ≤ χ(ℝ²)`. -/
theorem six_le_chromaticNumber_of_finite_witness
    {vertexCount : ℕ} (G : SimpleGraph (Fin vertexCount))
    (point : Fin vertexCount → R2)
    (unit_edges : ∀ ⦃u v : Fin vertexCount⦄,
      G.Adj u v → dist (point u) (point v) = 1)
    (not_five_colorable : ¬ G.Colorable 5) :
    (6 : ℕ∞) ≤ unitDistanceGraph.chromaticNumber := by
  have plane_not_five_colorable : ¬ unitDistanceGraph.Colorable 5 :=
    unitDistanceGraph_not_colorable_five_of_witness G
      (unitDistanceHomOfEdgeRealization G point unit_edges) not_five_colorable
  apply SimpleGraph.le_chromaticNumber_iff_colorable.2
  intro colors colorable
  norm_cast
  by_contra hnot
  have hle : colors ≤ 5 := by omega
  exact plane_not_five_colorable (colorable.mono hle)

end HadwigerNelsonBounds
