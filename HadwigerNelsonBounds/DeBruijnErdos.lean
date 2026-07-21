/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import HadwigerNelsonBounds.PartsSpindle
import Mathlib.Combinatorics.Compactness

/-!
# The de Bruijn--Erdős compactness theorem for graph coloring

De Bruijn and Erdős proved that a graph is colorable with a fixed finite
number of colors if every finite subgraph is. We derive the theorem from
Mathlib's formalization of Rado's selection principle and specialize it to the
unit-distance graph of the Euclidean plane.

The final result makes the finite-certificate route for the Hadwiger--Nelson
problem exact: `6 ≤ χ(ℝ²)` holds if and only if some finite set of points has a
unit-distance graph that is not colorable with five colors.

## Source

N. G. de Bruijn and P. Erdős, *A colour problem for infinite graphs and a
problem in the theory of relations*, Indagationes Mathematicae 13 (1951),
369--373.

This module does not construct a finite obstruction and therefore does not
improve the known lower bound or solve Erdős Problem 508.
-/

universe u v

variable {α : Type u} {β : α → Type v} [∀ a, Finite (β a)]

/-- Binary-constraint form of Rado compactness. If every finite set of
variables has a simultaneous assignment satisfying all pairwise constraints,
then all variables have such an assignment. -/
theorem Finset.rado_selection_constraints
    (compatible : ∀ a b, β a → β b → Prop)
    (hfinite : ∀ s : Finset α,
      ∃ choice : (a : s) → β a,
        ∀ a b : s, compatible a b (choice a) (choice b)) :
    ∃ choice : (a : α) → β a,
      ∀ a b, compatible a b (choice a) (choice b) := by
  classical
  let localChoice (s : Finset α) : (a : s) → β a :=
    (hfinite s).choose
  have localCompatible (s : Finset α) :
      ∀ a b : s,
        compatible a b (localChoice s a) (localChoice s b) :=
    (hfinite s).choose_spec
  obtain ⟨choice, hagree⟩ :=
    Finset.rado_selection_subtype localChoice
  refine ⟨choice, ?_⟩
  intro a b
  obtain ⟨t, hsubset, hchoice⟩ := hagree {a, b}
  let aSmall : ({a, b} : Finset α) := ⟨a, by simp⟩
  let bSmall : ({a, b} : Finset α) := ⟨b, by simp⟩
  let aLarge : t := Set.inclusion hsubset aSmall
  let bLarge : t := Set.inclusion hsubset bSmall
  have ha : choice a = localChoice t aLarge := by
    simpa [aSmall, aLarge] using hchoice aSmall
  have hb : choice b = localChoice t bLarge := by
    simpa [bSmall, bLarge] using hchoice bSmall
  have hlocal := localCompatible t aLarge bLarge
  rw [← ha, ← hb] at hlocal
  simpa [aLarge, bLarge] using hlocal

namespace SimpleGraph

variable {V : Type u} {W : Type v} {n : ℕ}
    (G : SimpleGraph V) (H : SimpleGraph W)

/-- Finite-target graph-homomorphism compactness. If every finite induced
subgraph of `G` admits a homomorphism to a finite graph `H`, then `G` itself
admits a homomorphism to `H`. -/
theorem nonempty_hom_of_finite_induced [Finite W]
    (hfinite : ∀ s : Finset V,
      Nonempty (G.induce (↑s : Set V) →g H)) :
    Nonempty (G →g H) := by
  classical
  let localHom (s : Finset V) : G.induce (↑s : Set V) →g H :=
    (hfinite s).some
  obtain ⟨vertexMap, hvertexMap⟩ :=
    Finset.rado_selection_constraints
      (β := fun _ : V => W)
      (fun a b imageA imageB => G.Adj a b → H.Adj imageA imageB)
      (fun s => ⟨fun vertex => localHom s vertex, fun a b hadj =>
        (localHom s).map_adj ((induce_adj (G := G)).2 hadj)⟩)
  exact ⟨⟨vertexMap, fun {a b} hadj => hvertexMap a b hadj⟩⟩

/-- A homomorphism to a finite target exists exactly when one exists from
every finite induced subgraph. -/
theorem nonempty_hom_iff_finite_induced [Finite W] :
    Nonempty (G →g H) ↔
      ∀ s : Finset V,
        Nonempty (G.induce (↑s : Set V) →g H) := by
  constructor
  · rintro ⟨hom⟩ s
    exact ⟨hom.comp (Embedding.induce (G := G) (↑s : Set V)).toHom⟩
  · exact G.nonempty_hom_of_finite_induced H

/-- Failure of a homomorphism to a finite target is witnessed on a finite
induced subgraph. -/
theorem not_nonempty_hom_iff_exists_finite_induced [Finite W] :
    ¬Nonempty (G →g H) ↔
      ∃ s : Finset V,
        ¬Nonempty (G.induce (↑s : Set V) →g H) := by
  classical
  rw [G.nonempty_hom_iff_finite_induced H]
  simp only [not_forall]

/-- **De Bruijn--Erdős compactness theorem.** If every finite induced subgraph
of `G` is colorable with `n` colors, then `G` is colorable with `n` colors. -/
theorem colorable_of_finite_induced_colorable
    (hfinite : ∀ s : Finset V, (G.induce (↑s : Set V)).Colorable n) :
    G.Colorable n := by
  exact G.nonempty_hom_of_finite_induced (completeGraph (Fin n)) hfinite

/-- A global coloring restricts to every finite induced subgraph. -/
theorem finite_induced_colorable_of_colorable (hcolorable : G.Colorable n)
    (s : Finset V) : (G.induce (↑s : Set V)).Colorable n :=
  hcolorable.of_hom (Embedding.induce (G := G) (↑s : Set V)).toHom

/-- A graph is `n`-colorable exactly when all its finite induced subgraphs are
`n`-colorable. -/
theorem colorable_iff_finite_induced_colorable :
    G.Colorable n ↔
      ∀ s : Finset V, (G.induce (↑s : Set V)).Colorable n := by
  constructor
  · exact fun hcolorable s =>
      G.finite_induced_colorable_of_colorable hcolorable s
  · exact G.colorable_of_finite_induced_colorable

/-- Contrapositive finite-obstruction form of the de Bruijn--Erdős theorem. -/
theorem not_colorable_iff_exists_finite_induced_not_colorable :
    ¬G.Colorable n ↔
      ∃ s : Finset V, ¬(G.induce (↑s : Set V)).Colorable n := by
  classical
  rw [G.colorable_iff_finite_induced_colorable]
  simp only [not_forall]

section ListColoring

variable {C : Type v} (available : V → Set C)

/-- A proper coloring in which every vertex receives a color from its
prescribed finite list. -/
structure ListColoring where
  /-- The underlying proper coloring. -/
  coloring : G.Coloring C
  /-- Every chosen color belongs to the corresponding vertex list. -/
  mem_available : ∀ vertex, coloring vertex ∈ available vertex

namespace ListColoring

/-- Restrict a list coloring to an induced subgraph. -/
def induce {G : SimpleGraph V} {available : V → Set C}
    (coloring : G.ListColoring available) (s : Finset V) :
    (G.induce (↑s : Set V)).ListColoring
      (fun vertex : s => available vertex) where
  coloring := coloring.coloring.comp
    (Embedding.induce (G := G) (↑s : Set V)).toHom
  mem_available vertex := coloring.mem_available vertex

end ListColoring

/-- Compactness for finite-list coloring. If every finite induced subgraph
has a proper coloring from the prescribed finite lists, then the whole graph
has one. -/
theorem nonempty_listColoring_of_finite_induced
    [∀ vertex, Finite (available vertex)]
    (hfinite : ∀ s : Finset V,
      Nonempty ((G.induce (↑s : Set V)).ListColoring
        (fun vertex : s => available vertex))) :
    Nonempty (G.ListColoring available) := by
  classical
  let localColoring (s : Finset V) :
      (G.induce (↑s : Set V)).ListColoring
        (fun vertex : s => available vertex) :=
    (hfinite s).some
  obtain ⟨choice, hchoice⟩ :=
    Finset.rado_selection_constraints
      (β := fun vertex => {color // color ∈ available vertex})
      (fun a b colorA colorB => G.Adj a b → colorA.1 ≠ colorB.1)
      (fun s => ⟨fun vertex =>
        ⟨(localColoring s).coloring vertex,
          (localColoring s).mem_available vertex⟩,
        fun a b hadj => (localColoring s).coloring.valid
          ((induce_adj (G := G)).2 hadj)⟩)
  refine ⟨⟨Coloring.mk (fun vertex => (choice vertex).1) ?_,
    fun vertex => (choice vertex).2⟩⟩
  intro a b hadj
  exact hchoice a b hadj

/-- A graph has a coloring from prescribed finite lists exactly when all its
finite induced subgraphs do. -/
theorem nonempty_listColoring_iff_finite_induced
    [∀ vertex, Finite (available vertex)] :
    Nonempty (G.ListColoring available) ↔
      ∀ s : Finset V,
        Nonempty ((G.induce (↑s : Set V)).ListColoring
          (fun vertex : s => available vertex)) := by
  constructor
  · rintro ⟨coloring⟩ s
    exact ⟨coloring.induce s⟩
  · exact G.nonempty_listColoring_of_finite_induced available

/-- Failure of coloring from finite lists is witnessed on a finite induced
subgraph. -/
theorem not_nonempty_listColoring_iff_exists_finite_induced
    [∀ vertex, Finite (available vertex)] :
    ¬Nonempty (G.ListColoring available) ↔
      ∃ s : Finset V,
        ¬Nonempty ((G.induce (↑s : Set V)).ListColoring
          (fun vertex : s => available vertex)) := by
  classical
  rw [G.nonempty_listColoring_iff_finite_induced available]
  simp only [not_forall]

end ListColoring

/-- Requiring at least `n + 1` colors is equivalent to failure of
`n`-colorability. -/
theorem succ_le_chromaticNumber_iff_not_colorable :
    ((n + 1 : ℕ) : ℕ∞) ≤ G.chromaticNumber ↔ ¬G.Colorable n := by
  constructor
  · intro hlower hcolorable
    have himpossible : ((n + 1 : ℕ) : ℕ∞) ≤ (n : ℕ∞) :=
      hlower.trans hcolorable.chromaticNumber_le
    norm_cast at himpossible
    omega
  · intro hnot
    apply le_chromaticNumber_iff_colorable.2
    intro colors hcolorable
    by_contra hbound
    have hle : colors ≤ n := by omega
    exact hnot (hcolorable.mono hle)

/-- Every positive finite lower bound on the chromatic number is already
detected by a finite induced subgraph. -/
theorem succ_le_chromaticNumber_iff_exists_finite_induced :
    ((n + 1 : ℕ) : ℕ∞) ≤ G.chromaticNumber ↔
      ∃ s : Finset V,
        ((n + 1 : ℕ) : ℕ∞) ≤
          (G.induce (↑s : Set V)).chromaticNumber := by
  calc
    ((n + 1 : ℕ) : ℕ∞) ≤ G.chromaticNumber ↔ ¬G.Colorable n :=
      G.succ_le_chromaticNumber_iff_not_colorable
    _ ↔ ∃ s : Finset V,
        ¬(G.induce (↑s : Set V)).Colorable n :=
      G.not_colorable_iff_exists_finite_induced_not_colorable
    _ ↔ ∃ s : Finset V,
        ((n + 1 : ℕ) : ℕ∞) ≤
          (G.induce (↑s : Set V)).chromaticNumber := by
      apply exists_congr
      intro s
      exact (G.induce (↑s : Set V)).succ_le_chromaticNumber_iff_not_colorable.symm

/-- If a graph has positive finite chromatic number, some finite induced
subgraph has exactly the same chromatic number. -/
theorem exists_finite_induced_chromaticNumber_eq
    (hchromatic : G.chromaticNumber = ((n + 1 : ℕ) : ℕ∞)) :
    ∃ s : Finset V,
      (G.induce (↑s : Set V)).chromaticNumber =
        ((n + 1 : ℕ) : ℕ∞) := by
  obtain ⟨s, hlower⟩ :=
    G.succ_le_chromaticNumber_iff_exists_finite_induced.mp hchromatic.ge
  refine ⟨s, le_antisymm ?_ hlower⟩
  have hupper := chromaticNumber_mono_of_hom
    (Embedding.induce (G := G) (↑s : Set V)).toHom
  simpa [hchromatic] using hupper

end SimpleGraph

namespace HadwigerNelsonBounds

/-- The plane unit-distance graph is 5-colorable exactly when each finite
induced unit-distance graph is 5-colorable. -/
theorem unitDistanceGraph_colorable_five_iff_every_finite :
    unitDistanceGraph.Colorable 5 ↔
      ∀ s : Finset R2,
        (unitDistanceGraph.induce (↑s : Set R2)).Colorable 5 :=
  unitDistanceGraph.colorable_iff_finite_induced_colorable

/-- **Finite-obstruction completeness for the Hadwiger--Nelson lower bound.**
The plane requires at least six colors if and only if a finite set of points
already has a non-5-colorable induced unit-distance graph. -/
theorem six_le_chromaticNumber_iff_exists_finite_obstruction :
    (6 : ℕ∞) ≤ unitDistanceGraph.chromaticNumber ↔
      ∃ s : Finset R2,
        ¬(unitDistanceGraph.induce (↑s : Set R2)).Colorable 5 := by
  calc
    (6 : ℕ∞) ≤ unitDistanceGraph.chromaticNumber ↔
        ¬unitDistanceGraph.Colorable 5 := by
      simpa using
        (SimpleGraph.succ_le_chromaticNumber_iff_not_colorable
          (G := unitDistanceGraph) (n := 5))
    _ ↔ ∃ s : Finset R2,
        ¬(unitDistanceGraph.induce (↑s : Set R2)).Colorable 5 :=
      unitDistanceGraph.not_colorable_iff_exists_finite_induced_not_colorable

/-- **Finite-witness trichotomy for the Hadwiger--Nelson problem.** The known
bounds reduce the exact value to 5, 6, or 7. In either non-5 case, the exact
chromatic number is already attained by a finite induced unit-distance graph. -/
theorem hadwiger_nelson_finite_witness_trichotomy :
    unitDistanceGraph.chromaticNumber = (5 : ℕ∞) ∨
      (unitDistanceGraph.chromaticNumber = (6 : ℕ∞) ∧
        ∃ s : Finset R2,
          (unitDistanceGraph.induce (↑s : Set R2)).chromaticNumber =
            (6 : ℕ∞)) ∨
      (unitDistanceGraph.chromaticNumber = (7 : ℕ∞) ∧
        ∃ s : Finset R2,
          (unitDistanceGraph.induce (↑s : Set R2)).chromaticNumber =
            (7 : ℕ∞)) := by
  obtain ⟨hlower, hupper⟩ := hadwiger_nelson_known_bounds
  have hfinite : unitDistanceGraph.chromaticNumber ≠ ⊤ :=
    ne_top_of_le_ne_top (by norm_num) hupper
  have hlowerNat : 5 ≤ ENat.toNat unitDistanceGraph.chromaticNumber := by
    simpa using ENat.toNat_le_toNat hlower hfinite
  have hupperNat : ENat.toNat unitDistanceGraph.chromaticNumber ≤ 7 :=
    ENat.toNat_le_of_le_coe hupper
  have hcases : ENat.toNat unitDistanceGraph.chromaticNumber = 5 ∨
      ENat.toNat unitDistanceGraph.chromaticNumber = 6 ∨
      ENat.toNat unitDistanceGraph.chromaticNumber = 7 := by
    omega
  rcases hcases with hfive | hsix | hseven
  · exact Or.inl ((ENat.toNat_eq_iff (by norm_num)).mp hfive)
  · have hchromatic : unitDistanceGraph.chromaticNumber = (6 : ℕ∞) :=
      (ENat.toNat_eq_iff (by norm_num)).mp hsix
    exact Or.inr <| Or.inl ⟨hchromatic,
      unitDistanceGraph.exists_finite_induced_chromaticNumber_eq
        (n := 5) hchromatic⟩
  · have hchromatic : unitDistanceGraph.chromaticNumber = (7 : ℕ∞) :=
      (ENat.toNat_eq_iff (by norm_num)).mp hseven
    exact Or.inr <| Or.inr ⟨hchromatic,
      unitDistanceGraph.exists_finite_induced_chromaticNumber_eq
        (n := 6) hchromatic⟩

end HadwigerNelsonBounds
