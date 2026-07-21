/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import HadwigerNelsonBounds.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

/-!
# Obstruction to a linear six-residue triangular-lattice coloring

Isbell's seven-color construction colors triangular-lattice cells by a linear
residue.  This module isolates a limitation of replacing its modulus seven by
six: every linear map from the triangular lattice to `ZMod 6` has a nonzero
kernel vector of Eisenstein norm at most four.  Consequently, no such map has
the norm-seven separation property used by the existing seven-color proof.

This is a theorem about one restricted family of lattice colorings.  It does
not rule out nonlinear six-colorings, other tilings, or a six-coloring of the
plane, and it does not solve the Hadwiger--Nelson problem.

Recon: `~/Knowledge/Construct/recon/erdos_508_hadwiger.md`.
-/

namespace HadwigerNelsonBounds

/-- The squared length form for axial coordinates of the triangular lattice. -/
def triangularLatticeNorm (di dj : ℤ) : ℤ :=
  di ^ 2 + di * dj + dj ^ 2

/-- The triangular-lattice norm is nonnegative. -/
lemma triangularLatticeNorm_nonneg (di dj : ℤ) :
    0 ≤ triangularLatticeNorm di dj := by
  have hidentity : 4 * triangularLatticeNorm di dj =
      (2 * di + dj) ^ 2 + 3 * dj ^ 2 := by
    simp only [triangularLatticeNorm]
    ring
  nlinarith [sq_nonneg (2 * di + dj), sq_nonneg dj]

/-- A linear residue assigned to a triangular-lattice index. -/
def linearResidueSix (a b : ZMod 6) (i j : ℤ) : ZMod 6 :=
  a * i + b * j

/-- Every pair of coefficients modulo six satisfies a relation represented by
one of the nonzero triangular-lattice vectors of norm `1`, `3`, or `4`. -/
private lemma short_relation_mod_six (a b : ZMod 6) :
    a = 0 ∨ b = 0 ∨ a - b = 0 ∨ a + b = 0 ∨
      2 * a - b = 0 ∨ a - 2 * b = 0 ∨
      2 * a = 0 ∨ 2 * b = 0 ∨ 2 * a - 2 * b = 0 := by
  letI : DecidableEq (ZMod 6) := ZMod.decidableEq 6
  fin_cases a <;> fin_cases b <;> decide

/-- **Short-kernel theorem.** Every linear map `ℤ² → ZMod 6` has a
nonzero kernel vector whose triangular-lattice squared norm is at most four. -/
theorem linearResidueSix_has_short_kernel (a b : ZMod 6) :
    ∃ di dj : ℤ,
      (di, dj) ≠ (0, 0) ∧
      triangularLatticeNorm di dj ≤ 4 ∧
      linearResidueSix a b di dj = 0 := by
  rcases short_relation_mod_six a b with
    ha | hb | hab | hab | hab | hab | ha | hb | hab
  · refine ⟨1, 0, by norm_num, by norm_num [triangularLatticeNorm], ?_⟩
    simp [linearResidueSix, ha]
  · refine ⟨0, 1, by norm_num, by norm_num [triangularLatticeNorm], ?_⟩
    simp [linearResidueSix, hb]
  · refine ⟨1, -1, by norm_num, by norm_num [triangularLatticeNorm], ?_⟩
    simpa [linearResidueSix, sub_eq_add_neg, mul_comm] using hab
  · refine ⟨1, 1, by norm_num, by norm_num [triangularLatticeNorm], ?_⟩
    simpa [linearResidueSix] using hab
  · refine ⟨2, -1, by norm_num, by norm_num [triangularLatticeNorm], ?_⟩
    simpa [linearResidueSix, sub_eq_add_neg, mul_comm] using hab
  · refine ⟨1, -2, by norm_num, by norm_num [triangularLatticeNorm], ?_⟩
    simpa [linearResidueSix, sub_eq_add_neg, mul_comm] using hab
  · refine ⟨2, 0, by norm_num, by norm_num [triangularLatticeNorm], ?_⟩
    simpa [linearResidueSix, mul_comm] using ha
  · refine ⟨0, 2, by norm_num, by norm_num [triangularLatticeNorm], ?_⟩
    simpa [linearResidueSix, mul_comm] using hb
  · refine ⟨2, -2, by norm_num, by norm_num [triangularLatticeNorm], ?_⟩
    simpa [linearResidueSix, sub_eq_add_neg, mul_comm] using hab

/-- The bound four is attained by the coefficient pair `(1, 3)`: every
nonzero vector in its kernel has triangular-lattice norm at least four. -/
theorem linearResidueSix_one_three_kernel_norm_ge_four
    {di dj : ℤ} (hnonzero : (di, dj) ≠ (0, 0))
    (hkernel : linearResidueSix 1 3 di dj = 0) :
    4 ≤ triangularLatticeNorm di dj := by
  by_contra hnot
  have hnorm_le : triangularLatticeNorm di dj ≤ 3 := by omega
  have hfirst : 4 * triangularLatticeNorm di dj =
      (2 * di + dj) ^ 2 + 3 * dj ^ 2 := by
    simp only [triangularLatticeNorm]
    ring
  have hsecond : 4 * triangularLatticeNorm di dj =
      (di + 2 * dj) ^ 2 + 3 * di ^ 2 := by
    simp only [triangularLatticeNorm]
    ring
  have hdi_sq : di ^ 2 ≤ 4 := by
    nlinarith [sq_nonneg (di + 2 * dj)]
  have hdj_sq : dj ^ 2 ≤ 4 := by
    nlinarith [sq_nonneg (2 * di + dj)]
  have hdi_lower : -2 ≤ di := by nlinarith [sq_nonneg (di + 2)]
  have hdi_upper : di ≤ 2 := by nlinarith [sq_nonneg (di - 2)]
  have hdj_lower : -2 ≤ dj := by nlinarith [sq_nonneg (dj + 2)]
  have hdj_upper : dj ≤ 2 := by nlinarith [sq_nonneg (dj - 2)]
  have hdiv : (6 : ℤ) ∣ di + 3 * dj := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    push_cast
    simpa [linearResidueSix, mul_comm] using hkernel
  interval_cases di <;> interval_cases dj <;>
    norm_num [triangularLatticeNorm] at *

/-- The coefficient pair `(1, 3)` has a nonzero kernel vector of norm four. -/
theorem linearResidueSix_one_three_has_norm_four_kernel :
    (0, (2 : ℤ)) ≠ (0, 0) ∧
      triangularLatticeNorm 0 2 = 4 ∧
      linearResidueSix 1 3 0 2 = 0 := by
  norm_num [triangularLatticeNorm]
  rfl

/-- No linear six-residue coloring has the norm-seven separation certificate
that drives the Isbell seven-color construction. -/
theorem no_linearResidueSix_normSeven_separation (a b : ZMod 6) :
    ¬ ∀ di dj : ℤ,
      (di, dj) ≠ (0, 0) →
      linearResidueSix a b di dj = 0 →
      7 ≤ triangularLatticeNorm di dj := by
  intro hseparated
  obtain ⟨di, dj, hnonzero, hshort, hkernel⟩ :=
    linearResidueSix_has_short_kernel a b
  have hlong := hseparated di dj hnonzero hkernel
  omega

end HadwigerNelsonBounds
