/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import HadwigerNelsonBounds.PartsSpindle

/-!
# Kernel-checked Hadwiger--Nelson bounds

This library proves the currently known bounds `5 ≤ χ(ℝ²) ≤ 7` for the
unit-distance graph of the Euclidean plane.  The upper bound is an explicit
Isbell-style coloring.  The lower bound checks Parts' 481-vertex certificate,
embeds a finite doubled triangular-lattice gadget, and closes the final
spindle.

The exact chromatic number remains open: this does not decide whether it is
five, six, or seven, and therefore does not solve Erdős Problem 508.
-/
