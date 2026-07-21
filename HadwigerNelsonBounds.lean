/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import HadwigerNelsonBounds.IsbellColoring

/-!
# Isbell's seven-coloring of the Euclidean plane

This library constructs a proper seven-coloring of the unit-distance graph on
the Euclidean plane. It formalizes the classical upper bound
`χ(ℝ²) ≤ 7` associated with the Hadwiger--Nelson problem and Erdős Problem 508.

The exact chromatic number of the plane and the known lower bound `5 ≤ χ(ℝ²)`
are not formalized here.
-/
