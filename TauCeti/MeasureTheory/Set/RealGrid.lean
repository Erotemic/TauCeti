/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Tactic

/-!
# Uniform measurable grids on the real line

For `ε > 0`, the half-open intervals `gridCell ε k = [k * ε, (k + 1) * ε)`, indexed by
integers, partition the real line into measurable cells. Every real number belongs to
exactly one cell; each cell has width `ε` and a bound in terms of its index.

These facts are useful when decomposing real-valued spectral parameters into countably
many measurable blocks, or when estimating a function locally on each block.

## Source

Adapted from the Kitware DKPS formalization,
`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralGrid.lean`.
-/

public section

open Set

namespace TauCeti

variable {ε : ℝ}

/-- The half-open cell with left endpoint `k * ε` and right endpoint `(k + 1) * ε`. -/
def gridCell (ε : ℝ) (k : ℤ) : Set ℝ :=
  Ico ((k : ℝ) * ε) (((k : ℝ) + 1) * ε)

/-- Every uniform grid cell is a measurable subset of the real line. -/
theorem measurableSet_gridCell (ε : ℝ) (k : ℤ) : MeasurableSet (gridCell ε k) :=
  measurableSet_Ico

/-- Distinct cells of a positive-width uniform grid are disjoint. -/
theorem pairwise_disjoint_gridCell (hε : 0 < ε) :
    Pairwise (Function.onFun Disjoint (gridCell ε)) := by
  intro k l hkl
  rw [Function.onFun, Set.disjoint_left]
  rintro x hxk hxl
  rcases lt_or_gt_of_ne hkl with h | h
  · have hkl' : ((k : ℝ) + 1) ≤ (l : ℝ) := by
      exact_mod_cast Int.add_one_le_iff.mpr h
    have : ((k : ℝ) + 1) * ε ≤ (l : ℝ) * ε := by
      nlinarith [hε.le]
    exact absurd (lt_of_lt_of_le hxk.2 this) (not_lt.mpr hxl.1)
  · have hlk' : ((l : ℝ) + 1) ≤ (k : ℝ) := by
      exact_mod_cast Int.add_one_le_iff.mpr h
    have : ((l : ℝ) + 1) * ε ≤ (k : ℝ) * ε := by
      nlinarith [hε.le]
    exact absurd (lt_of_lt_of_le hxl.2 this) (not_lt.mpr hxk.1)

/-- The countable family of positive-width grid cells covers the real line. -/
theorem iUnion_gridCell (hε : 0 < ε) : (⋃ k : ℤ, gridCell ε k) = univ := by
  ext x
  simp only [mem_iUnion, mem_univ, iff_true, gridCell, mem_Ico]
  refine ⟨⌊x / ε⌋, ?_, ?_⟩
  · rw [← le_div_iff₀ hε]
    exact Int.floor_le _
  · rw [← div_lt_iff₀ hε]
    exact Int.lt_floor_add_one _

/-- Every point in a cell has absolute value bounded by the size of its index and its width. -/
theorem abs_le_of_mem_gridCell (hε : 0 < ε) (k : ℤ) {s : ℝ}
    (hs : s ∈ gridCell ε k) :
    |s| ≤ (|(k : ℝ)| + 1) * ε := by
  obtain ⟨h1, h2⟩ := hs
  have hk : -|(k : ℝ)| ≤ (k : ℝ) := neg_abs_le _
  have hk' : (k : ℝ) ≤ |(k : ℝ)| := le_abs_self _
  rw [abs_le]
  constructor <;> nlinarith [hε.le, abs_nonneg ((k : ℝ))]

/-- The distance from a point in a grid cell to its left endpoint is at most its width. -/
theorem abs_sub_le_of_mem_gridCell (hε : 0 < ε) (k : ℤ) {s : ℝ}
    (hs : s ∈ gridCell ε k) :
    |s - (k : ℝ) * ε| ≤ ε := by
  obtain ⟨h1, h2⟩ := hs
  rw [abs_le]
  constructor <;> nlinarith

end TauCeti
