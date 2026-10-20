/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Ring

/-!
# Uniform interval grids on the real line

For a positive width `ε`, the half-open intervals
`[k * ε, (k + 1) * ε)`, indexed by integers, partition the real line.
A point belongs to the cell indexed by `⌊s / ε⌋`, and the distance
from a point to the cell's left endpoint is bounded by the width.

Mathlib's integer-smul interval lemmas give disjointness and covering directly
after unfolding `gridCell`. The grid can be used to decompose real spectral parameters
or to bound functions locally on each interval.

For the partition properties, use `Set.pairwise_disjoint_Ico_zsmul` from
`Mathlib.Algebra.Order.Interval.Set.Group`, `Set.iUnion_Ico_zsmul` from
`Mathlib.Algebra.Order.ToIntervalMod`, and `existsUnique_zsmul_near_of_pos` from
`Mathlib.Algebra.Order.Archimedean.Basic`. Measurability follows from
`measurableSet_Ico` in `Mathlib.MeasureTheory.Constructions.BorelSpace.Order`.

Adapted from the Kitware DKPS formalization,
`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralGrid.lean`.
-/

public section

open Set

namespace TauCeti

/-- The half-open interval between successive integer multiples of `ε`. -/
def gridCell (ε : ℝ) (k : ℤ) : Set ℝ :=
  Ico (k • ε) ((k + 1) • ε)

/-- The multiplicative form of the endpoints of a grid cell. -/
theorem gridCell_eq_Ico (ε : ℝ) (k : ℤ) :
    gridCell ε k = Ico ((k : ℝ) * ε) (((k : ℝ) + 1) * ε) := by
  simp only [gridCell, zsmul_eq_mul, Int.cast_add, Int.cast_one]

/-- Membership in a grid cell is given by its two endpoint inequalities. -/
@[simp] theorem mem_gridCell {ε : ℝ} {k : ℤ} {s : ℝ} :
    s ∈ gridCell ε k ↔ (k : ℝ) * ε ≤ s ∧ s < ((k : ℝ) + 1) * ε := by
  rw [gridCell_eq_Ico]
  exact Iff.rfl

/-- For positive width, the index of the grid cell containing `s` is `⌊s / ε⌋`. -/
theorem mem_gridCell_iff_floor {ε : ℝ} (hε : 0 < ε) (k : ℤ) (s : ℝ) :
    s ∈ gridCell ε k ↔ ⌊s / ε⌋ = k := by
  rw [mem_gridCell, Int.floor_eq_iff]
  constructor
  · rintro ⟨hl, hu⟩
    exact ⟨(le_div_iff₀ hε).2 hl, (div_lt_iff₀ hε).2 hu⟩
  · rintro ⟨hl, hu⟩
    exact ⟨(le_div_iff₀ hε).1 hl, (div_lt_iff₀ hε).1 hu⟩

/-- Every point belongs to the grid cell indexed by the floor of its scaled value. -/
theorem mem_gridCell_floor {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    s ∈ gridCell ε ⌊s / ε⌋ := by
  rw [mem_gridCell_iff_floor hε]

/-- A cell containing a point must have strictly positive width. -/
theorem pos_of_mem_gridCell {ε : ℝ} {k : ℤ} {s : ℝ}
    (hs : s ∈ gridCell ε k) : 0 < ε := by
  obtain ⟨hl, hu⟩ := mem_gridCell.mp hs
  linarith

/-- Membership in a cell bounds the distance to its left endpoint by its width. -/
theorem abs_sub_le_of_mem_gridCell {ε : ℝ} {k : ℤ} {s : ℝ}
    (hs : s ∈ gridCell ε k) :
    |s - (k : ℝ) * ε| ≤ ε := by
  have hε : 0 < ε := pos_of_mem_gridCell hs
  obtain ⟨hl, hu⟩ := mem_gridCell.mp hs
  rw [abs_le]
  constructor <;> nlinarith [hε]

/-- Membership in a cell controls the absolute value of its points. -/
theorem abs_le_of_mem_gridCell {ε : ℝ} {k : ℤ} {s : ℝ}
    (hs : s ∈ gridCell ε k) :
    |s| ≤ (|(k : ℝ)| + 1) * ε := by
  have hε : 0 ≤ ε := (pos_of_mem_gridCell hs).le
  have hdist : |s - (k : ℝ) * ε| ≤ ε := abs_sub_le_of_mem_gridCell hs
  calc
    |s| = |(s - (k : ℝ) * ε) + (k : ℝ) * ε| := by rw [sub_add_cancel]
    _ ≤ |s - (k : ℝ) * ε| + |(k : ℝ) * ε| := abs_add_le _ _
    _ ≤ ε + |(k : ℝ)| * ε := by
      rw [abs_mul, abs_of_nonneg hε]
      exact add_le_add hdist (le_refl (|(k : ℝ)| * ε))
    _ = (|(k : ℝ)| + 1) * ε := by
      rw [add_mul, one_mul, add_comm]

end TauCeti
