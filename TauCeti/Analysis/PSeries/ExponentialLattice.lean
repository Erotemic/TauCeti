/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.Fourier.PoissonSummation

/-!
# Exponential lattice sums

Evaluates geometric sums of `exp (-a * n)` on positive and two-sided integer lattices when
`a > 0`. The two-sided identity is useful when applying Poisson summation to Cauchy kernels.
-/

public section

namespace TauCeti
namespace ExponentialLattice

open MeasureTheory Set Filter Asymptotics
open scoped BigOperators

noncomputable section

/-- The positive tail of the geometric exponential series. -/
theorem tsum_nat_exp_neg_mul_add_one {a : ℝ} (ha : 0 < a) :
    (∑' n : ℕ, Real.exp (-a * (n + 1 : ℕ))) =
      Real.exp (-a) / (1 - Real.exp (-a)) := by
  let q := Real.exp (-a)
  have hqpos : 0 < q := Real.exp_pos _
  have hqlt : q < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos ha)
  have hqnorm : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hqpos]
    exact hqlt
  calc
    (∑' n : ℕ, Real.exp (-a * (n + 1 : ℕ))) =
        ∑' n : ℕ, q ^ (n + 1) := by
      apply tsum_congr
      intro n
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    _ = ∑' n : ℕ, q ^ n * q := by simp_rw [pow_succ]
    _ = (∑' n : ℕ, q ^ n) * q := tsum_mul_right
    _ = (1 - q)⁻¹ * q := by rw [tsum_geometric_of_norm_lt_one hqnorm]
    _ = Real.exp (-a) / (1 - Real.exp (-a)) := by
      simp only [q, div_eq_mul_inv]
      ring

/-- The elementary two-sided geometric lattice sum. -/
theorem tsum_int_exp_neg_mul_abs {a : ℝ} (ha : 0 < a) :
    (∑' n : ℤ, Real.exp (-a * |(n : ℝ)|)) =
      (1 + Real.exp (-a)) / (1 - Real.exp (-a)) := by
  let f : ℤ → ℝ := fun n => Real.exp (-a * |(n : ℝ)|)
  let q := Real.exp (-a)
  have hqpos : 0 < q := Real.exp_pos _
  have hqlt : q < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos ha)
  have hqnorm : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hqpos]
    exact hqlt
  have hgeo : Summable (fun n : ℕ => q ^ n) :=
    (hasSum_geometric_of_norm_lt_one hqnorm).summable
  have hsum : Summable f := by
    apply Summable.of_nat_of_neg
    · refine hgeo.congr fun n => ?_
      -- states the goal with the definition unfolded, in the shape the next step needs;
      -- there is no `_apply` lemma to rewrite with here.
      change q ^ n = Real.exp (-a * |(((n : ℕ) : ℤ) : ℝ)|)
      rw [show |(((n : ℕ) : ℤ) : ℝ)| = (n : ℝ) by simp]
      simp only [q]
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    · refine hgeo.congr fun n => ?_
      -- states the goal with the definition unfolded, in the shape the next step needs;
      -- there is no `_apply` lemma to rewrite with here.
      change q ^ n = Real.exp (-a * |((-(n : ℤ) : ℤ) : ℝ)|)
      rw [show |((-(n : ℤ) : ℤ) : ℝ)| = (n : ℝ) by simp]
      simp only [q]
      rw [← Real.exp_nat_mul]
      congr 1
      ring
  have heven : Function.Even f := by
    intro n
    simp only [f, Int.cast_neg, abs_neg]
  have hpnat :
      (∑' n : ℕ+, f (n : ℤ)) =
        ∑' n : ℕ, Real.exp (-a * (n + 1 : ℕ)) := by
    calc
      (∑' n : ℕ+, f (n : ℤ)) = ∑' n : ℕ, f (Nat.succPNat n : ℤ) :=
        (Equiv.pnatEquivNat.symm.tsum_eq (fun n : ℕ+ => f (n : ℤ))).symm
      _ = ∑' n : ℕ, Real.exp (-a * (n + 1 : ℕ)) := by
        apply tsum_congr
        intro n
        dsimp only [f, Nat.succPNat]
        rw [abs_of_nonneg]
        · congr 1
        · positivity
  -- states the goal with the definition unfolded, in the shape the next step needs;
  -- there is no `_apply` lemma to rewrite with here.
  change ∑' n : ℤ, f n = _
  calc
    (∑' n : ℤ, f n) = f 0 + 2 • ∑' n : ℕ+, f (n : ℤ) :=
      tsum_int_eq_zero_add_two_mul_tsum_pnat heven hsum
    _ = 1 + 2 * (Real.exp (-a) / (1 - Real.exp (-a))) := by
      rw [hpnat, tsum_nat_exp_neg_mul_add_one ha]
      simp [f]
    _ = (1 + Real.exp (-a)) / (1 - Real.exp (-a)) := by
      have hne : 1 - Real.exp (-a) ≠ 0 := by
        have : Real.exp (-a) < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos ha)
        linarith
      field_simp [hne]
      ring

end

end ExponentialLattice
end TauCeti
