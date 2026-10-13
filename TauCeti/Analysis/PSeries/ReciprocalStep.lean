/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Telescoping reciprocal series

The successive differences `(a + 2n + 1)⁻¹ - (a + 2n + 3)⁻¹` telescope to `(a + 1)⁻¹`
for `0 ≤ a`. This lemma is independent of any Fourier kernel.
-/

public section

namespace TauCeti
namespace ReciprocalSeries

open MeasureTheory Set Filter Asymptotics
open scoped BigOperators

noncomputable section

/-- The elementary reciprocal series telescopes by steps of two. -/
theorem hasSum_reciprocal_step_difference
    {a : ℝ} (ha : 0 ≤ a) :
    HasSum (fun n : ℕ =>
      (a + 2 * n + 1)⁻¹ - (a + 2 * n + 3)⁻¹) (a + 1)⁻¹ := by
  let u : ℕ → ℝ := fun n => (a + 2 * n + 1)⁻¹
  have hnonneg : ∀ n : ℕ, 0 ≤ u n - u (n + 1) := by
    intro n
    dsimp only [u]
    have hleft : 0 < a + 2 * (n : ℝ) + 1 := by positivity
    have hright : 0 < a + 2 * ((n + 1 : ℕ) : ℝ) + 1 := by positivity
    apply sub_nonneg.mpr
    exact (inv_le_inv₀ hright hleft).2 (by push_cast; linarith)
  have hfinite : ∀ N : ℕ,
      (∑ n ∈ Finset.range N, (u n - u (n + 1))) = u 0 - u N := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
        rw [Finset.sum_range_succ, ih]
        ring
  have hDenTop : Tendsto (fun n : ℕ => a + 2 * (n : ℝ) + 1) atTop atTop := by
    convert tendsto_atTop_add_const_right atTop (a + 1)
      (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 2)) using 1
    funext n
    ring
  have huZero : Tendsto u atTop (nhds 0) := by
    exact hDenTop.inv_tendsto_atTop
  rw [show (fun n : ℕ =>
      (a + 2 * n + 1)⁻¹ - (a + 2 * n + 3)⁻¹) =
      fun n : ℕ => u n - u (n + 1) by
    funext n
    dsimp only [u]
    push_cast
    congr 2
    ring]
  apply (hasSum_iff_tendsto_nat_of_nonneg hnonneg _).2
  convert tendsto_const_nhds.sub huZero using 1
  · funext N
    exact hfinite N
  · dsimp only [u]
    norm_num

end

end ReciprocalSeries
end TauCeti
