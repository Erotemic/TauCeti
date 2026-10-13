/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# A nowhere-vanishing function in complex L²

A σ-finite measure has a strictly positive integrable function. Taking its square root
constructs a complex L² function which is nonzero everywhere, and hence an L² vector
nonzero almost everywhere. This is useful for maximal spectral vectors.

Nonvanishing is sufficient for the pushforward of |F|² · μ to have the same measure
class as the pushforward of μ. The reverse implication need not hold for a
noninjective pushforward map.
-/

public section

open MeasureTheory

open scoped ENNReal

namespace TauCeti

variable {α : Type*} [MeasurableSpace α]

/-- **A σ-finite measure carries a nowhere-vanishing square-integrable function.**

Take a positive integrable `w` from σ-finiteness and use its pointwise square root: squaring
turns the `L²` condition into the `L¹` condition that `w` already satisfies. -/
theorem exists_ae_ne_zero_memLp_two (ρ : Measure α) [SigmaFinite ρ] :
    ∃ f : α → ℂ, MemLp f 2 ρ ∧ ∀ x, f x ≠ 0 := by
  obtain ⟨w, hwpos, hwmeas, hwint⟩ :=
    MeasureTheory.exists_pos_lintegral_lt_of_sigmaFinite ρ (ε := 1) one_ne_zero
  refine ⟨fun x => ((Real.sqrt (w x) : ℝ) : ℂ), ?_, ?_⟩
  · have hfmeas : AEStronglyMeasurable
        (fun x => ((Real.sqrt (w x) : ℝ) : ℂ)) ρ :=
      (Complex.continuous_ofReal.measurable.comp
        (Real.continuous_sqrt.measurable.comp
          (measurable_coe_nnreal_real.comp hwmeas))).aestronglyMeasurable
    -- `MemLp` is an a.e.-measurability condition together with finite `eLpNorm`.
    -- The measurability half is already provided by `hfmeas`.
    change eLpNorm (fun x => ((Real.sqrt (w x) : ℝ) : ℂ)) 2 ρ < ∞
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num) hfmeas]
    have hcongr : ∫⁻ x, ‖((Real.sqrt (w x) : ℝ) : ℂ)‖ₑ ^ ((2 : ℝ≥0∞).toReal) ∂ρ
        = ∫⁻ x, (w x : ℝ≥0∞) ∂ρ := by
      refine lintegral_congr fun x => ?_
      have hnorm : ‖((Real.sqrt (w x) : ℝ) : ℂ)‖ = Real.sqrt (w x) := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      rw [show ((2 : ℝ≥0∞).toReal) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast,
        ← ofReal_norm, hnorm, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _),
        Real.sq_sqrt (w x).coe_nonneg, ENNReal.ofReal_coe_nnreal]
    rw [hcongr]
    exact hwint.trans_le le_top
  · intro x
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt (Real.sqrt_pos.mpr (NNReal.coe_pos.mpr (hwpos x)))

/-- **A σ-finite measure carries an almost-everywhere nonvanishing `L²` vector.** -/
theorem exists_ae_ne_zero_lp_two (ρ : Measure α) [SigmaFinite ρ] :
    ∃ F : Lp ℂ 2 ρ, ∀ᵐ x ∂ρ, (F : α → ℂ) x ≠ 0 := by
  obtain ⟨f, hmem, hne⟩ := exists_ae_ne_zero_memLp_two ρ
  refine ⟨hmem.toLp f, ?_⟩
  filter_upwards [hmem.coeFn_toLp] with x hx
  rw [hx]
  exact hne x

end TauCeti
