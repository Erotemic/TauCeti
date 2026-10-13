/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic


/-!
# Bounded multiplication operators on complex L²

A bounded measurable complex symbol acts by a continuous linear operator on L².
The `mulLp` construction records the operator norm bound; `coeFn_mulLp` identifies its
a.e. representatives, and `mulLp_congr_ae` shows only the a.e. class of the symbol matters.

The Radon–Nikodym and composition intertwinings are stated in their respective transport modules.
-/

public section

open MeasureTheory

open scoped ENNReal

namespace TauCeti

variable {α : Type*} [MeasurableSpace α]


section Multiplication

/-- A uniformly bounded measurable function multiplies `L²` into itself. -/
theorem memLp_two_mul_complex (ρ : Measure α) {g : α → ℂ} (hg : Measurable g) {C : ℝ}
    (hgC : ∀ x, ‖g x‖ ≤ C) (F : Lp ℂ 2 ρ) : MemLp (fun x => g x * F x) 2 ρ := by
  refine MemLp.mono' ((Lp.memLp F).norm.const_mul C)
    (hg.aestronglyMeasurable.mul (Lp.aestronglyMeasurable F)) ?_
  filter_upwards with x
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hgC x) (norm_nonneg _)

/-- **The seminorm bound for multiplication by a uniformly bounded function.**

Stated with `|C|` rather than `C`: a bound hypothesis `∀ x, ‖g x‖ ≤ C` does not force `0 ≤ C`
when the space is empty, and `ENNReal.ofReal` would silently truncate a negative `C`. -/
theorem eLpNorm_two_mul_le (ρ : Measure α) {g : α → ℂ} (hg : Measurable g)
    {C : ℝ} (hgC : ∀ x, ‖g x‖ ≤ C) (f : α → ℂ)
    (hf : AEStronglyMeasurable f ρ) :
    eLpNorm (fun x => g x * f x) 2 ρ ≤ ENNReal.ofReal |C| * eLpNorm f 2 ρ := by
  have hle : eLpNorm (fun x => g x * f x) 2 ρ ≤ eLpNorm (((|C| : ℝ) : ℂ) • f) 2 ρ := by
    refine eLpNorm_mono_ae (hg.aestronglyMeasurable.mul hf)
      (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_abs]
    exact mul_le_mul_of_nonneg_right ((hgC x).trans (le_abs_self C)) (norm_nonneg _)
  rw [eLpNorm_const_smul] at hle
  refine hle.trans_eq ?_
  congr 1
  rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_abs]

/-- **The bound that makes multiplication a bounded operator** on `L²`. -/
theorem norm_toLp_mul_le (ρ : Measure α) {g : α → ℂ} (hg : Measurable g) {C : ℝ}
    (hgC : ∀ x, ‖g x‖ ≤ C) (F : Lp ℂ 2 ρ) :
    ‖MemLp.toLp (fun x => g x * F x) (memLp_two_mul_complex ρ hg hgC F)‖ ≤ |C| * ‖F‖ := by
  rw [Lp.norm_toLp, Lp.norm_def, ← ENNReal.toReal_ofReal (abs_nonneg C), ← ENNReal.toReal_mul]
  refine ENNReal.toReal_mono ?_ (eLpNorm_two_mul_le ρ hg hgC _ (Lp.aestronglyMeasurable F))
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top F)

/-- **Multiplication by a bounded measurable function**, as a bounded operator on `L²`.

This is the "multiplication operator" of the multiplication models of spectral multiplicity
theory, for an arbitrary measure on an arbitrary measurable space. -/
noncomputable def mulLp (ρ : Measure α) {g : α → ℂ} (hg : Measurable g) {C : ℝ}
    (hgC : ∀ x, ‖g x‖ ≤ C) : Lp ℂ 2 ρ →L[ℂ] Lp ℂ 2 ρ :=
  LinearMap.mkContinuous
    { toFun := fun F => MemLp.toLp (fun x => g x * F x) (memLp_two_mul_complex ρ hg hgC F)
      map_add' := fun F G => by
        rw [← MemLp.toLp_add (memLp_two_mul_complex ρ hg hgC F) (memLp_two_mul_complex ρ hg hgC G)]
        refine (MemLp.toLp_eq_toLp_iff _ _).2 ?_
        filter_upwards [Lp.coeFn_add F G] with x hx
        simp only [Pi.add_apply, hx]
        ring
      map_smul' := fun c F => by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul c (memLp_two_mul_complex ρ hg hgC F)]
        refine (MemLp.toLp_eq_toLp_iff _ _).2 ?_
        filter_upwards [Lp.coeFn_smul c F] with x hx
        simp only [Pi.smul_apply, hx, smul_eq_mul]
        ring }
    |C| (norm_toLp_mul_le ρ hg hgC)

/-- The multiplication operator, unfolded. -/
theorem mulLp_apply (ρ : Measure α) {g : α → ℂ} (hg : Measurable g) {C : ℝ}
    (hgC : ∀ x, ‖g x‖ ≤ C) (F : Lp ℂ 2 ρ) :
    mulLp ρ hg hgC F = MemLp.toLp (fun x => g x * F x) (memLp_two_mul_complex ρ hg hgC F) := (rfl)

/-- The multiplication operator really is pointwise multiplication. -/
theorem coeFn_mulLp (ρ : Measure α) {g : α → ℂ} (hg : Measurable g) {C : ℝ}
    (hgC : ∀ x, ‖g x‖ ≤ C) (F : Lp ℂ 2 ρ) :
    (mulLp ρ hg hgC F : α → ℂ) =ᵐ[ρ] fun x => g x * F x := by
  rw [mulLp_apply]
  exact MemLp.coeFn_toLp _

end Multiplication

/-- **The multiplication operator depends on its symbol only almost everywhere.**

Two symbols that agree `ρ`-almost everywhere -- for instance the same function truncated at two
different bounds, both larger than the essential supremum -- define the same bounded operator on
`L²(ρ)`. -/
theorem mulLp_congr_ae (ρ : Measure α) {g g' : α → ℂ} (hg : Measurable g) (hg' : Measurable g')
    {C C' : ℝ} (hgC : ∀ x, ‖g x‖ ≤ C) (hgC' : ∀ x, ‖g' x‖ ≤ C') (h : g =ᵐ[ρ] g') :
    mulLp ρ hg hgC = mulLp ρ hg' hgC' := by
  refine ContinuousLinearMap.ext fun F => Lp.ext ?_
  filter_upwards [coeFn_mulLp ρ hg hgC F, coeFn_mulLp ρ hg' hgC' F, h] with x h1 h2 h3
  rw [h1, h2, h3]


end TauCeti
