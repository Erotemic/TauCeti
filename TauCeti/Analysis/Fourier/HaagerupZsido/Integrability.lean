/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import TauCeti.Analysis.Fourier.HaagerupZsido.Defs
public import TauCeti.Analysis.SpecialFunctions.Integral.SineLaplace

/-!
# Integrability and exact mass of the Haagerup--Zsidó kernel

Proves a product-integrability certificate for the hyperbolic-weight/sine integrand. The
weighted sine Laplace integral reduces to the Cauchy kernel `2 / (1 + y²)`, allowing Fubini's
interchange and the exact reciprocal-kernel mass `π / 2`. This mass enters the sharp
spectral-subspace perturbation constant.
-/

public section

namespace TauCeti
namespace HaagerupZsido

open MeasureTheory Set Filter Asymptotics
open scoped BigOperators

noncomputable section

/-- The hyperbolic weight cancels the geometric quotient of the absolute-sine
Laplace transform. -/
private theorem weight_mul_exp_ratio {y : ℝ} (hy : 0 < y) :
    weight y * ((1 + Real.exp (-Real.pi * y)) /
      (1 - Real.exp (-Real.pi * y))) = 1 := by
  have hq1 : Real.exp (-(Real.pi * y)) < 1 :=
    Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
  have hne : 1 - Real.exp (-(Real.pi * y)) ≠ 0 := by linarith
  have hpos : (0 : ℝ) < 1 + Real.exp (-(Real.pi * y)) := by positivity
  rw [weight_eq_exp_quotient, show -Real.pi * y = -(Real.pi * y) by ring]
  field_simp

/-- For a positive Laplace parameter the weighted absolute-sine integral is a Cauchy
rational function. This identity is shared by the product-integrability and mass proofs. -/
theorem integral_weight_mul_abs_sin_exp {y : ℝ} (hy : 0 < y) :
    (∫ t : ℝ, weight y * (|Real.sin t| * Real.exp (-y * |t|))) =
      2 * (1 + y ^ 2)⁻¹ := by
  have hq1 : Real.exp (-Real.pi * y) < 1 :=
    Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
  have hne : 1 - Real.exp (-Real.pi * y) ≠ 0 := by linarith
  have hy2 : (1 : ℝ) + y ^ 2 ≠ 0 := by positivity
  calc
    (∫ t : ℝ, weight y * (|Real.sin t| * Real.exp (-y * |t|))) =
        weight y * ∫ t : ℝ, |Real.sin t| * Real.exp (-y * |t|) :=
      integral_const_mul _ _
    _ = (weight y * ((1 + Real.exp (-Real.pi * y)) /
          (1 - Real.exp (-Real.pi * y)))) * (2 * (1 + y ^ 2)⁻¹) := by
      rw [Real.integral_abs_sin_mul_exp_neg_abs hy]
      field_simp
    _ = 2 * (1 + y ^ 2)⁻¹ := by
      rw [weight_mul_exp_ratio hy, one_mul]

/-- The kernel double integrand is integrable on the product of the positive
weight half-line with the full time line.  This single certificate powers
both the exact mass identity and the later Fourier exchange. -/
theorem integrable_kernel_prod :
    Integrable (Function.uncurry fun y t =>
      weight y * (|Real.sin t| * Real.exp (-y * |t|)))
      ((volume.restrict (Set.Ioi 0)).prod volume) := by
  have hcont : Continuous (Function.uncurry fun y t =>
      weight y * (|Real.sin t| * Real.exp (-y * |t|))) :=
    (continuous_weight.comp continuous_fst).mul
      (((Real.continuous_sin.comp continuous_snd).abs).mul
        (Real.continuous_exp.comp (continuous_fst.neg.mul continuous_snd.abs)))
  rw [integrable_prod_iff hcont.aestronglyMeasurable]
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact (Real.integrable_abs_sin_mul_exp_neg_abs hy).const_mul (weight y)
  · have hint : Integrable (fun y : ℝ => 2 * (1 + y ^ 2)⁻¹) :=
      integrable_inv_one_add_sq.const_mul 2
    apply hint.integrableOn.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy0 : (0 : ℝ) < y := hy
    calc
      2 * (1 + y ^ 2)⁻¹ =
          ∫ t : ℝ, weight y * (|Real.sin t| * Real.exp (-y * |t|)) :=
        (integral_weight_mul_abs_sin_exp hy0).symm
      _ = ∫ t : ℝ, ‖weight y * (|Real.sin t| * Real.exp (-y * |t|))‖ := by
        apply integral_congr_ae
        filter_upwards [] with t
        rw [Real.norm_eq_abs, abs_of_nonneg
          (mul_nonneg (weight_nonneg hy0.le)
            (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le))]

/-- The full-line sine-weighted Laplace mass. -/
private theorem integral_abs_sin_mul_weightLaplaceTransform :
    (∫ t : ℝ, |Real.sin t| * weightLaplaceTransform t) = Real.pi := by
  have hswap := integral_integral_swap integrable_kernel_prod
  have hleft :
      (∫ y in Set.Ioi (0 : ℝ),
        ∫ t : ℝ, weight y * (|Real.sin t| * Real.exp (-y * |t|))) =
        Real.pi := by
    calc
      (∫ y in Set.Ioi (0 : ℝ),
          ∫ t : ℝ, weight y * (|Real.sin t| * Real.exp (-y * |t|))) =
          ∫ y in Set.Ioi (0 : ℝ), 2 * (1 + y ^ 2)⁻¹ := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro y hy
        have hy0 : (0 : ℝ) < y := hy
        exact integral_weight_mul_abs_sin_exp hy0
      _ = 2 * ∫ y in Set.Ioi (0 : ℝ), (1 + y ^ 2)⁻¹ := by
        rw [integral_const_mul]
      _ = Real.pi := by
        rw [integral_Ioi_inv_one_add_sq, Real.arctan_zero, sub_zero]
        ring
  have hright :
      (∫ t : ℝ,
        ∫ y in Set.Ioi (0 : ℝ), weight y * (|Real.sin t| * Real.exp (-y * |t|))) =
        ∫ t : ℝ, |Real.sin t| * weightLaplaceTransform t := by
    apply integral_congr_ae
    filter_upwards [] with t
    rw [weightLaplaceTransform_def, ← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y _
    dsimp only
    rw [show -|t| * y = -y * |t| by ring]
    ring
  rw [← hright, ← hswap, hleft]

/-- Integrability of the even envelope of the kernel. -/
private theorem integrable_abs_sin_mul_weightLaplaceTransform :
    Integrable (fun t : ℝ => |Real.sin t| * weightLaplaceTransform t) := by
  have hswap := integrable_kernel_prod.swap
  have h2 := ((integrable_prod_iff hswap.aestronglyMeasurable).mp hswap).2
  apply h2.congr
  filter_upwards [] with t
  calc
    (∫ y in Set.Ioi (0 : ℝ),
        ‖(Function.uncurry fun y t =>
          weight y * (|Real.sin t| * Real.exp (-y * |t|))) ((t, y).swap)‖) =
        ∫ y in Set.Ioi (0 : ℝ), |Real.sin t| * (weight y * Real.exp (-|t| * y)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y hy
      have hy0 : (0 : ℝ) < y := hy
      simp only [Prod.swap_prod_mk, Function.uncurry_apply_pair]
      rw [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (weight_nonneg hy0.le)
          (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)),
        -- states the goal with the definition unfolded, in the shape the next step needs;
        -- there is no `_apply` lemma to rewrite with here.
        show -|t| * y = -y * |t| by ring]
      ring
    _ = |Real.sin t| * weightLaplaceTransform t := by
      rw [integral_const_mul, weightLaplaceTransform_def]

/-- The real kernel is integrable. -/
private theorem integrable_realKernel : Integrable realKernel := by
  apply integrable_abs_sin_mul_weightLaplaceTransform.mono'
    measurable_realKernel.aestronglyMeasurable
  filter_upwards [] with t
  rw [Real.norm_eq_abs, abs_realKernel]
  have h1 := weightLaplaceTransform_nonneg t
  have h2 := abs_nonneg (Real.sin t)
  nlinarith

/-- The reciprocal kernel is integrable. -/
theorem integrable_reciprocalKernel : Integrable reciprocalKernel := by
  rw [funext reciprocalKernel_def]
  exact integrable_realKernel.ofReal.const_mul (-Complex.I)

/-- The exact `L¹` mass of the real kernel. -/
private theorem integral_abs_realKernel : (∫ t : ℝ, |realKernel t|) = Real.pi / 2 := by
  calc
    (∫ t : ℝ, |realKernel t|) =
        ∫ t : ℝ, (1 / 2 : ℝ) * (|Real.sin t| * weightLaplaceTransform t) := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [abs_realKernel]
      ring
    _ = (1 / 2 : ℝ) * ∫ t : ℝ, |Real.sin t| * weightLaplaceTransform t :=
      integral_const_mul _ _
    _ = Real.pi / 2 := by
      rw [integral_abs_sin_mul_weightLaplaceTransform]
      ring

/-- **Exact mass.**  The reciprocal kernel has `L¹` norm exactly `π / 2`. -/
theorem integral_norm_reciprocalKernel :
    (∫ t : ℝ, ‖reciprocalKernel t‖) = Real.pi / 2 := by
  calc
    (∫ t : ℝ, ‖reciprocalKernel t‖) = ∫ t : ℝ, |realKernel t| := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [norm_reciprocalKernel]
    _ = Real.pi / 2 := integral_abs_realKernel

end

end HaagerupZsido
end TauCeti
