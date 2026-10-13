/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import Mathlib.MeasureTheory.Integral.ExpDecay

/-!
# The Haagerup--Zsidó kernel: definitions and elementary properties

Defines the hyperbolic weight `w(y) = tanh (πy/2)`, its one-sided Laplace transform `L(t)`,
the real kernel `r(t) = (sin t / 2) * L(t)`, and the reciprocal kernel `k(t) = -i * r(t)`.

Records positivity, continuity, parity, measurability, and the norm formula needed for the
kernel's integrability and Fourier calculations. Its Fourier integral becomes real after the
rotation by `-i`.
-/

public section

namespace TauCeti
namespace HaagerupZsido

open MeasureTheory Set

noncomputable section

/-- The positive hyperbolic weight in the limiting Haagerup--Zsidó kernel. -/
def weight (y : ℝ) : ℝ :=
  Real.tanh (Real.pi * y / 2)

/-- Rewrite form of `weight`, for `simp only` chains that must unfold the weight without
unfolding the surrounding kernel. -/
theorem weight_def (y : ℝ) : weight y = Real.tanh (Real.pi * y / 2) :=
  (rfl)

/-- The hyperbolic weight is nonnegative on the half-line `0 ≤ y`, which is the only range the
Laplace transform integrates over. -/
theorem weight_nonneg {y : ℝ} (hy : 0 ≤ y) : 0 ≤ weight y := by
  rw [weight, Real.tanh_eq]
  have hmono : Real.exp (- (Real.pi * y / 2)) ≤
      Real.exp (Real.pi * y / 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos]
  positivity

private theorem weight_le_one (y : ℝ) : weight y ≤ 1 :=
  (Real.tanh_lt_one _).le

/-- Exponential form of the hyperbolic weight. -/
theorem weight_eq_exp_quotient (y : ℝ) :
    weight y =
      (1 - Real.exp (-(Real.pi * y))) /
        (1 + Real.exp (-(Real.pi * y))) := by
  let z : ℝ := Real.pi * y / 2
  have htwo : Real.exp (-(Real.pi * y)) = Real.exp (-z) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    dsimp only [z]
    ring
  rw [weight, show Real.pi * y / 2 = z by rfl, Real.tanh_eq, htwo,
    Real.exp_neg z]
  have hne : Real.exp z ≠ 0 := Real.exp_ne_zero _
  field_simp [hne]

/-! ### The explicit kernel

The Laplace transform integrates the weight over the positive half-line. The sine factor
makes the real kernel odd, and multiplying by `-i` produces the reciprocal kernel.
-/

/-- The Laplace transform of the hyperbolic weight at `|t|`, the inner factor of
the limiting Haagerup--Zsidó kernel. -/
def weightLaplaceTransform (t : ℝ) : ℝ :=
  ∫ y in Set.Ioi (0 : ℝ), weight y * Real.exp (-|t| * y)

/-- Rewrite form of `weightLaplaceTransform` as an integral over `Ioi 0`. -/
theorem weightLaplaceTransform_def (t : ℝ) :
    weightLaplaceTransform t = ∫ y in Set.Ioi (0 : ℝ), weight y * Real.exp (-|t| * y) :=
  (rfl)

/-- The real Haagerup--Zsidó kernel at the sharp parameter. -/
def realKernel (t : ℝ) : ℝ :=
  (Real.sin t / 2) * weightLaplaceTransform t

/-- Rewrite form of `realKernel` as the sine multiple of the weight's Laplace transform. -/
theorem realKernel_def (t : ℝ) :
    realKernel t = (Real.sin t / 2) * weightLaplaceTransform t :=
  (rfl)

/-- The complex reciprocal kernel `-i f₀`. -/
def reciprocalKernel (t : ℝ) : ℂ :=
  -Complex.I * (realKernel t : ℂ)

/-- Rewrite form of `reciprocalKernel` as `-i` times the real kernel. -/
theorem reciprocalKernel_def (t : ℝ) :
    reciprocalKernel t = -Complex.I * (realKernel t : ℂ) :=
  (rfl)

/-- The hyperbolic weight is continuous. -/
theorem continuous_weight : Continuous weight := by
  -- Use the exponential quotient with its nonvanishing denominator.
  have h : weight = fun y =>
      (1 - Real.exp (-(Real.pi * y))) / (1 + Real.exp (-(Real.pi * y))) := by
    funext y
    exact weight_eq_exp_quotient y
  rw [h]
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro y
  positivity

/-- The Laplace transform of the weight is nonnegative, being the integral of a nonnegative
integrand over `Ioi 0`.  This is what lets `abs_realKernel` strip the absolute value. -/
theorem weightLaplaceTransform_nonneg (t : ℝ) : 0 ≤ weightLaplaceTransform t :=
  setIntegral_nonneg measurableSet_Ioi fun _y hy =>
    mul_nonneg (weight_nonneg (le_of_lt hy)) (Real.exp_pos _).le

private theorem weightLaplaceTransform_neg (t : ℝ) :
    weightLaplaceTransform (-t) = weightLaplaceTransform t := by
  simp only [weightLaplaceTransform_def, abs_neg]

private theorem measurable_weightLaplaceTransform : Measurable weightLaplaceTransform := by
  have hcont : Continuous fun p : ℝ × ℝ =>
      weight p.2 * Real.exp (-|p.1| * p.2) :=
    (continuous_weight.comp continuous_snd).mul
      (Real.continuous_exp.comp ((continuous_fst.abs.neg).mul continuous_snd))
  exact hcont.stronglyMeasurable.integral_prod_right'.measurable

/-- The real kernel is measurable. -/
theorem measurable_realKernel : Measurable realKernel :=
  (Real.measurable_sin.div_const 2).mul measurable_weightLaplaceTransform

/-- The complex reciprocal kernel is measurable. -/
theorem measurable_reciprocalKernel : Measurable reciprocalKernel :=
  (Complex.measurable_ofReal.comp measurable_realKernel).const_mul (-Complex.I)

private theorem realKernel_neg (t : ℝ) : realKernel (-t) = -realKernel t := by
  simp only [realKernel_def, Real.sin_neg, weightLaplaceTransform_neg]
  ring

/-- The reciprocal kernel is odd. The Fourier integral of the real odd kernel is purely
imaginary; the factor `-i` in the reciprocal kernel makes its Fourier integral real. -/
theorem reciprocalKernel_neg (t : ℝ) :
    reciprocalKernel (-t) = -reciprocalKernel t := by
  simp only [reciprocalKernel_def, realKernel_neg, Complex.ofReal_neg]
  ring

/-- Multiplication by `-i` is an isometry, so the reciprocal kernel has the same modulus as the
real kernel. -/
theorem norm_reciprocalKernel (t : ℝ) : ‖reciprocalKernel t‖ = |realKernel t| := by
  simp [reciprocalKernel_def]

/-- Modulus of the real kernel, with the absolute value pushed onto the sine factor alone --
the Laplace transform is already nonnegative. -/
theorem abs_realKernel (t : ℝ) :
    |realKernel t| = |Real.sin t| / 2 * weightLaplaceTransform t := by
  rw [realKernel_def, abs_mul, abs_div, abs_two,
    abs_of_nonneg (weightLaplaceTransform_nonneg t)]

end

end HaagerupZsido
end TauCeti
