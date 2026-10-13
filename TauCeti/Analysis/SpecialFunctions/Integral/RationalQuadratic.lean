/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import TauCeti.MeasureTheory.Integral.ExpDecay
public import Mathlib.Analysis.PSeries

/-!
# Rational quadratic integrals

Establishes integrability and values of one- and two-denominator Cauchy rational integrals,
including the coincident-pole case. The results apply to general positive parameters and do
not depend on a particular Fourier kernel. The hyperbolic-weight application is developed in
`Fourier.HaagerupZsido.OddPole`.
-/

public section

namespace TauCeti
namespace RationalQuadratic

open MeasureTheory Set Filter Asymptotics
open scoped BigOperators

noncomputable section

/-- Integrability of a rescaled Cauchy kernel. -/
theorem integrable_inv_sq_add_sq {c : ℝ} (hc : c ≠ 0) :
    Integrable (fun x : ℝ => (c ^ 2 + x ^ 2)⁻¹) := by
  have hcomp := integrable_inv_one_add_sq.comp_mul_left' (inv_ne_zero hc)
  have hscaled := hcomp.const_mul (c⁻¹ ^ 2)
  apply hscaled.congr
  filter_upwards [] with x
  have hden : c ^ 2 + x ^ 2 ≠ 0 := by
    nlinarith [sq_pos_of_ne_zero hc, sq_nonneg x]
  have hbase : 1 + (c⁻¹ * x) ^ 2 ≠ 0 := by positivity
  field_simp [hc, hden, hbase]

/-- Integral of a Cauchy kernel over the positive half-line. -/
theorem integral_Ioi_inv_sq_add_sq {c : ℝ} (hc : 0 < c) :
    (∫ x : ℝ in Set.Ioi 0, (c ^ 2 + x ^ 2)⁻¹) =
      Real.pi / (2 * c) := by
  have hchange := integral_comp_mul_left_Ioi
    (fun x : ℝ => (1 + x ^ 2)⁻¹) 0 (inv_pos.mpr hc)
  have hleft :
      (∫ x : ℝ in Set.Ioi 0, (1 + (c⁻¹ * x) ^ 2)⁻¹) =
        c ^ 2 * ∫ x : ℝ in Set.Ioi 0, (c ^ 2 + x ^ 2)⁻¹ := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    have hden : c ^ 2 + x ^ 2 ≠ 0 := by
      nlinarith [sq_pos_of_pos hc, sq_nonneg x]
    have hbase : 1 + (c⁻¹ * x) ^ 2 ≠ 0 := by positivity
    field_simp [hc.ne', hden, hbase]
  rw [hleft] at hchange
  simp only [mul_zero, integral_Ioi_inv_one_add_sq, Real.arctan_zero,
    sub_zero, inv_inv, smul_eq_mul] at hchange
  field_simp [hc.ne'] at hchange ⊢
  nlinarith

/-- The repeated-pole Cauchy integral needed when the two positive parameters
coincide. -/
theorem integral_Ioi_sq_div_sq_add_sq_sq {c : ℝ} (hc : 0 < c) :
    (∫ x : ℝ in Set.Ioi 0, x ^ 2 / (c ^ 2 + x ^ 2) ^ 2) =
      Real.pi / (4 * c) := by
  let g : ℝ → ℝ := (id : ℝ → ℝ) / fun x => c ^ 2 + x ^ 2
  let g' : ℝ → ℝ := fun x =>
    (1 * (c ^ 2 + x ^ 2) - x * ((2 : ℝ) * x ^ (2 - 1))) /
      (c ^ 2 + x ^ 2) ^ 2
  have hderiv (x : ℝ) := by
    have hden : c ^ 2 + x ^ 2 ≠ 0 := by
      nlinarith [sq_pos_of_pos hc, sq_nonneg x]
    exact (hasDerivAt_id x).div ((hasDerivAt_pow 2 x).const_add (c ^ 2)) hden
  have hCauchy : Integrable (fun x : ℝ => (c ^ 2 + x ^ 2)⁻¹) :=
    integrable_inv_sq_add_sq hc.ne'
  have hDerivInt : Integrable g' := by
    apply hCauchy.mono'
    · dsimp only [g']
      have hnum : Continuous (fun x : ℝ =>
          1 * (c ^ 2 + x ^ 2) - x * ((2 : ℝ) * x ^ (2 - 1))) := by
        fun_prop
      have hden : Continuous (fun x : ℝ => (c ^ 2 + x ^ 2) ^ 2) := by
        fun_prop
      exact (hnum.div hden fun x => pow_ne_zero _ (by
        nlinarith [sq_pos_of_pos hc, sq_nonneg x])).aestronglyMeasurable
    · filter_upwards [] with x
      have hden : 0 < c ^ 2 + x ^ 2 := by
        nlinarith [sq_pos_of_pos hc, sq_nonneg x]
      have habs : |c ^ 2 - x ^ 2| ≤ c ^ 2 + x ^ 2 := by
        rw [abs_sub_le_iff]
        constructor <;> nlinarith [sq_nonneg c, sq_nonneg x]
      dsimp only [g']
      have hnum : 1 * (c ^ 2 + x ^ 2) - x * ((2 : ℝ) * x ^ (2 - 1)) =
          c ^ 2 - x ^ 2 := by norm_num; ring
      rw [hnum]
      rw [Real.norm_eq_abs, abs_div, abs_pow, abs_of_pos hden]
      calc
        |c ^ 2 - x ^ 2| / (c ^ 2 + x ^ 2) ^ 2 ≤
            (c ^ 2 + x ^ 2) / (c ^ 2 + x ^ 2) ^ 2 :=
          div_le_div_of_nonneg_right habs (sq_nonneg _)
        _ = (c ^ 2 + x ^ 2)⁻¹ := by
          field_simp [hden.ne']
  have hgTop : Tendsto g atTop (nhds 0) := by
    have hInv : Tendsto (fun x : ℝ => x⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero
    have hDen : Tendsto (fun x : ℝ => c ^ 2 * x⁻¹ ^ 2 + 1) atTop (nhds 1) := by
      simpa using ((hInv.pow 2).const_mul (c ^ 2)).add tendsto_const_nhds
    have hQuot := hInv.div hDen one_ne_zero
    norm_num only [zero_div] at hQuot
    apply hQuot.congr'
    filter_upwards [eventually_gt_atTop 0] with x hx
    dsimp only [g]
    have hx0 : x ≠ 0 := hx.ne'
    -- states the goal with the definition unfolded, in the shape the next step needs;
    -- there is no `_apply` lemma to rewrite with here.
    change x⁻¹ / (c ^ 2 * x⁻¹ ^ 2 + 1) = x / (c ^ 2 + x ^ 2)
    field_simp [hx0]
  have hDerivIntegral : (∫ x : ℝ in Set.Ioi 0, g' x) = 0 := by
    have h := integral_Ioi_of_hasDerivAt_of_tendsto'
      (a := 0) (m := 0) (fun x _ => hderiv x) hDerivInt.integrableOn hgTop
    simpa [g, g'] using h
  calc
    (∫ x : ℝ in Set.Ioi 0, x ^ 2 / (c ^ 2 + x ^ 2) ^ 2) =
        ∫ x : ℝ in Set.Ioi 0,
          (1 / 2 : ℝ) * (c ^ 2 + x ^ 2)⁻¹ - (1 / 2 : ℝ) * g' x := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x _
      dsimp only [g']
      have hnum : 1 * (c ^ 2 + x ^ 2) - x * ((2 : ℝ) * x ^ (2 - 1)) =
          c ^ 2 - x ^ 2 := by norm_num; ring
      rw [hnum]
      have hden : c ^ 2 + x ^ 2 ≠ 0 := by
        nlinarith [sq_pos_of_pos hc, sq_nonneg x]
      field_simp [hden]
      ring
    _ = (1 / 2 : ℝ) * (∫ x : ℝ in Set.Ioi 0, (c ^ 2 + x ^ 2)⁻¹) -
        (1 / 2 : ℝ) * ∫ x : ℝ in Set.Ioi 0, g' x := by
      rw [integral_sub (hCauchy.const_mul _).integrableOn
        (hDerivInt.const_mul _).integrableOn, integral_const_mul, integral_const_mul]
    _ = Real.pi / (4 * c) := by
      rw [integral_Ioi_inv_sq_add_sq hc, hDerivIntegral]
      field_simp [hc.ne']
      ring

/-- The elementary two-Cauchy-denominator integral. -/
theorem integral_Ioi_sq_div_two_quadratics
    {a c : ℝ} (ha : 0 ≤ a) (hc : 0 < c) :
    (∫ y : ℝ in Set.Ioi 0,
        y ^ 2 / ((y ^ 2 + c ^ 2) * (y ^ 2 + a ^ 2))) =
      Real.pi / (2 * (a + c)) := by
  rcases ha.eq_or_lt with rfl | haPos
  · calc
      (∫ y : ℝ in Set.Ioi 0,
          y ^ 2 / ((y ^ 2 + c ^ 2) * (y ^ 2 + 0 ^ 2))) =
          ∫ y : ℝ in Set.Ioi 0, (c ^ 2 + y ^ 2)⁻¹ := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro y hy
        have hy0 : y ≠ 0 := hy.ne'
        have hcden : c ^ 2 + y ^ 2 ≠ 0 := by
          nlinarith [sq_pos_of_pos hc, sq_nonneg y]
        field_simp [hy0, hcden]
        ring
      _ = Real.pi / (2 * c) := integral_Ioi_inv_sq_add_sq hc
      _ = Real.pi / (2 * (0 + c)) := by ring
  · by_cases hac : a = c
    · subst a
      calc
        (∫ y : ℝ in Set.Ioi 0,
            y ^ 2 / ((y ^ 2 + c ^ 2) * (y ^ 2 + c ^ 2))) =
            ∫ y : ℝ in Set.Ioi 0, y ^ 2 / (c ^ 2 + y ^ 2) ^ 2 := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro y _
          ring_nf
        _ = Real.pi / (4 * c) := integral_Ioi_sq_div_sq_add_sq_sq hc
        _ = Real.pi / (2 * (c + c)) := by ring
    · have hdiff : c ^ 2 - a ^ 2 ≠ 0 := by
        rw [sub_ne_zero]
        intro hsq
        rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hsq) with h | h
        · exact hac h.symm
        · nlinarith
      have hCInt : Integrable (fun y : ℝ => (c ^ 2 + y ^ 2)⁻¹) :=
        integrable_inv_sq_add_sq hc.ne'
      have hAInt : Integrable (fun y : ℝ => (a ^ 2 + y ^ 2)⁻¹) :=
        integrable_inv_sq_add_sq haPos.ne'
      calc
        (∫ y : ℝ in Set.Ioi 0,
            y ^ 2 / ((y ^ 2 + c ^ 2) * (y ^ 2 + a ^ 2))) =
            ∫ y : ℝ in Set.Ioi 0,
              (c ^ 2 / (c ^ 2 - a ^ 2)) * (c ^ 2 + y ^ 2)⁻¹ -
                (a ^ 2 / (c ^ 2 - a ^ 2)) * (a ^ 2 + y ^ 2)⁻¹ := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro y _
          have hcden : c ^ 2 + y ^ 2 ≠ 0 := by
            nlinarith [sq_pos_of_pos hc, sq_nonneg y]
          have haden : a ^ 2 + y ^ 2 ≠ 0 := by
            nlinarith [sq_pos_of_pos haPos, sq_nonneg y]
          field_simp [hdiff, hcden, haden]
          ring
        _ = (c ^ 2 / (c ^ 2 - a ^ 2)) *
              (∫ y : ℝ in Set.Ioi 0, (c ^ 2 + y ^ 2)⁻¹) -
            (a ^ 2 / (c ^ 2 - a ^ 2)) *
              ∫ y : ℝ in Set.Ioi 0, (a ^ 2 + y ^ 2)⁻¹ := by
          rw [integral_sub (hCInt.const_mul _).integrableOn
            (hAInt.const_mul _).integrableOn, integral_const_mul, integral_const_mul]
        _ = (c ^ 2 / (c ^ 2 - a ^ 2)) * (Real.pi / (2 * c)) -
            (a ^ 2 / (c ^ 2 - a ^ 2)) * (Real.pi / (2 * a)) := by
          rw [integral_Ioi_inv_sq_add_sq hc, integral_Ioi_inv_sq_add_sq haPos]
        _ = Real.pi / (2 * (a + c)) := by
          have hsum : a + c ≠ 0 := by positivity
          field_simp [hdiff, hc.ne', haPos.ne', hsum]
          ring

/-- Integrability of the nonnegative rational kernel used in the telescoping
argument. -/
theorem integrable_sq_div_two_quadratics
    (a : ℝ) {c : ℝ} (hc : 0 < c) :
    Integrable (fun y : ℝ =>
      y ^ 2 / ((y ^ 2 + c ^ 2) * (y ^ 2 + a ^ 2))) := by
  have hCauchy : Integrable (fun y : ℝ => (c ^ 2 + y ^ 2)⁻¹) :=
    integrable_inv_sq_add_sq hc.ne'
  apply hCauchy.mono'
  · exact (by fun_prop : Measurable (fun y : ℝ =>
      y ^ 2 / ((y ^ 2 + c ^ 2) * (y ^ 2 + a ^ 2)))).aestronglyMeasurable
  · filter_upwards [] with y
    by_cases hy : y = 0
    · subst y
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add,
        zero_div, norm_zero, add_zero, inv_nonneg]
      positivity
    · have hySq : 0 < y ^ 2 := sq_pos_of_ne_zero hy
      have hC : 0 < y ^ 2 + c ^ 2 := by positivity
      have hA : 0 < y ^ 2 + a ^ 2 := by positivity
      have hquot : 0 ≤ y ^ 2 / ((y ^ 2 + c ^ 2) * (y ^ 2 + a ^ 2)) := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg hquot]
      calc
        y ^ 2 / ((y ^ 2 + c ^ 2) * (y ^ 2 + a ^ 2)) ≤
            (y ^ 2 + a ^ 2) / ((y ^ 2 + c ^ 2) * (y ^ 2 + a ^ 2)) :=
          div_le_div_of_nonneg_right (by nlinarith [sq_nonneg a]) (by positivity)
        _ = (c ^ 2 + y ^ 2)⁻¹ := by
          field_simp [hC.ne', hA.ne']
          ring

end

end RationalQuadratic
end TauCeti
