/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import TauCeti.Analysis.Fourier.HaagerupZsido.Defs
public import TauCeti.Analysis.Fourier.Poisson.CauchyLattice
public import TauCeti.Analysis.SpecialFunctions.Integral.RationalQuadratic
public import TauCeti.Analysis.PSeries.ReciprocalStep

/-!
# The odd-pole expansion of the Haagerup--Zsidó weight

Splitting the rational Cauchy lattice into even and odd terms expresses the hyperbolic
weight as an odd-pole sum. Integrating this expansion against the difference of adjacent
resolvents then gives the telescoping value `2 / (a + 1)`.

Generic Cauchy lattice sums, rational quadratic integrals, and the reciprocal telescoping
series are kept in their respective subject modules.
-/

public section

namespace TauCeti
namespace HaagerupZsido

open MeasureTheory Set Filter Asymptotics
open scoped BigOperators FourierTransform
open TauCeti.CauchyLattice TauCeti.RationalQuadratic TauCeti.ReciprocalSeries

noncomputable section

/-- The positive odd part of the Cauchy lattice. -/
theorem tsum_odd_inv_sq_add_sq
    {y : ℝ} (hy : 0 < y) :
    (∑' n : ℕ, (y ^ 2 + (((2 * n + 1 : ℕ) : ℝ) ^ 2))⁻¹) =
      (Real.pi / (4 * y)) * weight y := by
  let f : ℕ → ℝ := fun n => (y ^ 2 + (n : ℝ) ^ 2)⁻¹
  have hAll : Summable f := summable_nat_inv_sq_add_sq y
  have hmul : Function.Injective (fun n : ℕ => 2 * n) :=
    mul_right_injective₀ (by norm_num : (2 : ℕ) ≠ 0)
  have hEven := hAll.comp_injective hmul
  have hOdd := hAll.comp_injective ((add_left_injective 1).comp hmul)
  have hSplit := (hEven.hasSum.even_add_odd hOdd.hasSum).tsum_eq
  simp only [Function.comp_apply] at hSplit
  have hEvenScale :
      (∑' n : ℕ, f (2 * n)) =
        (1 / 4 : ℝ) * ∑' n : ℕ, ((y / 2) ^ 2 + (n : ℝ) ^ 2)⁻¹ := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    dsimp only [f]
    have hdenLeft : y ^ 2 + ((2 * n : ℕ) : ℝ) ^ 2 ≠ 0 := by
      nlinarith [sq_nonneg (((2 * n : ℕ) : ℝ))]
    have hdenRight : (y / 2) ^ 2 + (n : ℝ) ^ 2 ≠ 0 := by
      nlinarith [sq_nonneg (n : ℝ)]
    field_simp [hdenLeft, hdenRight]
    norm_num
    ring
  have hOddEq :
      (∑' n : ℕ, f (2 * n + 1)) =
        (∑' n : ℕ, f n) - (1 / 4 : ℝ) *
          ∑' n : ℕ, ((y / 2) ^ 2 + (n : ℝ) ^ 2)⁻¹ := by
    rw [← hEvenScale]
    linarith [hSplit]
  have hAllValue := tsum_nat_inv_sq_add_sq hy
  have hHalfValue := tsum_nat_inv_sq_add_sq (show 0 < y / 2 by positivity)
  rw [hAllValue, hHalfValue] at hOddEq
  let r : ℝ := Real.exp (-(Real.pi * y))
  have hrpos : 0 < r := Real.exp_pos _
  have hrlt : r < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
  have hFullExp : Real.exp (-(2 * Real.pi * y)) = r ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  have hHalfExp : Real.exp (-(2 * Real.pi * (y / 2))) = r := by
    dsimp only [r]
    congr 1
    ring
  have hInvHalf : (y / 2)⁻¹ ^ 2 = 4 * y⁻¹ ^ 2 := by
    field_simp [hy.ne']
    ring
  -- states the goal with the definition unfolded, in the shape the next step needs;
  -- there is no `_apply` lemma to rewrite with here.
  change (∑' n : ℕ, f (2 * n + 1)) = _
  calc
    (∑' n : ℕ, f (2 * n + 1)) =
        (1 / 2) *
            ((Real.pi / y) * ((1 + r ^ 2) / (1 - r ^ 2)) + y⁻¹ ^ 2) -
          (1 / 4) * ((1 / 2) *
            ((Real.pi / (y / 2)) * ((1 + r) / (1 - r)) +
              (y / 2)⁻¹ ^ 2)) := by
      simpa only [hFullExp, hHalfExp] using hOddEq
    _ = (Real.pi / (4 * y)) * weight y := by
      rw [weight_eq_exp_quotient, show Real.exp (-(Real.pi * y)) = r by rfl,
        hInvHalf]
      have hOneSub : 1 - r ≠ 0 := by linarith
      have hOneAdd : 1 + r ≠ 0 := by positivity
      have hSq : 1 - r ^ 2 ≠ 0 := by nlinarith
      field_simp [hy.ne', hOneSub, hOneAdd, hSq]
      ring

/-- Odd-pole partial-fraction expansion of the hyperbolic weight. -/
theorem weight_div_eq_tsum_odd
    {y : ℝ} (hy : 0 < y) :
    weight y / y =
      (4 / Real.pi) *
        ∑' n : ℕ, (y ^ 2 + (((2 * n + 1 : ℕ) : ℝ) ^ 2))⁻¹ := by
  rw [tsum_odd_inv_sq_add_sq hy]
  field_simp [Real.pi_ne_zero, hy.ne']

/-- Integrating the odd-pole expansion against a difference of two adjacent
resolvents produces the elementary step-two telescoping term. -/
theorem integral_weight_mul_reciprocal_difference
    {a : ℝ} (ha : 0 ≤ a) :
    (∫ y : ℝ in Set.Ioi 0,
        weight y * y *
          ((y ^ 2 + a ^ 2)⁻¹ - (y ^ 2 + (a + 2) ^ 2)⁻¹)) =
      2 / (a + 1) := by
  let c : ℕ → ℝ := fun n => 2 * n + 1
  let F : ℕ → ℝ → ℝ := fun n y =>
    (4 / Real.pi) *
      (y ^ 2 / ((y ^ 2 + (c n) ^ 2) * (y ^ 2 + a ^ 2)) -
        y ^ 2 / ((y ^ 2 + (c n) ^ 2) * (y ^ 2 + (a + 2) ^ 2)))
  have hc (n : ℕ) : 0 < c n := by
    dsimp only [c]
    positivity
  have hFInt (n : ℕ) : IntegrableOn (F n) (Set.Ioi 0) := by
    have hA := integrable_sq_div_two_quadratics a (hc n)
    have hB := integrable_sq_div_two_quadratics (a + 2) (hc n)
    exact ((hA.sub hB).const_mul (4 / Real.pi)).integrableOn
  have hFintegral (n : ℕ) :
      (∫ y : ℝ in Set.Ioi 0, F n y) =
        2 * ((a + 2 * n + 1)⁻¹ - (a + 2 * n + 3)⁻¹) := by
    have hA := integrable_sq_div_two_quadratics a (hc n)
    have hB := integrable_sq_div_two_quadratics (a + 2) (hc n)
    dsimp only [F]
    rw [integral_const_mul, integral_sub hA.integrableOn hB.integrableOn,
      integral_Ioi_sq_div_two_quadratics ha (hc n),
      integral_Ioi_sq_div_two_quadratics (by linarith : 0 ≤ a + 2) (hc n)]
    dsimp only [c]
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    have hleft : a + (2 * (n : ℝ) + 1) ≠ 0 := by positivity
    have hright : a + 2 + (2 * (n : ℝ) + 1) ≠ 0 := by positivity
    have hstepLeft : a + 2 * (n : ℝ) + 1 ≠ 0 := by positivity
    have hstepRight : a + 2 * (n : ℝ) + 3 ≠ 0 := by positivity
    field_simp [hpi, hleft, hright, hstepLeft, hstepRight]
    ring
  have hFnonneg (n : ℕ) {y : ℝ} (hy : y ∈ Set.Ioi (0 : ℝ)) : 0 ≤ F n y := by
    have hyPos : 0 < y := hy
    have hcommon : 0 < y ^ 2 + (c n) ^ 2 := by positivity
    have hA : 0 < y ^ 2 + a ^ 2 := by positivity
    have hAB : y ^ 2 + a ^ 2 ≤ y ^ 2 + (a + 2) ^ 2 := by
      nlinarith
    have hden :
        (y ^ 2 + (c n) ^ 2) * (y ^ 2 + a ^ 2) ≤
          (y ^ 2 + (c n) ^ 2) * (y ^ 2 + (a + 2) ^ 2) :=
      mul_le_mul_of_nonneg_left hAB hcommon.le
    have hquot :
        y ^ 2 / ((y ^ 2 + (c n) ^ 2) * (y ^ 2 + (a + 2) ^ 2)) ≤
          y ^ 2 / ((y ^ 2 + (c n) ^ 2) * (y ^ 2 + a ^ 2)) :=
      div_le_div_of_nonneg_left (sq_nonneg y) (mul_pos hcommon hA) hden
    dsimp only [F]
    positivity
  have hFnormIntegral (n : ℕ) :
      (∫ y : ℝ in Set.Ioi 0, ‖F n y‖) =
        2 * ((a + 2 * n + 1)⁻¹ - (a + 2 * n + 3)⁻¹) := by
    calc
      (∫ y : ℝ in Set.Ioi 0, ‖F n y‖) =
          ∫ y : ℝ in Set.Ioi 0, F n y := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro y hy
        -- names the application so the norm bound applies to it directly.
        change ‖F n y‖ = F n y
        rw [Real.norm_eq_abs, abs_of_nonneg (hFnonneg n hy)]
      _ = 2 * ((a + 2 * n + 1)⁻¹ - (a + 2 * n + 3)⁻¹) := hFintegral n
  have hNormSum : Summable (fun n : ℕ => ∫ y : ℝ in Set.Ioi 0, ‖F n y‖) := by
    apply ((hasSum_reciprocal_step_difference ha).summable.mul_left (2 : ℝ)).congr
    intro n
    exact (hFnormIntegral n).symm
  have hExchange :
      (∑' n : ℕ, ∫ y : ℝ in Set.Ioi 0, F n y) =
        ∫ y : ℝ in Set.Ioi 0, ∑' n : ℕ, F n y :=
    integral_tsum_of_summable_integral_norm hFInt hNormSum
  have hPointwise {y : ℝ} (hy : 0 < y) :
      (∑' n : ℕ, F n y) =
        weight y * y *
          ((y ^ 2 + a ^ 2)⁻¹ - (y ^ 2 + (a + 2) ^ 2)⁻¹) := by
    have hw := weight_div_eq_tsum_odd hy
    let D : ℝ := y ^ 2 *
      ((y ^ 2 + a ^ 2)⁻¹ - (y ^ 2 + (a + 2) ^ 2)⁻¹)
    calc
      (∑' n : ℕ, F n y) =
          ∑' n : ℕ, (4 / Real.pi) *
            (y ^ 2 + (2 * n + 1) ^ 2)⁻¹ * D := by
        apply tsum_congr
        intro n
        dsimp only [F, c, D]
        have hC : y ^ 2 + (2 * (n : ℝ) + 1) ^ 2 ≠ 0 := by positivity
        have hA : y ^ 2 + a ^ 2 ≠ 0 := by positivity
        have hB : y ^ 2 + (a + 2) ^ 2 ≠ 0 := by positivity
        field_simp [hC, hA, hB]
      _ = (4 / Real.pi) *
          ((∑' n : ℕ, (y ^ 2 + (2 * n + 1) ^ 2)⁻¹) * D) := by
        rw [← tsum_mul_right, ← tsum_mul_left]
        apply tsum_congr
        intro n
        ring
      _ = (weight y / y) * D := by
        have hw' : weight y / y =
            (4 / Real.pi) *
              ∑' n : ℕ, (y ^ 2 + (2 * (n : ℝ) + 1) ^ 2)⁻¹ := by
          simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hw
        rw [hw']
        ring
      _ = weight y * y *
          ((y ^ 2 + a ^ 2)⁻¹ - (y ^ 2 + (a + 2) ^ 2)⁻¹) := by
        dsimp only [D]
        field_simp [hy.ne']
  calc
    (∫ y : ℝ in Set.Ioi 0,
        weight y * y *
          ((y ^ 2 + a ^ 2)⁻¹ - (y ^ 2 + (a + 2) ^ 2)⁻¹)) =
        ∫ y : ℝ in Set.Ioi 0, ∑' n : ℕ, F n y := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y hy
      exact (hPointwise hy).symm
    _ = ∑' n : ℕ, ∫ y : ℝ in Set.Ioi 0, F n y := hExchange.symm
    _ = ∑' n : ℕ,
        2 * ((a + 2 * n + 1)⁻¹ - (a + 2 * n + 3)⁻¹) := by
      apply tsum_congr
      exact hFintegral
    _ = 2 * (a + 1)⁻¹ := by
      rw [tsum_mul_left, (hasSum_reciprocal_step_difference ha).tsum_eq]
    _ = 2 / (a + 1) := by rw [div_eq_mul_inv]

end

end HaagerupZsido
end TauCeti
