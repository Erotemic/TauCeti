/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import Mathlib.Analysis.Fourier.PoissonSummation
public import TauCeti.Analysis.Fourier.ExpNegAbs
public import TauCeti.Analysis.SpecialFunctions.ExpAbsDecay
public import TauCeti.Analysis.SpecialFunctions.ExpLatticeSum

/-!
# Poisson summation for the Cauchy kernel

For `y > 0`, Poisson summation identifies the two-sided exponential lattice
sum with the lattice sum of its Cauchy Fourier transform. Combined with the
geometric lattice series, this evaluates the full Cauchy lattice sum.

## Main results

* `TauCeti.tsum_cexp_neg_mul_abs_int_eq_tsum_div`: the sampled Fourier identity.
* `TauCeti.tsum_exp_neg_mul_abs_int_eq_tsum_div`: its real-valued form.
* `TauCeti.tsum_int_inv_sq_add_sq`: the Cauchy lattice sum in exponential form.

## Provenance

Adapted from `ForTauCeti/Analysis/Fourier/Poisson/CauchyLattice.lean`
in AIQ-Kitware/aiq-dkps-formalization (Apache-2.0; Jon Crall and GPT 5.6 High).
The Fourier-transform evaluation is reused from `TauCeti.Analysis.Fourier.ExpNegAbs`.
-/

public section

namespace TauCeti

open MeasureTheory Set Filter Asymptotics
open scoped BigOperators FourierTransform

noncomputable section

/-- The Cauchy function occurring as the transform has quadratic decay. -/
private theorem cauchy_fourier_isBigO_rpow_neg_two
    {y : ℝ} (hy : 0 < y) :
    (fun x : ℝ => ((y / (Real.pi * (y ^ 2 + x ^ 2)) : ℝ) : ℂ))
      =O[cocompact ℝ] (fun x : ℝ => |x| ^ (-2 : ℝ)) := by
  refine IsBigO.of_bound (y / Real.pi) ?_
  filter_upwards [isCompact_Icc.compl_mem_cocompact] with x hx
  have hxabs : 1 ≤ |x| := by
    have hnle : ¬ |x| ≤ 1 := by
      simpa only [mem_compl_iff, mem_Icc, abs_le] using hx
    exact (lt_of_not_ge hnle).le
  have hx0 : x ≠ 0 := by
    intro h
    subst x
    norm_num at hxabs
  have hsum_pos : 0 < y ^ 2 + x ^ 2 := by
    nlinarith [sq_pos_of_ne_zero hx0, sq_nonneg y]
  have hquot_nonneg : 0 ≤ y / (Real.pi * (y ^ 2 + x ^ 2)) := by positivity
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hquot_nonneg,
    Real.rpow_neg (abs_nonneg x), Real.rpow_two, sq_abs]
  rw [abs_of_nonneg (inv_nonneg.mpr (sq_nonneg x))]
  calc
    y / (Real.pi * (y ^ 2 + x ^ 2)) =
        (y / Real.pi) / (y ^ 2 + x ^ 2) := by
      field_simp [Real.pi_ne_zero]
    _ ≤ (y / Real.pi) / x ^ 2 := by
      exact div_le_div_of_nonneg_left (by positivity) (sq_pos_of_ne_zero hx0)
        (by nlinarith [sq_nonneg y])
    _ = (y / Real.pi) * (x ^ 2)⁻¹ := div_eq_mul_inv _ _

/-- **Poisson summation for the Cauchy lattice.** For `y > 0`, the lattice sum of
`exp (-2π y |n|)` is the sum of its sampled Cauchy Fourier transform. -/
theorem tsum_cexp_neg_mul_abs_int_eq_tsum_div {y : ℝ} (hy : 0 < y) :
    (∑' n : ℤ,
      Complex.exp ((-(2 * Real.pi * y * |(n : ℝ)|) : ℝ) : ℂ)) =
    ∑' n : ℤ, ((y / (Real.pi * (y ^ 2 + (n : ℝ) ^ 2)) : ℝ) : ℂ) := by
  let f : ℝ → ℂ := fun t => Complex.exp ((-(2 * Real.pi * y * |t|) : ℝ) : ℂ)
  have hscale : 0 < 2 * Real.pi * y := by positivity
  have hfContinuous : Continuous f := by
    dsimp only [f]
    fun_prop
  have hfDecay : f =O[cocompact ℝ] (fun x : ℝ => |x| ^ (-2 : ℝ)) :=
    (cexp_neg_mul_abs_isLittleO_rpow_cocompact hscale (-2)).isBigO
  have hFourier : 𝓕 f = fun x : ℝ =>
      ((y / (Real.pi * (y ^ 2 + x ^ 2)) : ℝ) : ℂ) := by
    funext x
    have hfun : f = fun t : ℝ => (Real.exp (-((2 * Real.pi * y) * |t|)) : ℂ) := by
      funext t
      simp only [f, Complex.ofReal_exp]
    rw [hfun, fourier_exp_neg_mul_abs hscale x]
    norm_cast
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    have hden : y ^ 2 + x ^ 2 ≠ 0 := by
      nlinarith [sq_nonneg x]
    field_simp [hpi, hden]
  have hFourierDecay : (𝓕 f) =O[cocompact ℝ]
      (fun x : ℝ => |x| ^ (-2 : ℝ)) := by
    rw [hFourier]
    exact cauchy_fourier_isBigO_rpow_neg_two hy
  have hPoisson := Real.tsum_eq_tsum_fourier_of_rpow_decay
    hfContinuous (by norm_num : (1 : ℝ) < 2) hfDecay hFourierDecay 0
  simpa only [f, zero_add, hFourier, Int.cast_zero, QuotientAddGroup.mk_zero,
    fourier_eval_zero, mul_one] using hPoisson

/-- The complex two-sided exponential lattice sum is the real exponential sum. -/
private theorem tsum_cexp_neg_two_pi_mul_abs_eq_ofReal (y : ℝ) :
    (∑' n : ℤ, Complex.exp ((-(2 * Real.pi * y * |(n : ℝ)|) : ℝ) : ℂ)) =
      ((∑' n : ℤ, Real.exp (-(2 * Real.pi * y) * |(n : ℝ)|) : ℝ) : ℂ) := by
  simpa only [neg_mul] using
    tsum_int_cexp_neg_mul_abs_eq_ofReal (2 * Real.pi * y)

/-- The real-valued Poisson identity for the two-sided exponential and Cauchy kernel. -/
theorem tsum_exp_neg_mul_abs_int_eq_tsum_div {y : ℝ} (hy : 0 < y) :
    (∑' n : ℤ, Real.exp (-(2 * Real.pi * y) * |(n : ℝ)|)) =
      ∑' n : ℤ, y / (Real.pi * (y ^ 2 + (n : ℝ) ^ 2)) := by
  apply Complex.ofReal_injective
  calc
    ((∑' n : ℤ, Real.exp (-(2 * Real.pi * y) * |(n : ℝ)|) : ℝ) : ℂ) =
        ∑' n : ℤ,
          Complex.exp ((-(2 * Real.pi * y * |(n : ℝ)|) : ℝ) : ℂ) :=
      (tsum_cexp_neg_two_pi_mul_abs_eq_ofReal y).symm
    _ = ∑' n : ℤ, ((y / (Real.pi * (y ^ 2 + (n : ℝ) ^ 2)) : ℝ) : ℂ) :=
      tsum_cexp_neg_mul_abs_int_eq_tsum_div hy
    _ = ((∑' n : ℤ, y / (Real.pi * (y ^ 2 + (n : ℝ) ^ 2)) : ℝ) : ℂ) :=
      (Complex.ofReal_tsum _).symm

/-- **Cauchy lattice sum.** Evaluating the Poisson identity gives the full sum
of `1 / (y² + n²)` over the integers. -/
theorem tsum_int_inv_sq_add_sq {y : ℝ} (hy : 0 < y) :
    (∑' n : ℤ, (y ^ 2 + (n : ℝ) ^ 2)⁻¹) =
      (Real.pi / y) *
        ((1 + Real.exp (-(2 * Real.pi * y))) /
          (1 - Real.exp (-(2 * Real.pi * y)))) := by
  have hscale : 0 < 2 * Real.pi * y := by positivity
  have hPoissonReal := tsum_exp_neg_mul_abs_int_eq_tsum_div hy
  -- Pull out the common scalar in the Cauchy sum before rearranging.
  have hscaled :
      (∑' n : ℤ, y / (Real.pi * (y ^ 2 + (n : ℝ) ^ 2))) =
        (y / Real.pi) * ∑' n : ℤ, (y ^ 2 + (n : ℝ) ^ 2)⁻¹ := by
    calc
      (∑' n : ℤ, y / (Real.pi * (y ^ 2 + (n : ℝ) ^ 2))) =
          ∑' n : ℤ, (y / Real.pi) * (y ^ 2 + (n : ℝ) ^ 2)⁻¹ := by
        apply tsum_congr
        intro n
        have hden : y ^ 2 + (n : ℝ) ^ 2 ≠ 0 := by
          nlinarith [sq_nonneg (n : ℝ)]
        field_simp [Real.pi_ne_zero, hden]
      _ = (y / Real.pi) * ∑' n : ℤ, (y ^ 2 + (n : ℝ) ^ 2)⁻¹ :=
        tsum_mul_left
  have hgeom :
      (∑' n : ℤ, Real.exp (-(2 * Real.pi * y) * |(n : ℝ)|)) =
        (1 + Real.exp (-(2 * Real.pi * y))) /
          (1 - Real.exp (-(2 * Real.pi * y))) := by
    simpa only [neg_mul] using tsum_int_exp_neg_mul_abs hscale
  have heq :
      (y / Real.pi) * ∑' n : ℤ, (y ^ 2 + (n : ℝ) ^ 2)⁻¹ =
        (1 + Real.exp (-(2 * Real.pi * y))) /
          (1 - Real.exp (-(2 * Real.pi * y))) := by
    rw [← hscaled, ← hPoissonReal]
    exact hgeom
  calc
    (∑' n : ℤ, (y ^ 2 + (n : ℝ) ^ 2)⁻¹) =
        (Real.pi / y) * ((y / Real.pi) *
          ∑' n : ℤ, (y ^ 2 + (n : ℝ) ^ 2)⁻¹) := by
      field_simp [Real.pi_ne_zero, hy.ne']
    _ = (Real.pi / y) *
          ((1 + Real.exp (-(2 * Real.pi * y))) /
            (1 - Real.exp (-(2 * Real.pi * y)))) := by
      rw [heq]

end

end TauCeti
