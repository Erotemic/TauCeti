/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.PSeries
public import TauCeti.Analysis.Fourier.ExpNegAbs

/-!
# Poisson summation for the Cauchy kernel

For `y > 0`, Poisson summation identifies the integer lattice sum of a two-sided
exponential with the lattice sum of its Cauchy (Lorentzian) Fourier transform.
The result also evaluates the full Cauchy lattice by elementary geometric sums.

This is the `SSP-A18` Cauchy Poisson obligation in the
`SpectralSubspacePerturbation` roadmap. The later odd-pole hyperbolic-weight
expansion `SSP-A19` is already available upstream via a different argument;
it is not duplicated here. The local asymptotic estimates are included so
this module does not depend on any unmerged SSP-A16 branch.

## Provenance

Adapted from `ForTauCeti/Analysis/Fourier/Poisson/CauchyLattice.lean`
in AIQ-Kitware/aiq-dkps-formalization (Apache-2.0), where the Poisson and
Cauchy-lattice arguments were authored by Jon Crall and GPT 5.6 High.
The Fourier-transform evaluation is reused from TauCeti's accepted
`TauCeti.Analysis.Fourier.ExpNegAbs` instead of porting it again.
-/

public section

namespace TauCeti
namespace HaagerupZsido

open MeasureTheory Set Filter Asymptotics
open scoped BigOperators FourierTransform

noncomputable section

/-- Two-sided exponentials decay faster than every real inverse power. -/
private theorem cexp_neg_mul_abs_isLittleO_rpow_cocompact
    {a : ℝ} (ha : 0 < a) (s : ℝ) :
    (fun x : ℝ => Complex.exp ((-(a * |x|) : ℝ) : ℂ))
      =o[cocompact ℝ] (fun x : ℝ => |x| ^ s) := by
  apply IsLittleO.of_norm_left
  simp only [Complex.norm_exp, Complex.ofReal_re]
  rw [cocompact_eq_atBot_atTop, isLittleO_sup]
  constructor
  · have h := (isLittleO_exp_neg_mul_rpow_atTop ha s).comp_tendsto
      tendsto_neg_atBot_atTop
    refine h.congr' ?_ ?_
    · filter_upwards [eventually_lt_atBot 0] with x hx
      simp [abs_of_neg hx]
    · filter_upwards [eventually_lt_atBot 0] with x hx
      simp [abs_of_neg hx]
  · refine (isLittleO_exp_neg_mul_rpow_atTop ha s).congr' ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with x hx
      simp [abs_of_pos hx]
    · filter_upwards [eventually_gt_atTop 0] with x hx
      simp [abs_of_pos hx]

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
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hquot_nonneg,
    Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg x) _)]
  rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num,
    Real.rpow_neg (abs_nonneg x), Real.rpow_two, sq_abs]
  calc
    y / (Real.pi * (y ^ 2 + x ^ 2)) =
        (y / Real.pi) / (y ^ 2 + x ^ 2) := by
      field_simp [Real.pi_ne_zero]
    _ ≤ (y / Real.pi) / x ^ 2 := by
      exact div_le_div_of_nonneg_left (by positivity) (sq_pos_of_ne_zero hx0)
        (by nlinarith [sq_nonneg y])
    _ = (y / Real.pi) * (x ^ 2)⁻¹ := div_eq_mul_inv _ _

/-- The positive tail of the geometric exponential series. -/
private theorem tsum_nat_exp_neg_mul_add_one {a : ℝ} (ha : 0 < a) :
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
private theorem tsum_int_exp_neg_mul_abs {a : ℝ} (ha : 0 < a) :
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

/-- **Poisson summation for the Cauchy lattice.** For `y > 0`, summing the two-sided
exponential on the integers equals the sampled Fourier transform, a Cauchy series. -/
theorem tsum_complexExp_eq_tsum_cauchy {y : ℝ} (hy : 0 < y) :
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

/-- The Cauchy lattice sum, written in exponential rather than hyperbolic
notation. -/
theorem tsum_int_inv_sq_add_sq
    {y : ℝ} (hy : 0 < y) :
    (∑' n : ℤ, (y ^ 2 + (n : ℝ) ^ 2)⁻¹) =
      (Real.pi / y) *
        ((1 + Real.exp (-(2 * Real.pi * y))) /
          (1 - Real.exp (-(2 * Real.pi * y)))) := by
  let q : ℝ := Real.exp (-(2 * Real.pi * y))
  let Q : ℝ := (1 + q) / (1 - q)
  have hscale : 0 < 2 * Real.pi * y := by positivity
  have hexpReal :
      (∑' n : ℤ, Real.exp (-(2 * Real.pi * y) * |(n : ℝ)|)) = Q := by
    simpa only [Q, q, neg_mul] using tsum_int_exp_neg_mul_abs hscale
  have hexpComplex :
      (∑' n : ℤ,
          Complex.exp ((-(2 * Real.pi * y * |(n : ℝ)|) : ℝ) : ℂ)) =
        (Q : ℂ) := by
    calc
      (∑' n : ℤ,
          Complex.exp ((-(2 * Real.pi * y * |(n : ℝ)|) : ℝ) : ℂ)) =
          ∑' n : ℤ, (Real.exp (-(2 * Real.pi * y) * |(n : ℝ)|) : ℂ) := by
        apply tsum_congr
        intro n
        rw [Complex.ofReal_exp]
        congr 1
        norm_cast
        ring
      _ = (((∑' n : ℤ,
          Real.exp (-(2 * Real.pi * y) * |(n : ℝ)|)) : ℝ) : ℂ) :=
        (Complex.ofReal_tsum _).symm
      _ = (Q : ℂ) := by rw [hexpReal]
  have hPoisson := tsum_complexExp_eq_tsum_cauchy hy
  have hscaled :
      (Q : ℂ) = ((y / Real.pi : ℝ) : ℂ) *
        ∑' n : ℤ, (((y ^ 2 + (n : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) := by
    calc
      (Q : ℂ) = ∑' n : ℤ,
          ((y / (Real.pi * (y ^ 2 + (n : ℝ) ^ 2)) : ℝ) : ℂ) := by
        rw [← hPoisson, hexpComplex]
      _ = ∑' n : ℤ, ((y / Real.pi : ℝ) : ℂ) *
          (((y ^ 2 + (n : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) := by
        apply tsum_congr
        intro n
        norm_cast
        have hden : y ^ 2 + (n : ℝ) ^ 2 ≠ 0 := by
          nlinarith [sq_nonneg (n : ℝ)]
        field_simp [Real.pi_ne_zero, hden]
      _ = ((y / Real.pi : ℝ) : ℂ) *
          ∑' n : ℤ, (((y ^ 2 + (n : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) := tsum_mul_left
  apply Complex.ofReal_injective
  rw [Complex.ofReal_tsum]
  calc
    (∑' n : ℤ, (((y ^ 2 + (n : ℝ) ^ 2)⁻¹ : ℝ) : ℂ)) =
        (((Real.pi / y : ℝ) : ℂ) * (((y / Real.pi : ℝ) : ℂ) *
          ∑' n : ℤ, (((y ^ 2 + (n : ℝ) ^ 2)⁻¹ : ℝ) : ℂ))) := by
      push_cast
      field_simp [Real.pi_ne_zero, hy.ne']
    _ = (((Real.pi / y : ℝ) : ℂ) * (Q : ℂ)) := by rw [← hscaled]
    _ = (((Real.pi / y) * Q : ℝ) : ℂ) := by push_cast; rfl
    _ = (((Real.pi / y) *
        ((1 + Real.exp (-(2 * Real.pi * y))) /
          (1 - Real.exp (-(2 * Real.pi * y)))) : ℝ) : ℂ) := rfl

end

end HaagerupZsido
end TauCeti
