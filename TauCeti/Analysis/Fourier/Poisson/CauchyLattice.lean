/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import Mathlib.Analysis.Fourier.PoissonSummation
public import Mathlib.Analysis.PSeries
public import TauCeti.Analysis.PSeries.ExponentialLattice
public import TauCeti.Analysis.Fourier.ExponentialAbs

/-!
# Poisson summation and Cauchy lattice identities

The Fourier transform of the two-sided exponential yields a Poisson identity for the Cauchy
kernel. Evaluating the exponential lattice sum gives the full- and half-lattice rational sums.
The geometric lattice formulas live in `Analysis.PSeries.ExponentialLattice`; this module does
not depend on the Haagerup--Zsidó weight.
-/

public section

namespace TauCeti
namespace CauchyLattice

open TauCeti.ExponentialLattice

open MeasureTheory Set Filter Asymptotics
open scoped BigOperators FourierTransform

noncomputable section

/-- Poisson summation for the two-sided exponential, before evaluating its
geometric side. -/
theorem poisson_exponential_eq_cauchy_lattice
    {y : ℝ} (hy : 0 < y) :
    (∑' n : ℤ,
        Complex.exp ((-(2 * Real.pi * y * |(n : ℝ)|) : ℝ) : ℂ)) =
      ∑' n : ℤ,
        ((y / (Real.pi * (y ^ 2 + (n : ℝ) ^ 2)) : ℝ) : ℂ) := by
  let f : ℝ → ℂ := fun t =>
    Complex.exp ((-(2 * Real.pi * y * |t|) : ℝ) : ℂ)
  have hscale : 0 < 2 * Real.pi * y := by positivity
  have hfContinuous : Continuous f := by
    dsimp only [f]
    fun_prop
  have hfDecay : f =O[cocompact ℝ] (fun x : ℝ => |x| ^ (-2 : ℝ)) :=
    (cexp_neg_mul_abs_isLittleO_rpow_cocompact hscale (-2)).isBigO
  have hFourier : 𝓕 f = fun x : ℝ =>
      ((y / (Real.pi * (y ^ 2 + x ^ 2)) : ℝ) : ℂ) := by
    funext x
    exact fourier_cexp_neg_two_pi_mul_abs x hy
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
  have hPoisson := poisson_exponential_eq_cauchy_lattice hy
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

/-- The natural-number Cauchy series is summable, uniformly with respect to
the harmless nonnegative square added to its denominator. -/
theorem summable_nat_inv_sq_add_sq (y : ℝ) :
    Summable (fun n : ℕ => (y ^ 2 + (n : ℝ) ^ 2)⁻¹) := by
  have hmajor : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹) := by
    have h := Real.summable_nat_pow_inv.mpr (by norm_num : 1 < (2 : ℕ))
    simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr h
  have htail : Summable (fun n : ℕ =>
      (y ^ 2 + ((n + 1 : ℕ) : ℝ) ^ 2)⁻¹) := by
    apply Summable.of_nonneg_of_le
    · intro n
      positivity
    · intro n
      have hbase : 0 < (((n + 1 : ℕ) : ℝ) ^ 2) := by positivity
      have hden : 0 < y ^ 2 + ((n + 1 : ℕ) : ℝ) ^ 2 := by positivity
      exact (inv_le_inv₀ hden hbase).2 (by nlinarith [sq_nonneg y])
    · exact hmajor
  apply (summable_nat_add_iff 1).mp
  exact htail

/-- The half-lattice version of the Cauchy sum. -/
theorem tsum_nat_inv_sq_add_sq
    {y : ℝ} (hy : 0 < y) :
    (∑' n : ℕ, (y ^ 2 + (n : ℝ) ^ 2)⁻¹) =
      (1 / 2) *
        ((Real.pi / y) *
          ((1 + Real.exp (-(2 * Real.pi * y))) /
            (1 - Real.exp (-(2 * Real.pi * y)))) + y⁻¹ ^ 2) := by
  let fNat : ℕ → ℝ := fun n => (y ^ 2 + (n : ℝ) ^ 2)⁻¹
  let fInt : ℤ → ℝ := fun n => (y ^ 2 + (n : ℝ) ^ 2)⁻¹
  have hNat : Summable fNat := summable_nat_inv_sq_add_sq y
  have hpos : Summable (fun n : ℕ => fInt (n + 1)) := by
    have := (summable_nat_add_iff 1).mpr hNat
    simpa only [fNat, fInt, Int.cast_add, Int.cast_natCast, Int.cast_one,
      Nat.cast_add, Nat.cast_one] using this
  have hneg : Summable (fun n : ℕ => fInt (-(n + 1))) := by
    simpa only [fInt, Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one,
      neg_sq] using hpos
  have hIntSplit := tsum_of_add_one_of_neg_add_one hpos hneg
  have hNatSplit := hNat.tsum_eq_zero_add
  have hLattice := tsum_int_inv_sq_add_sq hy
  -- states the goal with the definition unfolded, in the shape the next step needs;
  -- there is no `_apply` lemma to rewrite with here.
  change ∑' n : ℕ, fNat n = _
  simp only [fInt, Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one,
    Int.cast_zero, neg_sq] at hIntSplit
  simp only [fNat, Nat.cast_zero, Nat.cast_add, Nat.cast_one] at hNatSplit
  have hzero : (y ^ 2 + (0 : ℝ) ^ 2)⁻¹ = y⁻¹ ^ 2 := by simp [inv_pow]
  rw [hzero] at hIntSplit hNatSplit
  nlinarith

end

end CauchyLattice
end TauCeti
