/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
/-
Ported from AIQ-Kitware/aiq-dkps-formalization, ForTauCeti/Analysis/Calculus/
FourthOrderGreensIdentity.lean (Apache-2.0).
Source: https://github.com/AIQ-Kitware/aiq-dkps-formalization
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Green's identity for the fourth derivative with free-end boundary conditions

For sufficiently regular real functions on `[0,1]`, the free-end conditions
`u''(0) = u''(1) = u'''(0) = u'''(1) = 0` (and the corresponding conditions for
`v`) imply the symmetry identity

`∫₀¹ v(x) u''''(x) dx = ∫₀¹ u(x) v''''(x) dx`.

These boundary conditions are sufficient, not necessary: clamped or periodic
conditions can also make the fourth-derivative operator symmetric. The
associated quadratic form is `∫₀¹ u u'''' = ∫₀¹ (u'')²`.

The hypotheses require continuity and differentiability only on the unit
interval, plus interval integrability of the highest derivatives.
The identities are classical analytic inputs for the free-beam example in
Davis--Kahan (1970), Section 9.
-/

public section

namespace TauCeti

open intervalIntegral MeasureTheory

/-- Integration by parts on `[0,1]`, assuming continuity on the closed interval,
interior derivatives, and interval integrability of the derivatives. -/
theorem integral_mul_deriv_eq_deriv_mul_unitInterval
    {f f' g g' : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc 0 1)) (hg : ContinuousOn g (Set.Icc 0 1))
    (hff' : ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt f (f' x) x)
    (hgg' : ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt g (g' x) x)
    (hf' : IntervalIntegrable f' volume 0 1)
    (hg' : IntervalIntegrable g' volume 0 1) :
    ∫ x in (0 : ℝ)..1, f x * g' x =
      f 1 * g 1 - f 0 * g 0 - ∫ x in (0 : ℝ)..1, f' x * g x := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have hmin : min (0 : ℝ) 1 = 0 := min_eq_left h01
  have hmax : max (0 : ℝ) 1 = 1 := max_eq_right h01
  apply intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
  · simpa only [Set.uIcc_of_le h01] using hf
  · simpa only [Set.uIcc_of_le h01] using hg
  · simpa only [hmin, hmax] using hff'
  · simpa only [hmin, hmax] using hgg'
  · exact hf'
  · exact hg'

/-- Green's identity for fourth derivatives with free-end boundary conditions
on `[0,1]`: the fourth derivative is symmetric on this class of functions. -/
theorem integral_fourthDeriv_mul_eq_mul_fourthDeriv
    {u u1 u2 u3 u4 v v1 v2 v3 v4 : ℝ → ℝ}
    (hu : ContinuousOn u (Set.Icc 0 1)) (hu1 : ContinuousOn u1 (Set.Icc 0 1))
    (hu2 : ContinuousOn u2 (Set.Icc 0 1)) (hu3 : ContinuousOn u3 (Set.Icc 0 1))
    (hu4 : IntervalIntegrable u4 volume 0 1)
    (hv : ContinuousOn v (Set.Icc 0 1)) (hv1 : ContinuousOn v1 (Set.Icc 0 1))
    (hv2 : ContinuousOn v2 (Set.Icc 0 1)) (hv3 : ContinuousOn v3 (Set.Icc 0 1))
    (hv4 : IntervalIntegrable v4 volume 0 1)
    (hdu : ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt u (u1 x) x)
    (hdu1 : ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt u1 (u2 x) x)
    (hdu2 : ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt u2 (u3 x) x)
    (hdu3 : ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt u3 (u4 x) x)
    (hdv : ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt v (v1 x) x)
    (hdv1 : ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt v1 (v2 x) x)
    (hdv2 : ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt v2 (v3 x) x)
    (hdv3 : ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt v3 (v4 x) x)
    (hu2zero : u2 0 = 0) (hu2one : u2 1 = 0)
    (hu3zero : u3 0 = 0) (hu3one : u3 1 = 0)
    (hv2zero : v2 0 = 0) (hv2one : v2 1 = 0)
    (hv3zero : v3 0 = 0) (hv3one : v3 1 = 0) :
    ∫ x in (0 : ℝ)..1, v x * u4 x = ∫ x in (0 : ℝ)..1, u x * v4 x := by
  have hint : ∀ {f : ℝ → ℝ}, ContinuousOn f (Set.Icc (0 : ℝ) 1) →
      IntervalIntegrable f volume 0 1 := by
    intro f hf
    apply ContinuousOn.intervalIntegrable
    simpa only [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hf
  -- Step 1: move `u4` back to `u3`; the boundary term dies on `u3`.
  have step1 : ∫ x in (0 : ℝ)..1, v x * u4 x = -∫ x in (0 : ℝ)..1, v1 x * u3 x := by
    have h := integral_mul_deriv_eq_deriv_mul_unitInterval hv hu3 hdv hdu3 (hint hv1) hu4
    rw [h, hu3zero, hu3one]
    ring
  -- Step 2: again; the boundary term dies on `u2`.
  have step2 : ∫ x in (0 : ℝ)..1, v1 x * u3 x = -∫ x in (0 : ℝ)..1, v2 x * u2 x := by
    have h := integral_mul_deriv_eq_deriv_mul_unitInterval hv1 hu2 hdv1 hdu2 (hint hv2) (hint hu3)
    rw [h, hu2zero, hu2one]
    ring
  -- Step 3: now push derivatives onto `v`; the boundary term dies on `v2`.
  have step3 : ∫ x in (0 : ℝ)..1, u1 x * v3 x = -∫ x in (0 : ℝ)..1, u2 x * v2 x := by
    have h := integral_mul_deriv_eq_deriv_mul_unitInterval hu1 hv2 hdu1 hdv2 (hint hu2) (hint hv3)
    rw [h, hv2zero, hv2one]
    ring
  -- Step 4: last one; the boundary term dies on `v3`.
  have step4 : ∫ x in (0 : ℝ)..1, u x * v4 x = -∫ x in (0 : ℝ)..1, u1 x * v3 x := by
    have h := integral_mul_deriv_eq_deriv_mul_unitInterval hu hv3 hdu hdv3 (hint hu1) hv4
    rw [h, hv3zero, hv3one]
    ring
  -- The two middle integrals agree after commuting the product.
  have hmid : ∫ x in (0 : ℝ)..1, v2 x * u2 x = ∫ x in (0 : ℝ)..1, u2 x * v2 x := by
    simp_rw [mul_comm]
  rw [step1, step2, step4, step3, hmid]

/-- The free-beam quadratic form on `[0,1]` equals the integral of the
square of the second derivative, under free-end boundary conditions. -/
theorem integral_mul_fourthDeriv_self_eq_integral_secondDeriv_sq
    {u u1 u2 u3 u4 : ℝ → ℝ}
    (hu : ContinuousOn u (Set.Icc 0 1)) (hu1 : ContinuousOn u1 (Set.Icc 0 1))
    (hu2 : ContinuousOn u2 (Set.Icc 0 1)) (hu3 : ContinuousOn u3 (Set.Icc 0 1))
    (hu4 : IntervalIntegrable u4 volume 0 1)
    (hdu : ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt u (u1 x) x)
    (hdu1 : ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt u1 (u2 x) x)
    (hdu2 : ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt u2 (u3 x) x)
    (hdu3 : ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt u3 (u4 x) x)
    (hu2zero : u2 0 = 0) (hu2one : u2 1 = 0)
    (hu3zero : u3 0 = 0) (hu3one : u3 1 = 0) :
    ∫ x in (0 : ℝ)..1, u x * u4 x = ∫ x in (0 : ℝ)..1, u2 x ^ 2 := by
  have hint : ∀ {f : ℝ → ℝ}, ContinuousOn f (Set.Icc (0 : ℝ) 1) →
      IntervalIntegrable f volume 0 1 := by
    intro f hf
    apply ContinuousOn.intervalIntegrable
    simpa only [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hf
  have stepA : ∫ x in (0 : ℝ)..1, u x * u4 x = -∫ x in (0 : ℝ)..1, u1 x * u3 x := by
    have h := integral_mul_deriv_eq_deriv_mul_unitInterval hu hu3 hdu hdu3 (hint hu1) hu4
    rw [h, hu3zero, hu3one]
    ring
  have stepB : ∫ x in (0 : ℝ)..1, u1 x * u3 x = -∫ x in (0 : ℝ)..1, u2 x * u2 x := by
    have h := integral_mul_deriv_eq_deriv_mul_unitInterval hu1 hu2 hdu1 hdu2 (hint hu2) (hint hu3)
    rw [h, hu2zero, hu2one]
    ring
  have hsq : ∫ x in (0 : ℝ)..1, u2 x * u2 x = ∫ x in (0 : ℝ)..1, u2 x ^ 2 := by
    congr 1 with x
    ring
  rw [stepA, stepB, hsq]
  ring

end TauCeti
