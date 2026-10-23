/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.Fourier.PoissonSummation

/-!
# Asymptotic decay of the absolute exponential

For `0 < a`, the function `x ↦ exp (-a * |x|)` tends to zero faster than any
real power at both ends of the real line. The complex-valued form is convenient
for Fourier transform and Poisson summation arguments.

## Provenance

Adapted from `ForTauCeti/Analysis/Fourier/ExponentialAbs.lean` in the
AIQ-Kitware DKPS formalization (Apache-2.0; Jon Crall and GPT 5.6 High).
-/

public section

open Filter Asymptotics

namespace TauCeti

/-- A two-sided complex exponential decays faster than every real power at infinity. -/
theorem cexp_neg_mul_abs_isLittleO_rpow_cocompact
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

end TauCeti
