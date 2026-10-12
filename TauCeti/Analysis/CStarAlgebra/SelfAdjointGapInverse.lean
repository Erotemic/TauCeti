/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric

/-!
# Spectral-gap inverse of a self-adjoint element

If the real spectrum of a self-adjoint element `a` of a C⋆-algebra avoids
`(-r, r)` for `r > 0`, then `a` is a unit and its canonical ring inverse
has norm at most `r⁻¹`.

The invertibility statement is useful when constructing and manipulating
inverse operators. The norm estimate supplies the spectral-gap bound used
in interval and exterior Sylvester estimates.

## Main results

* `IsSelfAdjoint.isUnit_and_norm_ringInverse_le` returns both invertibility
  and the norm bound for the canonical inverse. Its unit conclusion is proved
  using Mathlib's spectrum criterion rather than a separate wrapper.

## Source

Adapted from the Davis--Kahan/DKPS formalization (Kitware, Inc.),
`ForMathlib/Analysis/CStarAlgebra/SelfAdjointGapInverse.lean` at commit
`fc38eb4`, by Jon Crall and Claude Fable 5 (Apache 2.0).
-/

public section

namespace IsSelfAdjoint

variable {A : Type*} [CStarAlgebra A] {a : A} {r : ℝ}

/-- A positive gap around zero in the real spectrum of a self-adjoint element
makes it a unit and bounds the canonical ring inverse by the reciprocal gap. -/
theorem isUnit_and_norm_ringInverse_le (ha : IsSelfAdjoint a) (hr : 0 < r)
    (hσ : ∀ x ∈ spectrum ℝ a, r ≤ |x|) :
    IsUnit a ∧ ‖Ring.inverse a‖ ≤ r⁻¹ := by
  have hunit : IsUnit a := by
    refine spectrum.isUnit_of_zero_notMem ℝ (fun hzero => ?_)
    have hbound : r ≤ (0 : ℝ) := by
      simpa only [abs_zero] using hσ 0 hzero
    exact (not_le_of_gt hr) hbound
  refine ⟨hunit, ?_⟩
  rw [← cfc_ringInverse_id (R := ℝ) a hunit]
  refine norm_cfc_le (by positivity) fun x hx => ?_
  rw [Real.norm_eq_abs, abs_inv]
  exact inv_anti₀ hr (hσ x hx)

end IsSelfAdjoint
