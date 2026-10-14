/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5, Claude Opus 4.8, Claude Opus 5
-/
module

public import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Eigenvalue control for real Gram operators

A quadratic-form bound on a linear map controls the eigenvalue of its Gram
operator at every unit eigenvector.

Adapted from the Apache-2.0 DKPS formalization (Kitware, Inc.).
-/

public section

open scoped RealInnerProductSpace InnerProductSpace

namespace LinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

/-- The eigenvalue of `M.adjoint * M` at a unit eigenvector differs from one
by at most the error in the quadratic-form bound for `M`. -/
theorem abs_eigenvalue_sub_one_le {M : E →ₗ[ℝ] E} {δ : ℝ}
    (hM : ∀ x : E, |⟪M x, M x⟫_ℝ - ⟪x, x⟫_ℝ| ≤ δ * ⟪x, x⟫_ℝ)
    {v : E} (hv : ⟪v, v⟫_ℝ = 1) {lam : ℝ}
    (hGv : (M.adjoint * M) v = lam • v) : |lam - 1| ≤ δ := by
  have hquad : ⟪(M.adjoint * M) v, v⟫_ℝ = ⟪M v, M v⟫_ℝ := by
    rw [Module.End.mul_apply, LinearMap.adjoint_inner_left]
  have hlam : ⟪(M.adjoint * M) v, v⟫_ℝ = lam := by
    rw [hGv, real_inner_smul_left, hv, mul_one]
  have hb := hM v
  rwa [← hquad, hlam, hv, mul_one] at hb

end LinearMap

end
