/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5, Claude Opus 4.8, Claude Opus 5
-/
module

public import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# A Gram-eigenvalue bound from squared-norm control

A relative bound on the squared-norm defect of a finite-dimensional linear map controls every
real eigenvalue of its Gram operator. The eigenvector need not be normalized, and the source and
target may differ. This supplies the spectral step of the near-isometry square-root estimate
independently of a particular square-root construction.

Generalized from the Apache-2.0 DKPS formalization (Kitware, Inc.).
-/

public section

open scoped InnerProductSpace

namespace LinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- An eigenvalue of the source Gram operator `M† M` on a nonzero vector is within `δ` of
one when `M` distorts squared norms by at most `δ` relative to their original size.
This is the eigenvalue step in the near-isometry square-root estimate. -/
theorem abs_eigenvalue_sub_one_le (M : E →ₗ[𝕜] F) {δ : ℝ}
    (hM : ∀ x, |‖M x‖ ^ 2 - ‖x‖ ^ 2| ≤ δ * ‖x‖ ^ 2)
    {μ : ℝ} {v : E} (hv : (M.adjoint ∘ₗ M) v = (μ : 𝕜) • v) (hv0 : v ≠ 0) :
    |μ - 1| ≤ δ := by
  have hnorm : ‖M v‖ ^ 2 = μ * ‖v‖ ^ 2 := by
    have h := congrArg (fun y ↦ RCLike.re ⟪y, v⟫_𝕜) hv
    simpa [adjoint_inner_left, inner_smul_left, ← norm_sq_eq_re_inner] using h
  have hvpos : 0 < ‖v‖ ^ 2 := by
    have := hv0
    positivity
  have h := hM v
  rw [hnorm, ← sub_one_mul, abs_mul, abs_of_pos hvpos] at h
  exact le_of_mul_le_mul_right h hvpos

end LinearMap

end
