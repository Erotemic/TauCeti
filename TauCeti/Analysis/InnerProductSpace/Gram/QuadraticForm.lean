/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5, Claude Opus 4.8, Claude Opus 5
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Error bounds for inner-product quadratic forms

General estimates for quadratic-form perturbations, independent of a particular near-isometry
factorization. The first result extracts nonnegativity of an error bound from a nonzero vector.

Adapted from the Apache-2.0 DKPS formalization (Kitware, Inc.).
-/

public section

namespace LinearMap

open scoped RealInnerProductSpace InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A relative quadratic-form error bound on a nontrivial inner product space has
nonnegative error constant. -/
theorem nonneg_of_quadraticFormBound [Nontrivial E] {M : E →ₗ[ℝ] E} {δ : ℝ}
    (hM : ∀ x : E, |⟪M x, M x⟫_ℝ - ⟪x, x⟫_ℝ| ≤ δ * ⟪x, x⟫_ℝ) : 0 ≤ δ := by
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  have hvpos : 0 < ⟪v, v⟫_ℝ := real_inner_self_pos.mpr hv
  have hmul : 0 ≤ δ * ⟪v, v⟫_ℝ :=
    le_trans (abs_nonneg (⟪M v, M v⟫_ℝ - ⟪v, v⟫_ℝ)) (hM v)
  exact nonneg_of_mul_nonneg_left hmul hvpos

end LinearMap

end
