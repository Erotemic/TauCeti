/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5, Claude Opus 4.8, Claude Opus 5
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Operator-norm bounds for Gram quadratic forms

The distance of `M.adjoint * M` from the identity in operator norm controls the relative
quadratic-form error of `M`. This estimate is independent of near-isometry factorization.

Adapted from the Apache-2.0 DKPS formalization (Kitware, Inc.).
-/

public section

open scoped RealInnerProductSpace InnerProductSpace

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

/-- An operator-norm bound on the Gram operator's deviation from the identity implies
the corresponding pointwise quadratic-form bound. -/
theorem abs_inner_sub_le_of_norm_adjoint_mul_self_sub_one_le (M : E →L[ℝ] E) {δ : ℝ}
    (hM : ‖ContinuousLinearMap.adjoint M * M - 1‖ ≤ δ) (x : E) :
    |⟪(M : E →ₗ[ℝ] E) x, (M : E →ₗ[ℝ] E) x⟫_ℝ - ⟪x, x⟫_ℝ| ≤
      δ * ⟪x, x⟫_ℝ := by
  have hid : ⟪(ContinuousLinearMap.adjoint M * M - 1) x, x⟫_ℝ
      = ⟪(M : E →ₗ[ℝ] E) x, (M : E →ₗ[ℝ] E) x⟫_ℝ - ⟪x, x⟫_ℝ := by
    rw [sub_apply, mul_apply_eq_comp, one_apply_eq_self, inner_sub_left,
      ContinuousLinearMap.adjoint_inner_left]
    simp
  rw [← hid]
  calc |⟪(ContinuousLinearMap.adjoint M * M - 1) x, x⟫_ℝ|
      ≤ ‖(ContinuousLinearMap.adjoint M * M - 1) x‖ * ‖x‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖ContinuousLinearMap.adjoint M * M - 1‖ * ‖x‖ * ‖x‖ :=
        mul_le_mul_of_nonneg_right
          ((ContinuousLinearMap.adjoint M * M - 1).le_opNorm x) (norm_nonneg x)
    _ ≤ δ * ‖x‖ * ‖x‖ := by gcongr
    _ = δ * ⟪x, x⟫_ℝ := by rw [real_inner_self_eq_norm_mul_norm]; ring

end ContinuousLinearMap

end
