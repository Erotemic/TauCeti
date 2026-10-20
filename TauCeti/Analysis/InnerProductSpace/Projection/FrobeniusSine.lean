/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import TauCeti.Analysis.InnerProductSpace.Projection.PrincipalAngle
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Frobenius
public import Mathlib.Data.Finsupp.Order

/-!
# Frobenius sine distance between subspaces

For subspaces `U` and `V` of a finite-dimensional inner product space, the Frobenius sine
`U.sinThetaFrobenius V` is the Frobenius seminorm of the directed sine map `P_{Vᗮ} P_U`.
It packages the quantity used in Frobenius subspace perturbation inequalities without
selecting bases.

The Frobenius sine is the square root of the sum of the squared principal sines.
The operator norm of the directed sine map sees only the largest principal sine;
the Frobenius quantity accounts for all of them.

## Source

* AIQ-Kitware DKPS formalization (Kitware, Inc.; Apache-2.0):
  https://github.com/AIQ-Kitware/aiq-dkps-formalization
* Source file: `ForTauCeti/Analysis/InnerProductSpace/SinTheta/Frobenius.lean`.
-/

public section

namespace Submodule

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- The Frobenius seminorm of the directed sine map between two subspaces. -/
noncomputable def sinThetaFrobenius (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : ℝ :=
  TauCeti.UnitarilyInvariantSeminorm.frobenius 𝕜 E E
    (U.sinThetaMap V : E →ₗ[𝕜] E)

/-- The Frobenius sine is the Frobenius seminorm of the directed sine map `P_{Vᗮ} P_U`. -/
theorem sinThetaFrobenius_def (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    U.sinThetaFrobenius V =
      TauCeti.UnitarilyInvariantSeminorm.frobenius 𝕜 E E
        (U.sinThetaMap V : E →ₗ[𝕜] E) :=
  (rfl)

/-- The Frobenius sine is nonnegative. -/
theorem sinThetaFrobenius_nonneg (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    0 ≤ U.sinThetaFrobenius V := by
  rw [sinThetaFrobenius_def,
    TauCeti.UnitarilyInvariantSeminorm.frobenius_apply_eq_sqrt_sum_sq_singularValues]
  exact Real.sqrt_nonneg _

/-- The Frobenius sine is the Euclidean norm of the principal-sine list. -/
theorem sinThetaFrobenius_eq_sqrt_sum_sq_principalSines (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    U.sinThetaFrobenius V = √((U.principalSines V).sum fun _ s => s ^ 2) := by
  rw [sinThetaFrobenius_def,
    TauCeti.UnitarilyInvariantSeminorm.frobenius_apply_eq_sqrt_sum_sq_singularValues,
    ← principalSines_def]

/-- The squared Frobenius sine equals the sum of the squared principal sines. -/
theorem sq_sinThetaFrobenius (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    (U.sinThetaFrobenius V) ^ 2 = (U.principalSines V).sum fun _ s => s ^ 2 := by
  have hs : 0 ≤ (U.principalSines V).sum (fun _ s => s ^ 2) := by
    exact Finsupp.sum_nonneg (fun _ _ => sq_nonneg _)
  rw [sinThetaFrobenius_eq_sqrt_sum_sq_principalSines, Real.sq_sqrt hs]

/-- The directed projection gap is bounded by the Frobenius sine. -/
theorem directedProjectionGap_le_sinThetaFrobenius (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    U.directedProjectionGap V ≤ U.sinThetaFrobenius V := by
  have hsq : (U.principalSines V 0) ^ 2 ≤
      (U.principalSines V).sum (fun _ s => s ^ 2) := by
    exact Finsupp.single_eval_le_sum (U.principalSines V)
      (g := fun s : ℝ => s ^ 2) (by simp) (fun s => sq_nonneg s) 0
  calc
    U.directedProjectionGap V = U.principalSines V 0 := (U.principalSines_zero V).symm
    _ = √((U.principalSines V 0) ^ 2) :=
      (Real.sqrt_sq (U.principalSines_nonneg V 0)).symm
    _ ≤ √((U.principalSines V).sum (fun _ s => s ^ 2)) := Real.sqrt_le_sqrt hsq
    _ = U.sinThetaFrobenius V :=
      (U.sinThetaFrobenius_eq_sqrt_sum_sq_principalSines V).symm

/-- The Frobenius sine vanishes precisely when the first subspace is contained in the second. -/
@[simp]
theorem sinThetaFrobenius_eq_zero_iff (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    U.sinThetaFrobenius V = 0 ↔ U ≤ V := by
  constructor
  · intro h
    have hgap : U.directedProjectionGap V = 0 := by
      apply le_antisymm
      · simpa only [h] using (U.directedProjectionGap_le_sinThetaFrobenius V)
      · rw [← U.norm_sinThetaMap V]
        exact norm_nonneg _
    exact (U.directedProjectionGap_eq_zero_iff V).mp hgap
  · intro h
    rw [sinThetaFrobenius_eq_sqrt_sum_sq_principalSines,
      (U.principalSines_eq_zero_iff V).mpr h]
    simp

/-- The Frobenius sine from a subspace to itself is zero. -/
@[simp]
theorem sinThetaFrobenius_self (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] : U.sinThetaFrobenius U = 0 :=
  (U.sinThetaFrobenius_eq_zero_iff U).mpr le_rfl

end Submodule
