/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import TauCeti.Analysis.InnerProductSpace.Projection.PrincipalAngle
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Frobenius

/-!
# Frobenius sine distance between subspaces

For subspaces `U` and `V` of a finite-dimensional inner product space, the Frobenius sine
`sinThetaFrobenius U V` is the Frobenius seminorm of the directed sine map
`P_{Vᗮ} P_U`. This packages the quantity used in the Frobenius form of subspace
perturbation inequalities without selecting bases.

Its value is the square root of the sum of the squares of the principal sines.
Unlike the operator-norm gap, the Frobenius quantity measures all principal sines.

## Source

* AIQ-Kitware DKPS formalization (Kitware, Inc.; Apache-2.0):
  https://github.com/AIQ-Kitware/aiq-dkps-formalization
* Source file: `ForTauCeti/Analysis/InnerProductSpace/SinTheta/Frobenius.lean`.
-/

public section

namespace TauCeti

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- The Frobenius seminorm of the directed sine map between two subspaces. -/
@[expose]
noncomputable def sinThetaFrobenius (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : ℝ :=
  UnitarilyInvariantSeminorm.frobenius 𝕜 E E
    (U.sinThetaMap V : E →ₗ[𝕜] E)

/-- The Frobenius sine is the Frobenius seminorm of the cross-projection. -/
theorem sinThetaFrobenius_eq (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    sinThetaFrobenius U V =
      UnitarilyInvariantSeminorm.frobenius 𝕜 E E
        (U.sinThetaMap V : E →ₗ[𝕜] E) :=
  rfl

/-- The Frobenius sine is nonnegative. -/
theorem sinThetaFrobenius_nonneg (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    0 ≤ sinThetaFrobenius U V := by
  rw [sinThetaFrobenius_eq,
    UnitarilyInvariantSeminorm.frobenius_apply_eq_sqrt_sum_sq_singularValues]
  exact Real.sqrt_nonneg _

/-- The Frobenius sine is the Euclidean norm of the principal-sine list. -/
theorem sinThetaFrobenius_eq_sqrt_sum_sq_principalSines (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    sinThetaFrobenius U V = √((U.principalSines V).sum fun _ s => s ^ 2) := by
  rw [sinThetaFrobenius_eq,
    UnitarilyInvariantSeminorm.frobenius_apply_eq_sqrt_sum_sq_singularValues,
    ← Submodule.principalSines_def]

end TauCeti
