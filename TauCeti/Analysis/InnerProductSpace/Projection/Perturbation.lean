/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import TauCeti.Analysis.InnerProductSpace.Projection.PrincipalAngle
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.OpNorm
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.SinTheta.Basic

/-!
# Operator-norm perturbation of invariant subspaces

For symmetric operators `A` and `B` on a finite-dimensional inner product space,
an interval/exterior gap between the spectrum of `A` on an invariant subspace `U`
and that of `B` on `Vᗮ` bounds the directed sine map by the operator perturbation:

`δ * ‖U.sinThetaMap V‖ ≤ ‖B - A‖`.

For positive `δ`, this controls the component of vectors in `U` orthogonal to `V`.
It applies to arbitrary invariant subspaces, including spectral blocks of Gram
operators used to define singular subspaces.

## References

* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a perturbation. III*,
  SIAM J. Numer. Anal. **7** (1970), 1--46.
-/

public section

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-- An interval/exterior spectral gap bounds the directed sine between invariant
subspaces by the operator perturbation. -/
theorem mul_norm_sinThetaMap_le_norm_sub_of_pointIntervalExteriorGap
    (U V : Submodule 𝕜 E) {A B : E →L[𝕜] E}
    (hA : (A : E →ₗ[𝕜] E).IsSymmetric) (hB : (B : E →ₗ[𝕜] E).IsSymmetric)
    (hU : ∀ x ∈ U, A x ∈ U) (hV : ∀ x ∈ V, B x ∈ V) {a b δ : ℝ}
    (hgap : Module.End.PointIntervalExteriorGap (A : E →ₗ[𝕜] E) U
      (B : E →ₗ[𝕜] E) Vᗮ a b δ) :
    δ * ‖U.sinThetaMap V‖ ≤ ‖B - A‖ := by
  have hround (T : E →L[𝕜] E) :
      LinearMap.toContinuousLinearMap (T : E →ₗ[𝕜] E) = T := by
    simpa only [LinearMap.coe_toContinuousLinearMap_symm] using
      (LinearEquiv.apply_symm_apply
        (LinearMap.toContinuousLinearMap :
          (E →ₗ[𝕜] E) ≃ₗ[𝕜] E →L[𝕜] E) T)
  simpa only [sinThetaMap_def, TauCeti.UnitarilyInvariantSeminorm.opNorm_apply,
    map_sub, hround] using
    (TauCeti.UnitarilyInvariantSeminorm.mul_map_starProjection_comp_starProjection_le_map_sub
      (TauCeti.UnitarilyInvariantSeminorm.opNorm 𝕜 E E) hA hB hU hV hgap)

end Submodule
