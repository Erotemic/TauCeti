/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Projection.Acute
public import TauCeti.Analysis.SpecialFunctions.Trigonometric.TanArcsin

/-!
# A directed tangent representative for subspaces

For subspaces `Z` and `U` of a finite-dimensional real or complex inner product space, the
directed sine embedding is `S = P_{Uᗮ} ∘ inclusion_Z : Z → E`. In its right singular basis,
`Submodule.directedTanThetaMap` multiplies the `i`-th vector by
`tan (arcsin (S.singularValues i))` and then includes the result into the ambient space.

When the directed gap from `Z` to `U` is less than `1`, all these sine singular values are below
the right-angle pole. Nonnegativity and monotonicity of `tan ∘ arcsin` then show that the
singular values of this representative are exactly `Z.principalTangents U`, including the
zero tail. No equality between the dimensions of `Z` and `U` is required.

This realizes the representative-construction and singular-value-identification step of the
equal- and lower-rank Ritz-residual `tan Θ` theorems (SSP-C28 and SSP-C29).

## Main results

* `Submodule.directedTanThetaMap_apply_rightSingularBasis`: the defining diagonal action on
  the right singular vectors of the sine embedding.
* `Submodule.singularValues_directedTanThetaMap`: below the right-angle pole, the rectangular
  representative has the directed principal tangents as its singular values.

## References

* C. Davis, W. M. Kahan, *The rotation of eigenvectors by a perturbation. III*,
  SIAM J. Numer. Anal. **7** (1970), 1–46.
* [Tau Ceti roadmap](https://github.com/TauCetiProject/TauCetiRoadmap),
  `TauCetiRoadmap/OperatorTheory/SpectralSubspacePerturbation/README.md`,
  SSP-C28 and SSP-C29.
-/

public section

noncomputable section

namespace Submodule

open Module

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  (Z U : Submodule 𝕜 E) [Z.HasOrthogonalProjection] [U.HasOrthogonalProjection]

/-- The directed tangent representative in a right singular basis of the sine embedding
from `Z` to `Uᗮ`, followed by the inclusion of `Z` into the ambient space. -/
def directedTanThetaMap : Z →ₗ[𝕜] E :=
  let S : Z →ₗ[𝕜] E :=
    (Uᗮ.starProjection ∘L Z.subtypeL : Z →L[𝕜] E)
  let e := S.rightSingularBasis
  Z.subtypeₗᵢ.toLinearMap ∘ₗ
    Matrix.toLin e.toBasis e.toBasis
      (Matrix.diagonal fun i ↦
        (Real.tan (Real.arcsin (S.singularValues i)) : 𝕜))

omit [Z.HasOrthogonalProjection] in
/-- The directed tangent representative multiplies each right sine singular vector by
the sine-to-tangent transform of its singular value. -/
theorem directedTanThetaMap_apply_rightSingularBasis (i : Fin (finrank 𝕜 Z)) :
    let S : Z →ₗ[𝕜] E :=
      (Uᗮ.starProjection ∘L Z.subtypeL : Z →L[𝕜] E)
    Z.directedTanThetaMap U (S.rightSingularBasis i) =
      (Real.tan (Real.arcsin (S.singularValues i)) : 𝕜) •
        (S.rightSingularBasis i : E) := by
  simp only [directedTanThetaMap, LinearMap.comp_apply,
    Matrix.toLin_diagonal_apply_self, subtypeₗᵢ_toLinearMap, map_smul]
  simp only [Submodule.subtype_apply]

/-- Below the right-angle pole, the directed tangent representative has the directed principal
tangents as its singular values, including the zero tail. No rank equality is required. -/
theorem singularValues_directedTanThetaMap (hgap : Z.directedProjectionGap U < 1) :
    (Z.directedTanThetaMap U).singularValues = Z.principalTangents U := by
  let S : Z →ₗ[𝕜] E :=
    (Uᗮ.starProjection ∘L Z.subtypeL : Z →L[𝕜] E)
  let e := S.rightSingularBasis
  let d : Fin (finrank 𝕜 Z) → 𝕜 :=
    fun i ↦ (Real.tan (Real.arcsin (S.singularValues i)) : 𝕜)
  let D : Z →ₗ[𝕜] Z :=
    Matrix.toLin e.toBasis e.toBasis (Matrix.diagonal d)
  have hS : S.singularValues = Z.principalSines U := by
    simpa only [S, toLinearMap_subtypeL, range_subtype] using
      (U.principalSines_range_eq_singularValues
        (X := Z.subtypeL) Z.subtypeₗᵢ.isometry).symm
  have hlt (i : ℕ) : S.singularValues i < 1 := by
    rw [hS]
    exact (Z.forall_principalSines_lt_iff U).2 hgap i
  have hnorm (i : Fin (finrank 𝕜 Z)) :
      ‖d i‖ = Real.tan (Real.arcsin (S.singularValues i)) :=
    RCLike.norm_of_nonneg (Real.tan_arcsin_nonneg (S.singularValues_nonneg i))
  have hanti : Antitone fun i ↦ ‖d i‖ := by
    intro i j hij
    simp only [hnorm]
    exact Real.tan_arcsin_le_tan_arcsin
      (lt_of_lt_of_le neg_one_lt_zero (S.singularValues_nonneg j))
      (S.singularValues_antitone hij) (hlt i)
  have hD : D.singularValues = Z.principalTangents U := by
    ext i
    rcases lt_or_ge i (finrank 𝕜 Z) with hi | hi
    · calc
        D.singularValues i = ‖d ⟨i, hi⟩‖ :=
          Matrix.singularValues_toLin_diagonal e d (Equiv.refl _) hanti ⟨i, hi⟩
        _ = Real.tan (Real.arcsin (S.singularValues i)) := hnorm _
        _ = Z.principalTangents U i := by
          rw [hS, principalTangents_apply, principalAngles_apply]
    · rw [D.singularValues_of_finrank_le hi, principalTangents_of_finrank_le Z U hi]
  -- The representative is `D` followed by the isometric inclusion of `Z`.
  exact (LinearMap.singularValues_linearIsometry_comp Z.subtypeₗᵢ D).trans hD

end Submodule
