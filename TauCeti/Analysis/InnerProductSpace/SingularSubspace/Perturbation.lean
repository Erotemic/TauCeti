/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import TauCeti.Analysis.InnerProductSpace.SingularSubspace
public import TauCeti.Analysis.InnerProductSpace.Projection.PrincipalAngle
public import TauCeti.Analysis.InnerProductSpace.Gram.Perturbation
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.SinTheta.Basic
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.OpNorm

/-!
# Gram perturbation bounds for singular subspaces

The right and left singular subspaces of a rectangular map are the spectral subspaces
of its source and target Gram operators. An interval/exterior spectral gap for two
corresponding Gram subspaces therefore bounds their directed sine by the change in
the rectangular map:

`delta * norm(sinTheta) <= (norm B + norm A) * norm(B - A)`.

The proof combines the interval/exterior Davis--Kahan theorem with the Gram
perturbation estimate, without repeating either argument. The spectral sets
select squared singular values.

## References

* Y. Yu, T. Wang, R. J. Samworth, *A useful variant of the Davis--Kahan
  theorem for statisticians*, Biometrika **102** (2015), 315--323.
* Adapted from the Kitware DKPS formalization (Apache-2.0),
  `YuWangSamworth2015/Core/SingularSubspace.lean`.
-/

public section

namespace LinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- Under an interval/exterior gap between right Gram spectral blocks, the directed
sine of the selected right singular subspaces is controlled by the rectangular
operator perturbation. -/
theorem mul_norm_sinThetaMap_rightSingularSubspace_le (A B : E →ₗ[𝕜] F)
    {a b δ : ℝ}
    (hgap : Module.End.PointIntervalExteriorGap (A.adjoint ∘ₗ A)
      (A.rightSingularSubspace (Set.Icc a b)) (B.adjoint ∘ₗ B)
      (B.rightSingularSubspace (Set.Icc a b))ᗮ a b δ) :
    δ * ‖(A.rightSingularSubspace (Set.Icc a b)).sinThetaMap
      (B.rightSingularSubspace (Set.Icc a b))‖ ≤
      (‖B.toContinuousLinearMap‖ + ‖A.toContinuousLinearMap‖) *
        ‖B.toContinuousLinearMap - A.toContinuousLinearMap‖ := by
  let : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  let : CompleteSpace F := FiniteDimensional.complete 𝕜 F
  let P : E →L[𝕜] E := A.toContinuousLinearMap.adjoint ∘L A.toContinuousLinearMap
  let Q : E →L[𝕜] E := B.toContinuousLinearMap.adjoint ∘L B.toContinuousLinearMap
  let U : Submodule 𝕜 E := A.rightSingularSubspace (Set.Icc a b)
  let V : Submodule 𝕜 E := B.rightSingularSubspace (Set.Icc a b)
  have hP : (P : E →ₗ[𝕜] E).IsSymmetric := by
    change (A.adjoint ∘ₗ A).IsSymmetric
    exact A.isSymmetric_adjoint_comp_self
  have hQ : (Q : E →ₗ[𝕜] E).IsSymmetric := by
    change (B.adjoint ∘ₗ B).IsSymmetric
    exact B.isSymmetric_adjoint_comp_self
  have hU : ∀ x ∈ U, P x ∈ U := by
    intro x hx
    change (A.adjoint ∘ₗ A) x ∈ A.rightSingularSubspace (Set.Icc a b)
    exact (A.map_rightSingularSubspace_le (Set.Icc a b))
      (Submodule.mem_map_of_mem hx)
  have hV : ∀ x ∈ V, Q x ∈ V := by
    intro x hx
    change (B.adjoint ∘ₗ B) x ∈ B.rightSingularSubspace (Set.Icc a b)
    exact (B.map_rightSingularSubspace_le (Set.Icc a b))
      (Submodule.mem_map_of_mem hx)
  have hgap' : Module.End.PointIntervalExteriorGap (P : E →ₗ[𝕜] E) U
      (Q : E →ₗ[𝕜] E) Vᗮ a b δ := by
    change Module.End.PointIntervalExteriorGap (A.adjoint ∘ₗ A) U
      (B.adjoint ∘ₗ B) Vᗮ a b δ
    exact hgap
  have hdk : δ * ‖Vᗮ.starProjection ∘L U.starProjection‖ ≤ ‖Q - P‖ := by
    have hround (T : E →L[𝕜] E) :
        LinearMap.toContinuousLinearMap (T : E →ₗ[𝕜] E) = T := by
      exact ContinuousLinearMap.coe_injective rfl
    simpa only [TauCeti.UnitarilyInvariantSeminorm.opNorm_apply,
      map_sub, hround] using
      (TauCeti.UnitarilyInvariantSeminorm.mul_map_starProjection_comp_starProjection_le_map_sub
        (TauCeti.UnitarilyInvariantSeminorm.opNorm 𝕜 E E)
        (A := P) (B := Q) (U := U) (V := V) hP hQ hU hV hgap')
  change δ * ‖U.sinThetaMap V‖ ≤
    (‖B.toContinuousLinearMap‖ + ‖A.toContinuousLinearMap‖) *
      ‖B.toContinuousLinearMap - A.toContinuousLinearMap‖
  calc
    δ * ‖U.sinThetaMap V‖ =
        δ * ‖Vᗮ.starProjection ∘L U.starProjection‖ := by rw [Submodule.sinThetaMap_def]
    _ ≤ ‖Q - P‖ := hdk
    _ ≤ (‖B.toContinuousLinearMap‖ + ‖A.toContinuousLinearMap‖) *
          ‖B.toContinuousLinearMap - A.toContinuousLinearMap‖ :=
      ContinuousLinearMap.norm_adjoint_comp_self_sub_adjoint_comp_self_le
        B.toContinuousLinearMap A.toContinuousLinearMap

/-- Under an interval/exterior gap between left Gram spectral blocks, the directed
sine of the selected left singular subspaces is controlled by the rectangular
operator perturbation. -/
theorem mul_norm_sinThetaMap_leftSingularSubspace_le (A B : E →ₗ[𝕜] F)
    {a b δ : ℝ}
    (hgap : Module.End.PointIntervalExteriorGap (A ∘ₗ A.adjoint)
      (A.leftSingularSubspace (Set.Icc a b)) (B ∘ₗ B.adjoint)
      (B.leftSingularSubspace (Set.Icc a b))ᗮ a b δ) :
    δ * ‖(A.leftSingularSubspace (Set.Icc a b)).sinThetaMap
      (B.leftSingularSubspace (Set.Icc a b))‖ ≤
      (‖B.toContinuousLinearMap‖ + ‖A.toContinuousLinearMap‖) *
        ‖B.toContinuousLinearMap - A.toContinuousLinearMap‖ := by
  let : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  let : CompleteSpace F := FiniteDimensional.complete 𝕜 F
  let P : F →L[𝕜] F := A.toContinuousLinearMap ∘L A.toContinuousLinearMap.adjoint
  let Q : F →L[𝕜] F := B.toContinuousLinearMap ∘L B.toContinuousLinearMap.adjoint
  let U : Submodule 𝕜 F := A.leftSingularSubspace (Set.Icc a b)
  let V : Submodule 𝕜 F := B.leftSingularSubspace (Set.Icc a b)
  have hP : (P : F →ₗ[𝕜] F).IsSymmetric := by
    change (A ∘ₗ A.adjoint).IsSymmetric
    exact A.isSymmetric_self_comp_adjoint
  have hQ : (Q : F →ₗ[𝕜] F).IsSymmetric := by
    change (B ∘ₗ B.adjoint).IsSymmetric
    exact B.isSymmetric_self_comp_adjoint
  have hU : ∀ x ∈ U, P x ∈ U := by
    intro x hx
    change (A ∘ₗ A.adjoint) x ∈ A.leftSingularSubspace (Set.Icc a b)
    exact (A.map_leftSingularSubspace_le (Set.Icc a b))
      (Submodule.mem_map_of_mem hx)
  have hV : ∀ x ∈ V, Q x ∈ V := by
    intro x hx
    change (B ∘ₗ B.adjoint) x ∈ B.leftSingularSubspace (Set.Icc a b)
    exact (B.map_leftSingularSubspace_le (Set.Icc a b))
      (Submodule.mem_map_of_mem hx)
  have hgap' : Module.End.PointIntervalExteriorGap (P : F →ₗ[𝕜] F) U
      (Q : F →ₗ[𝕜] F) Vᗮ a b δ := by
    change Module.End.PointIntervalExteriorGap (A ∘ₗ A.adjoint) U
      (B ∘ₗ B.adjoint) Vᗮ a b δ
    exact hgap
  have hdk : δ * ‖Vᗮ.starProjection ∘L U.starProjection‖ ≤ ‖Q - P‖ := by
    have hround (T : F →L[𝕜] F) :
        LinearMap.toContinuousLinearMap (T : F →ₗ[𝕜] F) = T := by
      exact ContinuousLinearMap.coe_injective rfl
    simpa only [TauCeti.UnitarilyInvariantSeminorm.opNorm_apply,
      map_sub, hround] using
      (TauCeti.UnitarilyInvariantSeminorm.mul_map_starProjection_comp_starProjection_le_map_sub
        (TauCeti.UnitarilyInvariantSeminorm.opNorm 𝕜 F F)
        (A := P) (B := Q) (U := U) (V := V) hP hQ hU hV hgap')
  change δ * ‖U.sinThetaMap V‖ ≤
    (‖B.toContinuousLinearMap‖ + ‖A.toContinuousLinearMap‖) *
      ‖B.toContinuousLinearMap - A.toContinuousLinearMap‖
  calc
    δ * ‖U.sinThetaMap V‖ =
        δ * ‖Vᗮ.starProjection ∘L U.starProjection‖ := by rw [Submodule.sinThetaMap_def]
    _ ≤ ‖Q - P‖ := hdk
    _ ≤ (‖B.toContinuousLinearMap‖ + ‖A.toContinuousLinearMap‖) *
          ‖B.toContinuousLinearMap - A.toContinuousLinearMap‖ :=
      ContinuousLinearMap.norm_self_comp_adjoint_sub_self_comp_adjoint_le
        B.toContinuousLinearMap A.toContinuousLinearMap

end LinearMap
