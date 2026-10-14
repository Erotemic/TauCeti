/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5, Claude Opus 4.8, Claude Opus 5
-/
module

public import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Constructing linear isometries from inner-product data

Inner-product preservation on an orthonormal basis determines inner-product preservation on the
whole space, for linear maps between two inner product spaces over `RCLike` scalars. An
inner-product-preserving endomorphism of a finite-dimensional inner product space gives a
linear isometry equivalence.

Adapted from the Apache-2.0 DKPS formalization (Kitware, Inc.).
-/

public section

open scoped InnerProductSpace

namespace OrthonormalBasis

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
variable {ι : Type*} [Fintype ι]

/-- A linear map preserving the inner products of all pairs of orthonormal basis vectors
preserves the inner products of arbitrary vectors. -/
theorem inner_map_eq_of_inner_basis (b : OrthonormalBasis ι 𝕜 E)
    {W : E →ₗ[𝕜] F}
    (hW : ∀ j k : ι, ⟪W (b j), W (b k)⟫_𝕜 = ⟪b j, b k⟫_𝕜)
    (x y : E) :
    ⟪W x, W y⟫_𝕜 = ⟪x, y⟫_𝕜 := by
  classical
  conv_lhs => rw [← b.sum_repr x, ← b.sum_repr y]
  conv_rhs => rw [← b.sum_repr x, ← b.sum_repr y]
  simp only [map_sum, map_smul, sum_inner, inner_sum, inner_smul_left,
    inner_smul_right]
  simp only [hW]

end OrthonormalBasis

namespace LinearMap

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]

/-- An inner-product-preserving finite-dimensional endomorphism extends to a linear
isometry equivalence with the same underlying map. -/
theorem exists_linearIsometryEquiv_of_inner_map {W : E →ₗ[𝕜] E}
    (hW : ∀ x y : E, ⟪W x, W y⟫_𝕜 = ⟪x, y⟫_𝕜) :
    ∃ U : E ≃ₗᵢ[𝕜] E, ∀ x, U x = W x := by
  have hcoe : ⇑(W.isometryOfInner hW) = ⇑W := W.coe_isometryOfInner hW
  have hsurj : Function.Surjective (W.isometryOfInner hW) := by
    rw [hcoe]
    exact LinearMap.injective_iff_surjective.mp (hcoe ▸ (W.isometryOfInner hW).injective)
  refine ⟨LinearIsometryEquiv.ofSurjective _ hsurj, fun x => ?_⟩
  rw [LinearIsometryEquiv.coe_ofSurjective, hcoe]

end LinearMap

end
