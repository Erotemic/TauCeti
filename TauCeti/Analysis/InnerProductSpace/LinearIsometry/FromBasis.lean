/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5, Claude Opus 4.8, Claude Opus 5
-/
module

public import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Isometries from finite orthonormal-basis data

A linear map that preserves inner products on a finite orthonormal basis preserves inner products
on the entire source space, including when the source and target are different inner product
spaces over either `ℝ` or `ℂ`. A finite-dimensional inner-product-preserving endomorphism is a
linear isometry equivalence.

Adapted from the Apache-2.0 DKPS formalization (Kitware, Inc.).
-/

public section

open scoped InnerProductSpace

namespace OrthonormalBasis

variable {𝕜 E F ι : Type*} [RCLike 𝕜] [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- If a linear map preserves the inner products between the vectors of a finite orthonormal
basis, it preserves the inner products of arbitrary vectors. The codomain may differ from the
domain; in particular, no surjectivity or equality of dimensions is required. -/
theorem inner_map_eq_of_inner_basis (b : OrthonormalBasis ι 𝕜 E)
    {W : E →ₗ[𝕜] F}
    (hW : ∀ j k : ι, ⟪W (b j), W (b k)⟫_𝕜 = ⟪b j, b k⟫_𝕜)
    (x y : E) :
    ⟪W x, W y⟫_𝕜 = ⟪x, y⟫_𝕜 := by
  classical
  conv_lhs => rw [← b.sum_repr x, ← b.sum_repr y]
  conv_rhs => rw [← b.sum_repr x, ← b.sum_repr y]
  simp only [map_sum, map_smul, sum_inner, inner_sum, inner_smul_left, inner_smul_right]
  simp_rw [hW]

end OrthonormalBasis

namespace LinearMap

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-- An inner-product-preserving finite-dimensional endomorphism gives a linear isometry
equivalence with the same pointwise action, over `ℝ` or `ℂ`. -/
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
