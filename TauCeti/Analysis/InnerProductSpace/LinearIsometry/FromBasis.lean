/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5, Claude Opus 4.8, Claude Opus 5
-/
module

public import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Constructing linear isometries from inner-product data

An orthonormal-basis inner-product certificate extends to the whole Hilbert
space. In finite dimension a linear endomorphism preserving inner products
extends to a linear isometry equivalence.

Adapted from the Apache-2.0 DKPS formalization (Kitware, Inc.).
-/

public section

namespace TauCeti

open scoped RealInnerProductSpace InnerProductSpace
open Module (finrank)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section OrthonormalBasis

variable {d : ℕ}

/-- Inner-product preservation on an orthonormal basis implies preservation on all vectors. -/
theorem inner_map_eq_of_inner_basis (b : OrthonormalBasis (Fin d) ℝ E)
    {W : E →ₗ[ℝ] E}
    (hW : ∀ j k : Fin d, ⟪W (b j), W (b k)⟫_ℝ = ⟪b j, b k⟫_ℝ)
    (x y : E) :
    ⟪W x, W y⟫_ℝ = ⟪x, y⟫_ℝ := by
  conv_lhs => rw [← b.sum_repr x, ← b.sum_repr y]
  conv_rhs => rw [← b.sum_repr x, ← b.sum_repr y]
  simp only [map_sum, map_smul, sum_inner, inner_sum, real_inner_smul_left,
    real_inner_smul_right]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [hW k j]

end OrthonormalBasis

end TauCeti

open scoped RealInnerProductSpace InnerProductSpace

namespace LinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

/-- An inner-product-preserving finite-dimensional endomorphism determines a linear
isometry equivalence with the same pointwise action. -/
theorem exists_linearIsometryEquiv_of_inner_map {W : E →ₗ[ℝ] E}
    (hW : ∀ x y : E, ⟪W x, W y⟫_ℝ = ⟪x, y⟫_ℝ) :
    ∃ U : E ≃ₗᵢ[ℝ] E, ∀ x, U x = W x := by
  have hcoe : ⇑(W.isometryOfInner hW) = ⇑W := W.coe_isometryOfInner hW
  have hsurj : Function.Surjective (W.isometryOfInner hW) := by
    rw [hcoe]
    exact LinearMap.injective_iff_surjective.mp (hcoe ▸ (W.isometryOfInner hW).injective)
  refine ⟨LinearIsometryEquiv.ofSurjective _ hsurj, fun x => ?_⟩
  rw [LinearIsometryEquiv.coe_ofSurjective, hcoe]


end LinearMap
end
