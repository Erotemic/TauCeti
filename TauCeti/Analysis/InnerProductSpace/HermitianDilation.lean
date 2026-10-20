/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import TauCeti.Analysis.InnerProductSpace.Adjoint

/-!
# Hermitian dilation of a rectangular linear map

A linear map `A : E →ₗ[𝕜] F` between finite-dimensional inner product spaces determines
an endomorphism of the Hilbert direct sum `WithLp 2 (E × F)` with block matrix
`[[0, A†], [A, 0]]`. This construction is symmetric even when `E` and `F` differ.

Hermitian dilation allows spectral arguments for symmetric endomorphisms to be applied
to rectangular operators and their singular subspaces.

## Source

Adapted from the Kitware DKPS formalization,
`YuWangSamworth2015/YuWangSamworth2015/Core/SingularSubspace.lean`.
-/

public section

open scoped InnerProductSpace

namespace LinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- The underlying product-coordinate map `(x, y) ↦ (A† y, A x)`. -/
noncomputable def hermitianDilationProd (A : E →ₗ[𝕜] F) :
    (E × F) →ₗ[𝕜] (E × F) where
  toFun x := (A.adjoint x.2, A x.1)
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp

/-- The Hermitian dilation on the Hilbert `L²` product of the domain and codomain. -/
noncomputable def hermitianDilation (A : E →ₗ[𝕜] F) :
    WithLp 2 (E × F) →ₗ[𝕜] WithLp 2 (E × F) :=
  (WithLp.linearEquiv 2 𝕜 (E × F)).symm.toLinearMap ∘ₗ
    A.hermitianDilationProd ∘ₗ
      (WithLp.linearEquiv 2 𝕜 (E × F)).toLinearMap

/-- The dilation interchanges the two summands, applying `A` and its adjoint. -/
@[simp]
theorem hermitianDilation_apply (A : E →ₗ[𝕜] F) (x : WithLp 2 (E × F)) :
    A.hermitianDilation x =
      WithLp.toLp 2 (A.adjoint (WithLp.ofLp x).2, A (WithLp.ofLp x).1) := by
  (rfl)

/-- The Hermitian dilation of any finite-dimensional rectangular linear map is symmetric. -/
theorem isSymmetric_hermitianDilation (A : E →ₗ[𝕜] F) :
    A.hermitianDilation.IsSymmetric := fun x y => by
  simp only [hermitianDilation_apply, WithLp.prod_inner_apply]
  rw [LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_right, add_comm]

end LinearMap
