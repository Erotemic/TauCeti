/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 4.8
-/
module

public import TauCeti.Analysis.InnerProductSpace.RectangularPartialIsometry

/-!
# Square partial isometries

On finite-dimensional endomorphisms, the star-monoid predicate
`TauCeti.IsPartialIsometry` agrees with the rectangular `LinearMap` predicate.
Its initial projection is the orthogonal projection onto `(ker u)ᗮ`.
The norm-preservation characterization is a specialization of the rectangular
version, so that its geometric proof is maintained only once.

Adapted from the Apache-2.0 DKPS formalization (Kitware, Inc.), following
Conway, *A Course in Functional Analysis*, §VI.3, and Reed–Simon I, §VI.
-/

public section

open scoped InnerProductSpace
open LinearMap

namespace TauCeti

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-- The initial projection of a partial isometry is the orthogonal projection onto `(ker u)ᗮ`:
`star u * u = P_{(ker u)ᗮ}`. Conway VI.3.2. -/
theorem IsPartialIsometry.star_mul_self_eq_starProjection {u : E →ₗ[𝕜] E}
    (hu : IsPartialIsometry u) :
    star u * u = ((ker u)ᗮ).starProjection.toLinearMap := by
  have hu' : u * star u * u = u := hu
  ext x
  have huxx : u ((star u * u) x) = u x := by
    have hx : (u * star u * u) x = u x := congrArg (fun f : E →ₗ[𝕜] E => f x) hu'
    rwa [mul_assoc, Module.End.mul_apply] at hx
  have hv : (star u * u) x ∈ (ker u)ᗮ := by
    rw [LinearMap.orthogonal_ker, star_eq_adjoint, Module.End.mul_apply]
    exact LinearMap.mem_range_self _ _
  have hz : x - (star u * u) x ∈ ((ker u)ᗮ)ᗮ := by
    rw [Submodule.orthogonal_orthogonal, LinearMap.mem_ker, map_sub, huxx, sub_self]
  have hres := Submodule.eq_starProjection_of_mem_orthogonal' (u := x) hv hz (by abel)
  simpa using hres.symm

/-- A square partial isometry preserves norms precisely on `(ker u)ᗮ`.
This is the endomorphism specialization of the rectangular characterization. -/
theorem isPartialIsometry_iff_norm_map {u : E →ₗ[𝕜] E} :
    IsPartialIsometry u ↔ ∀ x ∈ (ker u)ᗮ, ‖u x‖ = ‖x‖ := by
  exact (LinearMap.isPartialIsometry_iff_starMul (u := u)).symm.trans
    (LinearMap.isPartialIsometry_iff_norm_map (u := u))

/-- **Constructor** used by the polar decomposition: a linear map that is isometric on a submodule
`K` and vanishes on `Kᗮ` is a partial isometry with initial space `K`. Conway VI.3.9. -/
theorem isPartialIsometry_of_isometryOn {u : E →ₗ[𝕜] E} {K : Submodule 𝕜 E}
    (hker : ker u = Kᗮ) (hiso : ∀ x ∈ K, ‖u x‖ = ‖x‖) :
    IsPartialIsometry u := by
  rw [isPartialIsometry_iff_norm_map]
  intro x hx
  rw [hker, Submodule.orthogonal_orthogonal] at hx
  exact hiso x hx


end TauCeti
end
