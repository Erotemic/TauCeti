/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import TauCeti.Algebra.Star.PartialIsometry
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.InnerProductSpace.Subspace

/-!
# Rectangular partial isometries

For a linear map `u : E →ₗ[𝕜] F`, the equation `u ∘ₗ u.adjoint ∘ₗ u = u`
characterizes a partial isometry even when source and target differ. The
finite-dimensional characterization is preservation of norms on `(ker u)ᗮ`.
When source and target coincide, this agrees with the algebraic predicate
`TauCeti.IsPartialIsometry`. The bounded-operator version uses the same
adjoint-composition equation.

Based on the Apache-2.0 DKPS formalization (Kitware, Inc.).
-/

public section

open scoped InnerProductSpace

namespace LinearMap

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- **Partial isometry between possibly different spaces**: `u ∘ₗ u.adjoint ∘ₗ u = u`.

This is the Moore--Penrose-style identity that the algebraic `u * star u * u = u`
becomes when source and target differ and no single carrier holds both `u` and its
adjoint. -/
def IsPartialIsometry (u : E →ₗ[𝕜] F) : Prop :=
  u ∘ₗ u.adjoint ∘ₗ u = u

/-- The adjoint-composition equation defining a rectangular partial isometry. -/
theorem isPartialIsometry_iff {u : E →ₗ[𝕜] F} :
    u.IsPartialIsometry ↔ u ∘ₗ u.adjoint ∘ₗ u = u := Iff.rfl

/-- The rectangular and star-monoid predicates agree on endomorphisms (PD-B03). -/
theorem isPartialIsometry_iff_starMul {u : E →ₗ[𝕜] E} :
    u.IsPartialIsometry ↔ TauCeti.IsPartialIsometry u := by
  simp only [LinearMap.IsPartialIsometry, TauCeti.IsPartialIsometry, star_eq_adjoint,
    Module.End.mul_eq_comp, LinearMap.comp_assoc]


/-- Norm preservation on `(ker u)ᗮ` implies preservation of its inner products. -/
theorem inner_map_eq_of_norm_map_on_orthogonal_ker {u : E →ₗ[𝕜] F}
    (h : ∀ x ∈ (LinearMap.ker u)ᗮ, ‖u x‖ = ‖x‖)
    {a b : E} (ha : a ∈ (LinearMap.ker u)ᗮ) (hb : b ∈ (LinearMap.ker u)ᗮ) :
    ⟪u a, u b⟫_𝕜 = ⟪a, b⟫_𝕜 := by
  have hg : ∀ w : ((LinearMap.ker u)ᗮ), ‖(u ∘ₗ ((LinearMap.ker u)ᗮ).subtype) w‖ = ‖w‖ := by
    intro w
    simpa using h w.1 w.2
  have hmap := (LinearMap.norm_map_iff_inner_map_map
    (u ∘ₗ ((LinearMap.ker u)ᗮ).subtype)).mp hg ⟨a, ha⟩ ⟨b, hb⟩
  simpa using hmap

/-- Projecting onto `(ker u)ᗮ` does not change the value of a linear map. -/
theorem apply_starProjection_orthogonal_ker (u : E →ₗ[𝕜] F) (x : E) :
    u (((LinearMap.ker u)ᗮ).starProjection x) = u x := by
  set P := ((LinearMap.ker u)ᗮ).starProjection with hP
  have hmem0 : x - P x ∈ LinearMap.ker u := by
    have h1 : x - P x ∈ ((LinearMap.ker u)ᗮ)ᗮ := by
      rw [hP]
      exact Submodule.sub_starProjection_mem_orthogonal x
    rwa [Submodule.orthogonal_orthogonal] at h1
  rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at hmem0
  exact hmem0.symm

/-- If a linear map is isometric on `(ker u)ᗮ`, then its Gram operator is the
orthogonal projection onto that initial space. -/
theorem adjoint_comp_apply_eq_starProjection_of_norm_map {u : E →ₗ[𝕜] F}
    (h : ∀ x ∈ (LinearMap.ker u)ᗮ, ‖u x‖ = ‖x‖) (x : E) :
    u.adjoint (u x) = ((LinearMap.ker u)ᗮ).starProjection x := by
  have hq : u.adjoint (u x) ∈ (LinearMap.ker u)ᗮ := by
    rw [LinearMap.orthogonal_ker]
    exact LinearMap.mem_range_self _ _
  set P := ((LinearMap.ker u)ᗮ).starProjection with hP
  have hPx : P x ∈ (LinearMap.ker u)ᗮ := Submodule.starProjection_apply_mem _ _
  have hux : u x = u (P x) := (apply_starProjection_orthogonal_ker u x).symm
  have hmem : u.adjoint (u x) - P x ∈ (LinearMap.ker u)ᗮ := Submodule.sub_mem _ hq hPx
  set w := u.adjoint (u x) - P x with hw
  have hzero : ⟪w, w⟫_𝕜 = 0 := by
    have e1 : ⟪u.adjoint (u x), w⟫_𝕜 = ⟪P x, w⟫_𝕜 := by
      rw [LinearMap.adjoint_inner_left, hux,
        inner_map_eq_of_norm_map_on_orthogonal_ker h hPx hmem]
    calc ⟪w, w⟫_𝕜 = ⟪u.adjoint (u x), w⟫_𝕜 - ⟪P x, w⟫_𝕜 := by rw [hw, inner_sub_left]
      _ = 0 := by rw [e1, sub_self]
  have hw0 := inner_self_eq_zero.mp hzero
  rw [hw, sub_eq_zero] at hw0
  exact hw0

/-- A finite-dimensional rectangular partial isometry preserves norms precisely on the
orthogonal complement of its kernel (PD-B09). -/
theorem isPartialIsometry_iff_norm_map {u : E →ₗ[𝕜] F} :
    u.IsPartialIsometry ↔ ∀ x ∈ (LinearMap.ker u)ᗮ, ‖u x‖ = ‖x‖ := by
  constructor
  · intro hu x hx
    have hux : u (u.adjoint (u x)) = u x := by
      have := LinearMap.congr_fun hu x
      simpa only [LinearMap.comp_apply] using this
    -- `u⋆ u x` and `x` agree, because their difference lies in `ker u` and in `(ker u)ᗮ`
    have hmemO : u.adjoint (u x) ∈ (LinearMap.ker u)ᗮ := by
      rw [LinearMap.orthogonal_ker]; exact LinearMap.mem_range_self _ _
    have hdiffO : x - u.adjoint (u x) ∈ (LinearMap.ker u)ᗮ := Submodule.sub_mem _ hx hmemO
    have hdiffK : x - u.adjoint (u x) ∈ LinearMap.ker u := by
      rw [LinearMap.mem_ker, map_sub, hux, sub_self]
    have hadj : u.adjoint (u x) = x := by
      have hz : ⟪x - u.adjoint (u x), x - u.adjoint (u x)⟫_𝕜 = 0 :=
        Submodule.inner_right_of_mem_orthogonal hdiffK hdiffO
      have := inner_self_eq_zero.mp hz
      rw [sub_eq_zero] at this
      exact this.symm
    have hsq : ‖u x‖ ^ 2 = ‖x‖ ^ 2 := by
      rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := 𝕜) (u x),
        InnerProductSpace.norm_sq_eq_re_inner (𝕜 := 𝕜) x,
        ← LinearMap.adjoint_inner_left, hadj]
    rw [← Real.sqrt_sq (norm_nonneg (u x)), ← Real.sqrt_sq (norm_nonneg x), hsq]
  · intro h
    ext x
    have hqP := adjoint_comp_apply_eq_starProjection_of_norm_map h x
    simp only [LinearMap.comp_apply, hqP]
    exact apply_starProjection_orthogonal_ker u x

/-- The adjoint of a rectangular partial isometry is again a partial isometry. -/
theorem IsPartialIsometry.adjoint {u : E →ₗ[𝕜] F} (hu : u.IsPartialIsometry) :
    u.adjoint.IsPartialIsometry := by
  have h := congrArg LinearMap.adjoint hu
  unfold LinearMap.IsPartialIsometry
  simpa only [LinearMap.adjoint_comp, LinearMap.adjoint_adjoint, LinearMap.comp_assoc] using h

end LinearMap

namespace ContinuousLinearMap

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- **Partial isometry between possibly different spaces**, bounded form:
`u ∘L u.adjoint ∘L u = u`.

The same typed equation as `LinearMap.IsPartialIsometry`, stated on the bounded carrier so
that consumers on complete spaces -- the rectangular polar decomposition in particular --
never leave `→L`.  A rectangular map is not an element of one monoid, so the star-monoid
predicate `u * star u * u = u` is unavailable here. -/
def IsPartialIsometry (u : E →L[𝕜] F) : Prop :=
  u ∘L u.adjoint ∘L u = u

/-- The defining equation for a bounded rectangular partial isometry. -/
theorem isPartialIsometry_iff {u : E →L[𝕜] F} :
    u.IsPartialIsometry ↔ u ∘L u.adjoint ∘L u = u := Iff.rfl

/-- The range of `u.adjoint` is orthogonal to `ker u`. -/
theorem adjoint_apply_mem_orthogonal_ker (u : E →L[𝕜] F) (y : F) :
    u.adjoint y ∈ (LinearMap.ker u.toLinearMap)ᗮ := by
  refine (Submodule.mem_orthogonal' (LinearMap.ker u.toLinearMap) (u.adjoint y)).mpr ?_
  intro z hz
  have hz0 : u z = 0 := (LinearMap.mem_ker).mp hz
  rw [ContinuousLinearMap.adjoint_inner_left, hz0]
  simp

/-- A bounded partial isometry preserves norms exactly on the orthogonal complement
of its kernel; equivalently, it is isometric on its initial space (PD-B10). -/
theorem isPartialIsometry_iff_norm_map {u : E →L[𝕜] F} :
    u.IsPartialIsometry ↔
      ∀ x ∈ (LinearMap.ker u.toLinearMap)ᗮ, ‖u x‖ = ‖x‖ := by
  constructor
  · intro hu x hx
    have hux : u (u.adjoint (u x)) = u x := by
      have h := congrArg (fun g : E →L[𝕜] F => g x) hu
      simpa only [ContinuousLinearMap.comp_apply] using h
    have hmemO : u.adjoint (u x) ∈ (LinearMap.ker u.toLinearMap)ᗮ :=
      adjoint_apply_mem_orthogonal_ker u (u x)
    have hdiffO : x - u.adjoint (u x) ∈ (LinearMap.ker u.toLinearMap)ᗮ :=
      Submodule.sub_mem _ hx hmemO
    have hdiffK : x - u.adjoint (u x) ∈ LinearMap.ker u.toLinearMap := by
      apply (LinearMap.mem_ker).2
      change u (x - u.adjoint (u x)) = 0
      rw [map_sub, hux, sub_self]
    have hadj : u.adjoint (u x) = x := by
      have hz : ⟪x - u.adjoint (u x), x - u.adjoint (u x)⟫_𝕜 = 0 :=
        Submodule.inner_right_of_mem_orthogonal hdiffK hdiffO
      have h := inner_self_eq_zero.mp hz
      rw [sub_eq_zero] at h
      exact h.symm
    have hsq : ‖u x‖ ^ 2 = ‖x‖ ^ 2 := by
      rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := 𝕜) (u x),
        InnerProductSpace.norm_sq_eq_re_inner (𝕜 := 𝕜) x,
        ← ContinuousLinearMap.adjoint_inner_left, hadj]
    rw [← Real.sqrt_sq (norm_nonneg (u x)), ← Real.sqrt_sq (norm_nonneg x), hsq]
  · intro h
    have hinner : ∀ a ∈ (LinearMap.ker u.toLinearMap)ᗮ,
        ∀ b ∈ (LinearMap.ker u.toLinearMap)ᗮ,
        ⟪u a, u b⟫_𝕜 = ⟪a, b⟫_𝕜 := by
      have hg : ∀ w : ((LinearMap.ker u.toLinearMap)ᗮ),
          ‖(u.toLinearMap ∘ₗ ((LinearMap.ker u.toLinearMap)ᗮ).subtype) w‖ = ‖w‖ := by
        intro w
        simpa using h w.1 w.2
      intro a ha b hb
      have hmap := (LinearMap.norm_map_iff_inner_map_map
        (u.toLinearMap ∘ₗ ((LinearMap.ker u.toLinearMap)ᗮ).subtype)).mp
          hg ⟨a, ha⟩ ⟨b, hb⟩
      simpa using hmap
    ext x
    have hq : u.adjoint (u x) ∈ (LinearMap.ker u.toLinearMap)ᗮ :=
      adjoint_apply_mem_orthogonal_ker u (u x)
    set P := ((LinearMap.ker u.toLinearMap)ᗮ).starProjection with hP
    have hPx : P x ∈ (LinearMap.ker u.toLinearMap)ᗮ :=
      Submodule.starProjection_apply_mem _ _
    have hux : u x = u (P x) := by
      have hmem0 : x - P x ∈ LinearMap.ker u.toLinearMap := by
        have h1 : x - P x ∈ ((LinearMap.ker u.toLinearMap)ᗮ)ᗮ := by
          rw [hP]
          exact Submodule.sub_starProjection_mem_orthogonal x
        rwa [Submodule.orthogonal_orthogonal] at h1
      have hmap0 : u (x - P x) = 0 := (LinearMap.mem_ker).mp hmem0
      rw [map_sub, sub_eq_zero] at hmap0
      exact hmap0
    have hqP : u.adjoint (u x) = P x := by
      have hmem : u.adjoint (u x) - P x ∈ (LinearMap.ker u.toLinearMap)ᗮ :=
        Submodule.sub_mem _ hq hPx
      set w := u.adjoint (u x) - P x with hw
      have hzero : ⟪w, w⟫_𝕜 = 0 := by
        have e1 : ⟪u.adjoint (u x), w⟫_𝕜 = ⟪P x, w⟫_𝕜 := by
          rw [ContinuousLinearMap.adjoint_inner_left, hux, hinner (P x) hPx w hmem]
        calc ⟪w, w⟫_𝕜 = ⟪u.adjoint (u x), w⟫_𝕜 - ⟪P x, w⟫_𝕜 := by rw [hw, inner_sub_left]
          _ = 0 := by rw [e1, sub_self]
      have hw0 := inner_self_eq_zero.mp hzero
      rw [hw, sub_eq_zero] at hw0
      exact hw0
    simp only [ContinuousLinearMap.comp_apply, hqP]
    exact hux.symm

/-- The adjoint of a partial isometry is a partial isometry. -/
theorem IsPartialIsometry.adjoint {u : E →L[𝕜] F} (hu : u.IsPartialIsometry) :
    u.adjoint.IsPartialIsometry := by
  have h := congrArg ContinuousLinearMap.adjoint hu
  unfold ContinuousLinearMap.IsPartialIsometry
  simpa only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
    ← ContinuousLinearMap.comp_assoc] using h

end ContinuousLinearMap
