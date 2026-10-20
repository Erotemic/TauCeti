/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5, GPT-6
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import TauCeti.Analysis.InnerProductSpace.InvariantSubspace
public import TauCeti.Analysis.InnerProductSpace.PointSpectrum

/-!
# Reduced extensions of invariant Hilbert-space blocks

For a bounded operator `T` leaving a subspace `W` invariant, the reduced extension
`T.reducedExtension W k` agrees with `T` on `W` and is multiplication by a real scalar
`k` on `Wᗮ`. Its quadratic form separates into the contributions of the two orthogonal
blocks, so local upper and lower form bounds extend to the full space. In finite dimension,
restricted point-spectrum containment supplies those local bounds.

The quadratic-form splitting proof and its Pythagorean lemma are adapted from the
AIQ-Kitware DKPS formalization, Apache-2.0, in
`ForTauCeti/Analysis/InnerProductSpace/ReducedExtension.lean`.

## Main declarations

* `ContinuousLinearMap.reducedExtension`: the block extension.
* `ContinuousLinearMap.reducedExtension_apply_of_mem` and
  `ContinuousLinearMap.reducedExtension_apply_of_mem_orthogonal`: actions on the two blocks.
* `ContinuousLinearMap.isSymmetric_reducedExtension`: symmetry of the extension.
* `ContinuousLinearMap.re_inner_reducedExtension_self_le` and
  `ContinuousLinearMap.le_re_inner_reducedExtension_self`: global form bounds.
* The corresponding `..._of_pointSpectrumIn` statements obtain the local form hypotheses
  from the restricted spectrum of a finite-dimensional symmetric operator.
-/

public section

open scoped InnerProductSpace

namespace TauCeti

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **Pythagoras for an orthogonal projection.**  A vector splits into its
projection and the complementary part, and the squared norms add. -/
theorem norm_sq_eq_starProjection_add_sub {W : Submodule 𝕜 E}
    [W.HasOrthogonalProjection] (x : E) :
    ‖x‖ ^ 2 = ‖W.starProjection x‖ ^ 2 + ‖x - W.starProjection x‖ ^ 2 := by
  have hpx : W.starProjection x ∈ W := W.starProjection_apply_mem x
  have hrest : x - W.starProjection x ∈ Wᗮ :=
    W.sub_starProjection_mem_orthogonal x
  have h0 : RCLike.re ⟪W.starProjection x, x - W.starProjection x⟫_𝕜 = 0 := by
    rw [Submodule.inner_right_of_mem_orthogonal hpx hrest]; simp
  have hns := norm_add_sq (𝕜 := 𝕜) (W.starProjection x) (x - W.starProjection x)
  rw [show W.starProjection x + (x - W.starProjection x) = x by abel, h0] at hns
  linarith

/-- **The quadratic form of a reduced extension splits.**  If `W` is invariant
under `R`, then the extension agreeing with `R` on `W` and with the real scalar
`κ` on `Wᗮ` has quadratic form

`re ⟪R (P x), P x⟫ + κ ‖x - P x‖²`,

both cross terms vanishing by orthogonality.

Stated at the value `R (P x) + κ • (x - P x)` rather than at a bundled operator,
so that callers packaging the extension as a `ContinuousLinearMap` — by any
route, with or without finite-dimensionality — can use it after a one-line
`simp`. -/
theorem re_inner_reducedExtension_self {R : E →ₗ[𝕜] E} {W : Submodule 𝕜 E}
    [W.HasOrthogonalProjection] (hinv : ∀ x ∈ W, R x ∈ W) (κ : ℝ) (x : E) :
    RCLike.re ⟪R (W.starProjection x)
        + ((κ : ℝ) : 𝕜) • (x - W.starProjection x), x⟫_𝕜
      = RCLike.re ⟪R (W.starProjection x), W.starProjection x⟫_𝕜
        + κ * ‖x - W.starProjection x‖ ^ 2 := by
  have hpx : W.starProjection x ∈ W := W.starProjection_apply_mem x
  have hrest : x - W.starProjection x ∈ Wᗮ :=
    W.sub_starProjection_mem_orthogonal x
  have hre : RCLike.re ⟪R (W.starProjection x)
        + ((κ : ℝ) : 𝕜) • (x - W.starProjection x), x⟫_𝕜
      = RCLike.re ⟪R (W.starProjection x), x⟫_𝕜
        + κ * RCLike.re ⟪x - W.starProjection x, x⟫_𝕜 := by
    rw [inner_add_left, inner_smul_left, RCLike.conj_ofReal, map_add,
      RCLike.re_ofReal_mul]
  have h1 : RCLike.re ⟪R (W.starProjection x), x⟫_𝕜
      = RCLike.re ⟪R (W.starProjection x), W.starProjection x⟫_𝕜 := by
    have hz : ⟪R (W.starProjection x), x - W.starProjection x⟫_𝕜 = 0 :=
      Submodule.inner_right_of_mem_orthogonal (hinv _ hpx) hrest
    have hsplit : ⟪R (W.starProjection x), x⟫_𝕜
        = ⟪R (W.starProjection x), W.starProjection x⟫_𝕜
          + ⟪R (W.starProjection x), x - W.starProjection x⟫_𝕜 := by
      rw [← inner_add_right]; congr 1; abel
    rw [hsplit, hz, add_zero]
  have h2 : RCLike.re ⟪x - W.starProjection x, x⟫_𝕜
      = ‖x - W.starProjection x‖ ^ 2 := by
    have hz : ⟪x - W.starProjection x, W.starProjection x⟫_𝕜 = 0 :=
      Submodule.inner_left_of_mem_orthogonal hpx hrest
    have hsplit : ⟪x - W.starProjection x, x⟫_𝕜
        = ⟪x - W.starProjection x, x - W.starProjection x⟫_𝕜 := by
      have h' : ⟪x - W.starProjection x, x⟫_𝕜
          = ⟪x - W.starProjection x, W.starProjection x⟫_𝕜
            + ⟪x - W.starProjection x, x - W.starProjection x⟫_𝕜 := by
        rw [← inner_add_right]; congr 1; abel
      rw [h', hz, zero_add]
    rw [hsplit, inner_self_eq_norm_sq]
  rw [hre, h1, h2]

end TauCeti

namespace ContinuousLinearMap

open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Extend the block of `T` on `W` by the real scalar `κ` on its orthogonal complement.
If `W` is `T`-invariant, the result agrees with `T` on `W`. -/
noncomputable def reducedExtension (T : E →L[𝕜] E) (W : Submodule 𝕜 E)
    [W.HasOrthogonalProjection] (κ : ℝ) : E →L[𝕜] E :=
  T ∘L W.starProjection + (κ : 𝕜) • (1 - W.starProjection)

@[simp]
theorem reducedExtension_apply (T : E →L[𝕜] E) (W : Submodule 𝕜 E)
    [W.HasOrthogonalProjection] (κ : ℝ) (x : E) :
    T.reducedExtension W κ x =
      T (W.starProjection x) + (κ : 𝕜) • (x - W.starProjection x) := by
  simp only [reducedExtension, add_apply, ContinuousLinearMap.comp_apply, smul_apply,
    sub_apply, one_apply_eq_self]

/-- On the selected block, a reduced extension equals the original operator. -/
@[simp]
theorem reducedExtension_apply_of_mem (T : E →L[𝕜] E) (W : Submodule 𝕜 E)
    [W.HasOrthogonalProjection] (κ : ℝ) {x : E} (hx : x ∈ W) :
    T.reducedExtension W κ x = T x := by
  rw [reducedExtension_apply, W.starProjection_eq_self_iff.mpr hx]
  simp

/-- On the orthogonal complement, a reduced extension acts by its scalar value. -/
@[simp]
theorem reducedExtension_apply_of_mem_orthogonal (T : E →L[𝕜] E)
    (W : Submodule 𝕜 E) [W.HasOrthogonalProjection] (κ : ℝ)
    {x : E} (hx : x ∈ Wᗮ) :
    T.reducedExtension W κ x = (κ : 𝕜) • x := by
  rw [reducedExtension_apply, W.starProjection_apply_eq_zero_iff.mpr hx]
  simp

/-- A reduced extension of a symmetric operator along an invariant subspace is symmetric.
Its orthogonal projection commutes with the original symmetric operator. -/
theorem isSymmetric_reducedExtension [CompleteSpace E] (T : E →L[𝕜] E)
    {W : Submodule 𝕜 E} [W.HasOrthogonalProjection]
    (hT : (T : E →ₗ[𝕜] E).IsSymmetric) (hW : ∀ x ∈ W, T x ∈ W) (κ : ℝ) :
    (T.reducedExtension W κ : E →ₗ[𝕜] E).IsSymmetric := by
  have hTsa : IsSelfAdjoint T :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mpr hT
  have hPsa : IsSelfAdjoint W.starProjection := isSelfAdjoint_starProjection W
  have hcomm : T ∘L W.starProjection = W.starProjection ∘L T := by
    ext x
    simp only [ContinuousLinearMap.comp_apply]
    exact (hT.starProjection_apply_comm (fun y hy => hW y hy) x).symm
  have hcomp : IsSelfAdjoint (T ∘L W.starProjection) :=
    (IsSelfAdjoint.commute_iff hTsa hPsa).mp hcomm
  have hcsa : IsSelfAdjoint (κ : 𝕜) :=
    isSelfAdjoint_iff.mpr (RCLike.conj_ofReal _)
  have hone : IsSelfAdjoint (1 : E →L[𝕜] E) := IsSelfAdjoint.one _
  have hscalar : IsSelfAdjoint ((κ : 𝕜) • (1 - W.starProjection)) := by
    rw [isSelfAdjoint_iff, star_smul, hcsa.star_eq, (hone.sub hPsa).star_eq]
  have hsa : IsSelfAdjoint (T.reducedExtension W κ) := by
    change IsSelfAdjoint (T ∘L W.starProjection + (κ : 𝕜) • (1 - W.starProjection))
    exact hcomp.add hscalar
  exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mp hsa

/-- Orthogonal splitting of the quadratic form of a reduced extension. -/
theorem re_inner_reducedExtension_self (T : E →L[𝕜] E)
    {W : Submodule 𝕜 E} [W.HasOrthogonalProjection]
    (hW : ∀ x ∈ W, T x ∈ W) (κ : ℝ) (x : E) :
    RCLike.re ⟪T.reducedExtension W κ x, x⟫_𝕜 =
      RCLike.re ⟪T (W.starProjection x), W.starProjection x⟫_𝕜 +
        κ * ‖x - W.starProjection x‖ ^ 2 := by
  rw [reducedExtension_apply]
  exact TauCeti.re_inner_reducedExtension_self
    (R := (T : E →ₗ[𝕜] E)) hW κ x

/-- An upper bound on an invariant block extends to the ambient space if the scalar on the
orthogonal complement is no larger than the same upper bound. -/
theorem re_inner_reducedExtension_self_le (T : E →L[𝕜] E)
    {W : Submodule 𝕜 E} [W.HasOrthogonalProjection]
    (hW : ∀ x ∈ W, T x ∈ W) {c κ : ℝ} (hκ : κ ≤ c)
    (hlocal : ∀ x ∈ W, RCLike.re ⟪T x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2) (x : E) :
    RCLike.re ⟪T.reducedExtension W κ x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2 := by
  calc
    RCLike.re ⟪T.reducedExtension W κ x, x⟫_𝕜 =
        RCLike.re ⟪T (W.starProjection x), W.starProjection x⟫_𝕜 +
          κ * ‖x - W.starProjection x‖ ^ 2 :=
      T.re_inner_reducedExtension_self hW κ x
    _ ≤ c * ‖W.starProjection x‖ ^ 2 + c * ‖x - W.starProjection x‖ ^ 2 :=
      add_le_add (hlocal _ (W.starProjection_apply_mem x))
        (mul_le_mul_of_nonneg_right hκ (sq_nonneg _))
    _ = c * ‖x‖ ^ 2 := by
      rw [TauCeti.norm_sq_eq_starProjection_add_sub (W := W) x]
      ring

/-- A lower bound on an invariant block extends to the ambient space if the scalar on the
orthogonal complement is at least the same lower bound. -/
theorem le_re_inner_reducedExtension_self (T : E →L[𝕜] E)
    {W : Submodule 𝕜 E} [W.HasOrthogonalProjection]
    (hW : ∀ x ∈ W, T x ∈ W) {c κ : ℝ} (hκ : c ≤ κ)
    (hlocal : ∀ x ∈ W, c * ‖x‖ ^ 2 ≤ RCLike.re ⟪T x, x⟫_𝕜) (x : E) :
    c * ‖x‖ ^ 2 ≤ RCLike.re ⟪T.reducedExtension W κ x, x⟫_𝕜 := by
  calc
    c * ‖x‖ ^ 2 =
        c * ‖W.starProjection x‖ ^ 2 + c * ‖x - W.starProjection x‖ ^ 2 := by
      rw [TauCeti.norm_sq_eq_starProjection_add_sub (W := W) x]
      ring
    _ ≤ RCLike.re ⟪T (W.starProjection x), W.starProjection x⟫_𝕜 +
          κ * ‖x - W.starProjection x‖ ^ 2 :=
      add_le_add (hlocal _ (W.starProjection_apply_mem x))
        (mul_le_mul_of_nonneg_right hκ (sq_nonneg _))
    _ = RCLike.re ⟪T.reducedExtension W κ x, x⟫_𝕜 :=
      (T.re_inner_reducedExtension_self hW κ x).symm

section FiniteDimensional

variable [FiniteDimensional 𝕜 E]

/-- Restricted point-spectrum containment in `(-∞, c]` gives a global upper form bound
for a reduced extension with scalar `κ ≤ c`. -/
theorem re_inner_reducedExtension_self_le_of_pointSpectrumIn (T : E →L[𝕜] E)
    {W : Submodule 𝕜 E} [W.HasOrthogonalProjection]
    (hT : (T : E →ₗ[𝕜] E).IsSymmetric) (hW : ∀ x ∈ W, T x ∈ W)
    {c κ : ℝ} (hκ : κ ≤ c)
    (hspec : Module.End.PointSpectrumIn (T : E →ₗ[𝕜] E) W (Set.Iic c)) (x : E) :
    RCLike.re ⟪T.reducedExtension W κ x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2 :=
  T.re_inner_reducedExtension_self_le hW hκ
    (fun _ hy => hT.re_inner_apply_self_le_of_pointSpectrumIn hW hspec hy) x

/-- Restricted point-spectrum containment in `[c, ∞)` gives a global lower form bound
for a reduced extension with scalar `κ ≥ c`. -/
theorem le_re_inner_reducedExtension_self_of_pointSpectrumIn (T : E →L[𝕜] E)
    {W : Submodule 𝕜 E} [W.HasOrthogonalProjection]
    (hT : (T : E →ₗ[𝕜] E).IsSymmetric) (hW : ∀ x ∈ W, T x ∈ W)
    {c κ : ℝ} (hκ : c ≤ κ)
    (hspec : Module.End.PointSpectrumIn (T : E →ₗ[𝕜] E) W (Set.Ici c)) (x : E) :
    c * ‖x‖ ^ 2 ≤ RCLike.re ⟪T.reducedExtension W κ x, x⟫_𝕜 :=
  T.le_re_inner_reducedExtension_self hW hκ
    (fun _ hy => hT.le_re_inner_apply_self_of_pointSpectrumIn hW hspec hy) x

end FiniteDimensional

end ContinuousLinearMap
