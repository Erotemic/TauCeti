/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5, GPT-6
-/
module

public import TauCeti.Analysis.InnerProductSpace.Projection.Block
public import TauCeti.Analysis.InnerProductSpace.InvariantSubspace
public import TauCeti.Analysis.InnerProductSpace.PointSpectrum

/-!
# Symmetry and spectral bounds for reduced extensions

`ContinuousLinearMap.reducedExtension` is defined in `Projection.Block`, together with its
block actions, quadratic-form splitting and global bounds from local quadratic-form bounds.
This module proves symmetry of the extension for invariant symmetric blocks, without a
completeness assumption, and obtains the global form bounds from finite-dimensional
restricted point-spectrum containment.

## Provenance

The spectral consequences are adapted from the maintained
[AIQ-Kitware DKPS formalization](https://github.com/AIQ-Kitware/aiq-dkps-formalization)
(Kitware, Inc.; Apache-2.0), `ForTauCeti/Analysis/InnerProductSpace/ReducedExtension.lean`.
The common block splitting and bounds reuse `Projection.Block` rather than duplicating them.
-/

public section

open scoped InnerProductSpace

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The reduced extension of a symmetric operator along an invariant subspace is symmetric,
without any completeness hypothesis on the ambient inner product space. -/
theorem isSymmetric_reducedExtension (T : E →L[𝕜] E)
    {W : Submodule 𝕜 E} [W.HasOrthogonalProjection]
    (hT : (T : E →ₗ[𝕜] E).IsSymmetric) (hW : ∀ x ∈ W, T x ∈ W) (κ : ℝ) :
    (T.reducedExtension W κ : E →ₗ[𝕜] E).IsSymmetric := by
  have hcomm (y : E) : W.starProjection (T y) = T (W.starProjection y) :=
    hT.starProjection_apply_comm (fun z hz => hW z hz) y
  have hblock (x y : E) :
      ⟪T (W.starProjection x), y⟫_𝕜 = ⟪x, T (W.starProjection y)⟫_𝕜 := by
    calc
      _ = ⟪W.starProjection x, T y⟫_𝕜 := hT _ _
      _ = ⟪x, W.starProjection (T y)⟫_𝕜 := W.starProjection_isSymmetric x (T y)
      _ = ⟪x, T (W.starProjection y)⟫_𝕜 := by rw [hcomm y]
  have hscalar (x y : E) :
      ⟪(κ : 𝕜) • Wᗮ.starProjection x, y⟫_𝕜 =
        ⟪x, (κ : 𝕜) • Wᗮ.starProjection y⟫_𝕜 := by
    have hproj : ⟪Wᗮ.starProjection x, y⟫_𝕜 =
        ⟪x, Wᗮ.starProjection y⟫_𝕜 := Wᗮ.starProjection_isSymmetric x y
    simpa only [inner_smul_left, inner_smul_right, RCLike.conj_ofReal] using
      congrArg (fun z : 𝕜 => (κ : 𝕜) * z) hproj
  intro x y
  -- `IsSymmetric` is stated for the underlying linear map. The `change` reduces the
  -- continuous-to-linear-map coercion so the pointwise `reducedExtension_apply` lemma applies.
  change ⟪T.reducedExtension W κ x, y⟫_𝕜 =
    ⟪x, T.reducedExtension W κ y⟫_𝕜
  rw [T.reducedExtension_apply W κ x, T.reducedExtension_apply W κ y,
    inner_add_left, inner_add_right, hblock x y, hscalar x y]

section FiniteDimensional

variable [FiniteDimensional 𝕜 E]

/-- Restricted point-spectrum containment in `(-∞, c]` gives an upper bound
for a reduced extension with scalar `κ ≤ c`. -/
theorem re_inner_reducedExtension_self_le_of_pointSpectrumIn (T : E →L[𝕜] E)
    {W : Submodule 𝕜 E} [W.HasOrthogonalProjection]
    (hT : (T : E →ₗ[𝕜] E).IsSymmetric) (hW : ∀ x ∈ W, T x ∈ W)
    {c κ : ℝ} (hκ : κ ≤ c)
    (hspec : Module.End.PointSpectrumIn (T : E →ₗ[𝕜] E) W (Set.Iic c)) (x : E) :
    RCLike.re ⟪T.reducedExtension W κ x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2 :=
  W.re_inner_comp_starProjection_add_smul_apply_self_le
    (B := T) (r := c) (κ := κ) hW hκ
    (fun _ hy => hT.re_inner_apply_self_le_of_pointSpectrumIn hW hspec hy) x

/-- Restricted point-spectrum containment in `[c, ∞)` gives a lower bound
for a reduced extension with scalar `κ ≥ c`. -/
theorem le_re_inner_reducedExtension_self_of_pointSpectrumIn (T : E →L[𝕜] E)
    {W : Submodule 𝕜 E} [W.HasOrthogonalProjection]
    (hT : (T : E →ₗ[𝕜] E).IsSymmetric) (hW : ∀ x ∈ W, T x ∈ W)
    {c κ : ℝ} (hκ : c ≤ κ)
    (hspec : Module.End.PointSpectrumIn (T : E →ₗ[𝕜] E) W (Set.Ici c)) (x : E) :
    c * ‖x‖ ^ 2 ≤ RCLike.re ⟪T.reducedExtension W κ x, x⟫_𝕜 :=
  W.le_re_inner_comp_starProjection_add_smul_apply_self
    (A := T) (r := c) (κ := κ) hW hκ
    (fun _ hy => hT.le_re_inner_apply_self_of_pointSpectrumIn hW hspec hy) x

end FiniteDimensional

end ContinuousLinearMap
