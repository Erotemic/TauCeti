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
This module proves symmetry of the extension for invariant self-adjoint blocks and obtains
the global form bounds from finite-dimensional restricted point-spectrum containment.

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

/-- The reduced extension of a symmetric operator along an invariant subspace is symmetric. -/
theorem isSymmetric_reducedExtension [CompleteSpace E] (T : E →L[𝕜] E)
    {W : Submodule 𝕜 E} [W.HasOrthogonalProjection]
    (hT : (T : E →ₗ[𝕜] E).IsSymmetric) (hW : ∀ x ∈ W, T x ∈ W) (κ : ℝ) :
    (T.reducedExtension W κ : E →ₗ[𝕜] E).IsSymmetric := by
  have hTsa : IsSelfAdjoint T :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mpr hT
  have hPsa : IsSelfAdjoint W.starProjection := isSelfAdjoint_starProjection W
  have hPperp : IsSelfAdjoint Wᗮ.starProjection := isSelfAdjoint_starProjection Wᗮ
  have hcomm : T ∘L W.starProjection = W.starProjection ∘L T := by
    ext x
    simp only [ContinuousLinearMap.comp_apply]
    exact (hT.starProjection_apply_comm (fun y hy => hW y hy) x).symm
  have hcomp : IsSelfAdjoint (T ∘L W.starProjection) :=
    (IsSelfAdjoint.commute_iff hTsa hPsa).mp hcomm
  have hcsa : IsSelfAdjoint (κ : 𝕜) :=
    isSelfAdjoint_iff.mpr (RCLike.conj_ofReal _)
  have hscalar : IsSelfAdjoint ((κ : 𝕜) • Wᗮ.starProjection) := by
    rw [isSelfAdjoint_iff, star_smul, hcsa.star_eq, hPperp.star_eq]
  have hsa : IsSelfAdjoint (T.reducedExtension W κ) := by
    have hEq : T.reducedExtension W κ =
        T ∘L W.starProjection + (κ : 𝕜) • Wᗮ.starProjection := by
      ext x
      rw [T.reducedExtension_apply W κ x, add_apply, comp_apply, smul_apply]
    rw [hEq]
    exact hcomp.add hscalar
  exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mp hsa

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
