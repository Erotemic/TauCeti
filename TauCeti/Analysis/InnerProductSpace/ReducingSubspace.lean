/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Algebra.Module.Submodule.Invariant

/-!
# Reducing subspaces and completeness of projected subspaces

This module develops roadmap targets **OG-15** and **OG-18** from
`OperatorTheory/OrthogonalGeometry`.

* `ContinuousLinearMap.Reduces` means that a submodule and its orthogonal complement are
  invariant under an operator, expressed using Mathlib's `Module.End.invtSubmodule`.
* Symmetric operators reduce every invariant submodule; reduction implies commutation with
  the orthogonal projector when it exists.
* A submodule admitting an orthogonal projection in a complete inner-product space is
  complete. A scoped instance makes this fact available to downstream spectral arguments.

## Provenance

Adapted from the DKPS formalization's
`ForTauCeti/Analysis/InnerProductSpace/ReducingSubspace.lean` (Kitware, Inc.,
Apache-2.0; original authors Jon Crall and GPT 5.6 High).
-/
public section

open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace ContinuousLinearMap

/-- A subspace reduces a bounded operator when both it and its orthogonal complement
belong to Mathlib's lattice of invariant submodules. (OG-15.) -/
@[expose]
def Reduces (A : E →L[𝕜] E) (U : Submodule 𝕜 E) : Prop :=
  U ∈ Module.End.invtSubmodule (A : E →ₗ[𝕜] E) ∧
    Uᗮ ∈ Module.End.invtSubmodule (A : E →ₗ[𝕜] E)

/-- The pointwise characterization of a reducing subspace. -/
theorem reduces_iff (A : E →L[𝕜] E) (U : Submodule 𝕜 E) :
    A.Reduces U ↔ (∀ x ∈ U, A x ∈ U) ∧ (∀ x ∈ Uᗮ, A x ∈ Uᗮ) :=
  Iff.rfl

/-- An invariant subspace of a symmetric operator is reducing. -/
theorem IsSymmetric.reduces_of_invariant {A : E →L[𝕜] E}
    (hA : A.IsSymmetric) {U : Submodule 𝕜 E}
    (hU : ∀ x ∈ U, A x ∈ U) : A.Reduces U := by
  apply (A.reduces_iff U).2
  refine ⟨hU, ?_⟩
  intro x hx
  rw [Submodule.mem_orthogonal]
  intro u hu
  -- states the goal as the inner-product identity the structure lemma expects.
  change ⟪u, (A : E →ₗ[𝕜] E) x⟫_𝕜 = 0
  rw [← hA u x]
  exact Submodule.inner_right_of_mem_orthogonal (hU u hu) hx

/-- The orthogonal projection onto a reducing subspace commutes with the
operator. -/
theorem starProjection_comp_comm_of_reduces
    (A : E →L[𝕜] E) (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (hU : A.Reduces U) :
    U.starProjection ∘L A = A ∘L U.starProjection := by
  ext x
  -- states the goal with the definition unfolded, in the shape the next step needs;
  -- there is no `_apply` lemma to rewrite with here.
  change U.starProjection (A x) = A (U.starProjection x)
  have hpx : U.starProjection x ∈ U := U.starProjection_apply_mem x
  have hrest : x - U.starProjection x ∈ Uᗮ :=
    U.sub_starProjection_mem_orthogonal x
  obtain ⟨hU_main, hU_orth⟩ := (A.reduces_iff U).1 hU
  have hApx : A (U.starProjection x) ∈ U := hU_main _ hpx
  have hArest : A (x - U.starProjection x) ∈ Uᗮ := hU_orth _ hrest
  have hsplit : A x = A (U.starProjection x) + A (x - U.starProjection x) := by
    calc
      A x = A (U.starProjection x + (x - U.starProjection x)) := by
        congr 1
        rw [add_comm, sub_add_cancel]
      _ = A (U.starProjection x) + A (x - U.starProjection x) := map_add A _ _
  rw [hsplit, map_add,
    Submodule.starProjection_eq_self_iff.mpr hApx,
    (Submodule.starProjection_apply_eq_zero_iff U).mpr hArest,
    add_zero]

/-- Pointwise form of `starProjection_comp_comm_of_reduces`. -/
theorem starProjection_apply_comm_of_reduces
    (A : E →L[𝕜] E) (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (hU : A.Reduces U) (x : E) :
    U.starProjection (A x) = A (U.starProjection x) := by
  have h := congrArg (fun T : E →L[𝕜] E => T x)
    (starProjection_comp_comm_of_reduces A U hU)
  simpa only [ContinuousLinearMap.comp_apply] using h

end ContinuousLinearMap


namespace Submodule

/-- A subspace admitting an orthogonal projection is complete when the ambient
space is complete. (OG-18.) -/
theorem isComplete_coe_of_hasOrthogonalProjection [CompleteSpace E]
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    IsComplete (U : Set E) := by
  have hclosed : IsClosed ((Uᗮ)ᗮ : Set E) := Uᗮ.isClosed_orthogonal
  rw [Submodule.orthogonal_orthogonal] at hclosed
  exact hclosed.isComplete

end Submodule

namespace TauCeti.CompleteSubspace

/-- Opt-in completeness instance for subspaces with an orthogonal projection.
Activate it with `open scoped TauCeti.CompleteSubspace`. -/
scoped instance instCompleteSpaceCoeOfHasOrthogonalProjection
    {𝕜 : Type*} [RCLike 𝕜] {G : Type*} [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 G] [CompleteSpace G]
    (U : Submodule 𝕜 G) [U.HasOrthogonalProjection] : CompleteSpace U :=
  (Submodule.isComplete_coe_of_hasOrthogonalProjection U).completeSpace_coe

end TauCeti.CompleteSubspace
