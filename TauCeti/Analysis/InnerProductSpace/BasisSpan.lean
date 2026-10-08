/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Spans of orthonormal subfamilies

For an orthonormal basis `b : OrthonormalBasis ι 𝕜 E` and a set `s : Set ι`,
`b.spanIndices s` is the subspace spanned by the basis vectors indexed by `s`.

## Main results

* `OrthonormalBasis.spanIndices`: the selected subspace.
* `OrthonormalBasis.spanIndices_mono`: enlarging the index set enlarges the span.
* `OrthonormalBasis.mem_spanIndices_iff`: membership is equivalent to vanishing
  of all basis coordinates outside `s`.
* `OrthonormalBasis.finrank_spanIndices`: the span's dimension is the number of
  selected indices.
* `OrthonormalBasis.orthogonal_spanIndices`: its orthogonal complement is the
  span of the complementary subfamily.

## Source

Ported from `ForTauCeti/Analysis/InnerProductSpace/BasisSpan.lean` in the
[AIQ-Kitware DKPS formalization](https://github.com/AIQ-Kitware/aiq-dkps-formalization)
(Kitware, Inc.; Apache-2.0). Its selected-span construction originates in the
donor's Courant--Fischer development. The definitions and proofs are unchanged.
-/

public section

namespace OrthonormalBasis

open Module (finrank)
open scoped InnerProductSpace

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [Fintype ι]

/-- The subspace spanned by the orthonormal basis vectors `b i` for indices
`i ∈ s`. -/
@[expose]
noncomputable def spanIndices (b : OrthonormalBasis ι 𝕜 E) (s : Set ι) :
    Submodule 𝕜 E :=
  Submodule.span 𝕜 (b '' s)

/-- A selected basis span equals the submodule span of the corresponding vectors. -/
theorem spanIndices_eq_span (b : OrthonormalBasis ι 𝕜 E) (s : Set ι) :
    b.spanIndices s = Submodule.span 𝕜 (b '' s) := (rfl)

/-- Selecting more indices spans more. -/
theorem spanIndices_mono (b : OrthonormalBasis ι 𝕜 E) {s t : Set ι} (h : s ⊆ t) :
    b.spanIndices s ≤ b.spanIndices t :=
  Submodule.span_mono (Set.image_mono h)

/-- A selected basis vector lies in the span of its index set. -/
theorem mem_spanIndices_of_mem (b : OrthonormalBasis ι 𝕜 E) {s : Set ι} {i : ι}
    (hi : i ∈ s) : b i ∈ b.spanIndices s :=
  Submodule.subset_span ⟨i, hi, rfl⟩

/-- A vector in the span of a selected subfamily has zero coordinate at any
index outside the selection. -/
theorem repr_eq_zero_of_mem_spanIndices (b : OrthonormalBasis ι 𝕜 E)
    {s : Set ι} {x : E} (hx : x ∈ b.spanIndices s) {i : ι} (hi : i ∉ s) :
    b.repr x i = 0 := by
  rw [b.repr_apply_apply]
  -- `⟪b i, ·⟫` vanishes on the spanning set, hence on the whole span.
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · rintro y ⟨j, hj, rfl⟩
    refine b.inner_eq_zero ?_
    rintro rfl
    exact hi hj
  · rw [inner_zero_right]
  · intro y z _ _ hy hz
    rw [inner_add_right, hy, hz, add_zero]
  · intro a y _ hy
    rw [inner_smul_right, hy, mul_zero]

/-- Membership in the span of a selected subfamily is exactly the vanishing of
the coordinates outside the selection. -/
theorem mem_spanIndices_iff (b : OrthonormalBasis ι 𝕜 E) {s : Set ι} {x : E} :
    x ∈ b.spanIndices s ↔ ∀ i ∉ s, b.repr x i = 0 := by
  classical
  refine ⟨fun hx i hi => b.repr_eq_zero_of_mem_spanIndices hx hi, fun h => ?_⟩
  rw [← b.sum_repr x]
  refine Submodule.sum_mem _ fun i _ => ?_
  by_cases hi : i ∈ s
  · exact Submodule.smul_mem _ _ (b.mem_spanIndices_of_mem hi)
  · rw [h i hi, zero_smul]
    exact Submodule.zero_mem _

/-- The span of a selected subfamily has dimension the number of selected
indices. -/
theorem finrank_spanIndices (b : OrthonormalBasis ι 𝕜 E) (s : Finset ι) :
    finrank 𝕜 (b.spanIndices ↑s) = s.card := by
  have h : finrank 𝕜 (Submodule.span 𝕜
      (Set.range fun i : ↥(↑s : Set ι) => b ↑i)) = Fintype.card ↥(↑s : Set ι) :=
    finrank_span_eq_card
      (b.orthonormal.linearIndependent.comp _ Subtype.val_injective)
  rw [spanIndices, Set.image_eq_range, h]
  simp

/-- `Set` form of `OrthonormalBasis.finrank_spanIndices`. -/
theorem finrank_spanIndices_set (b : OrthonormalBasis ι 𝕜 E) (s : Set ι)
    [DecidablePred (· ∈ s)] :
    finrank 𝕜 (b.spanIndices s) = s.toFinset.card := by
  rw [← b.finrank_spanIndices s.toFinset, Set.coe_toFinset]

/-- The orthogonal complement of the span of a selected subfamily is the span
of the complementary subfamily. -/
theorem orthogonal_spanIndices (b : OrthonormalBasis ι 𝕜 E) (s : Set ι) :
    (b.spanIndices s)ᗮ = b.spanIndices sᶜ := by
  classical
  have : FiniteDimensional 𝕜 E := Module.Finite.of_basis b.toBasis
  have hEcard : finrank 𝕜 E = Fintype.card ι := by
    rw [Module.finrank_eq_card_basis b.toBasis]
  refine (Submodule.eq_of_le_of_finrank_le ?_ ?_).symm
  · -- the complementary span is orthogonal to the selected span.
    apply Submodule.span_le.mpr
    rintro y ⟨j, hj, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_orthogonal]
    intro u hu
    rw [← inner_conj_symm, ← b.repr_apply_apply,
      b.repr_eq_zero_of_mem_spanIndices hu hj, map_zero]
  · -- dimensions match: `card ι − #s` on both sides.
    have h1 : finrank 𝕜 (b.spanIndices s)
        + finrank 𝕜 ((b.spanIndices s)ᗮ : Submodule 𝕜 E) = Fintype.card ι := by
      rw [Submodule.finrank_add_finrank_orthogonal, hEcard]
    have h2 := b.finrank_spanIndices_set s
    have h3 := b.finrank_spanIndices_set sᶜ
    have h4 : s.toFinset.card + (sᶜ).toFinset.card = Fintype.card ι := by
      rw [Set.toFinset_compl, Finset.card_compl]
      have := Finset.card_le_univ s.toFinset
      omega
    omega

end OrthonormalBasis

end
