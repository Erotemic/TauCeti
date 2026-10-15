/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module

public import TauCeti.LinearAlgebra.Matrix.Rank

import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Uniqueness of exact-rank matrix factorizations

An exact-rank factorization `M = L * R` is unique up to an invertible change of basis
on its intermediate space (MSS-A08). The existence and rank-characterization results
MSS-A01--A03 are already provided by `TauCeti.LinearAlgebra.Matrix.Rank`.

## Main result

* `Matrix.exists_unit_eq_mul_of_rank_factorization`: two exact-rank factorizations
  differ by a unit on the intermediate space.

## Provenance

Adapted from `ForTauCeti/LinearAlgebra/Matrix/RankFactorization.lean` in
[Kitware's DKPS formalization](https://github.com/AIQ-Kitware/aiq-dkps-formalization),
originally developed by Jon Crall and Claude Fable 5 (Apache-2.0).
-/

public section

namespace Matrix

variable {𝕜 m n : Type*} [Field 𝕜] [Fintype n]

-- Only used in the MSS-A08 uniqueness proof. The row index type need not be finite.
private theorem rank_eq_card_iff_mulVec_injective {ι : Type*} [Fintype ι]
    (B : Matrix m ι 𝕜) :
    B.rank = Fintype.card ι ↔ Function.Injective B.mulVec := by
  rw [mulVec_injective_iff, rank_eq_finrank_span_cols,
    linearIndependent_iff_card_eq_finrank_span, Set.finrank, eq_comm]

section Uniqueness

/-- If `M = L * R` has rank equal to the number of columns of `L`, then `L`
has full column rank. The intermediate index may be any finite type. -/
private theorem rank_left_factor_eq {ι : Type*} [Fintype ι]
    {M : Matrix m n 𝕜} {L : Matrix m ι 𝕜}
    {R : Matrix ι n 𝕜} (hM : M.rank = Fintype.card ι)
    (h : M = L * R) : L.rank = Fintype.card ι := by
  refine le_antisymm (by simpa using L.rank_le_card_width) ?_
  calc Fintype.card ι = M.rank := hM.symm
    _ = (L * R).rank := by rw [h]
    _ ≤ L.rank := Matrix.rank_mul_le_left L R

/-- An exact-rank left factor spans the column space of the factored matrix. -/
private theorem range_left_factor_eq {ι : Type*} [Fintype ι]
    {M : Matrix m n 𝕜} {L : Matrix m ι 𝕜}
    {R : Matrix ι n 𝕜} (hM : M.rank = Fintype.card ι) (h : M = L * R) :
    LinearMap.range L.mulVecLin = LinearMap.range M.mulVecLin := by
  refine (Submodule.eq_of_le_of_finrank_eq ?_ ?_).symm
  · rw [h, Matrix.mulVecLin_mul]
    exact LinearMap.range_comp_le_range _ _
  · have hL := rank_left_factor_eq hM h
    rw [Matrix.rank] at hM hL
    exact hM.trans hL.symm

omit [Fintype n] in
/-- If each column of `L'` belongs to the range of `L`, then `L'` factors
through `L`. The column index type `κ` need not be finite: a preimage is
chosen independently for each of its columns. -/
private theorem exists_mul_eq_of_range_le {ι κ : Type*} [Fintype ι]
    {L : Matrix m ι 𝕜} {L' : Matrix m κ 𝕜}
    (h : ∀ j : κ, L'.col j ∈ LinearMap.range L.mulVecLin) :
    ∃ G : Matrix ι κ 𝕜, L * G = L' := by
  classical
  have hpre (j : κ) : ∃ v : ι → 𝕜, L.mulVec v = L'.col j := h j
  choose v hv using hpre
  refine ⟨Matrix.of fun i j => v j i, ?_⟩
  ext i j
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using congrFun (hv j) i

/-- Two factorizations of the same matrix through any finite intermediate type `ι`,
when the rank equals `Fintype.card ι`, differ by an invertible change of basis.
The decidable equality instance supplies the identity matrix and square-matrix units. -/
theorem exists_unit_eq_mul_of_rank_factorization {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix m n 𝕜} (hM : M.rank = Fintype.card ι)
    {L L' : Matrix m ι 𝕜} {R R' : Matrix ι n 𝕜}
    (h : M = L * R) (h' : M = L' * R') :
    ∃ g : (Matrix ι ι 𝕜)ˣ,
      L' = L * (g : Matrix ι ι 𝕜) ∧
        R' = ((g⁻¹ : (Matrix ι ι 𝕜)ˣ) : Matrix ι ι 𝕜) * R := by
  classical
  have hrange : LinearMap.range L'.mulVecLin = LinearMap.range L.mulVecLin := by
    rw [range_left_factor_eq hM h', range_left_factor_eq hM h]
  have hcols : ∀ j : ι, L'.col j ∈ LinearMap.range L.mulVecLin := by
    intro j
    rw [← hrange, Matrix.range_mulVecLin]
    exact Submodule.subset_span (Set.mem_range_self j)
  have hcols' : ∀ j : ι, L.col j ∈ LinearMap.range L'.mulVecLin := by
    intro j
    rw [hrange, Matrix.range_mulVecLin]
    exact Submodule.subset_span (Set.mem_range_self j)
  obtain ⟨G, hG⟩ := exists_mul_eq_of_range_le (L := L) (L' := L') hcols
  obtain ⟨G', hG'⟩ := exists_mul_eq_of_range_le (L := L') (L' := L) hcols'
  have hLinj : Function.Injective L.mulVec :=
    (rank_eq_card_iff_mulVec_injective L).mp (rank_left_factor_eq hM h)
  have hL'inj : Function.Injective L'.mulVec :=
    (rank_eq_card_iff_mulVec_injective L').mp (rank_left_factor_eq hM h')
  have hGG' : G * G' = 1 := by
    rcases isEmpty_or_nonempty ι with hEmpty | hNonempty
    · apply Matrix.ext
      intro i j
      exact (hEmpty.false i).elim
    · let : Inhabited ι := ⟨Classical.choice hNonempty⟩
      apply (mul_right_injective_iff_mulVec_injective.mpr hLinj)
      exact calc
        L * (G * G') = (L * G) * G' := (Matrix.mul_assoc L G G').symm
        _ = L := by rw [hG, hG']
        _ = L * 1 := (Matrix.mul_one L).symm
  have hG'G : G' * G = 1 := by
    rcases isEmpty_or_nonempty ι with hEmpty | hNonempty
    · apply Matrix.ext
      intro i j
      exact (hEmpty.false i).elim
    · let : Inhabited ι := ⟨Classical.choice hNonempty⟩
      apply (mul_right_injective_iff_mulVec_injective.mpr hL'inj)
      exact calc
        L' * (G' * G) = (L' * G') * G := (Matrix.mul_assoc L' G' G).symm
        _ = L' := by rw [hG', hG]
        _ = L' * 1 := (Matrix.mul_one L').symm
  refine ⟨⟨G, G', hGG', hG'G⟩, hG.symm, ?_⟩
  have hR : R = G * R' := by
    rcases isEmpty_or_nonempty n with hEmpty | hNonempty
    · apply Matrix.ext
      intro i j
      exact (hEmpty.false j).elim
    · let : Inhabited n := ⟨Classical.choice hNonempty⟩
      apply (mul_right_injective_iff_mulVec_injective.mpr hLinj)
      exact calc
        L * R = M := h.symm
        _ = L' * R' := h'
        _ = (L * G) * R' := by rw [hG]
        _ = L * (G * R') := Matrix.mul_assoc L G R'
  rw [hR, ← Matrix.mul_assoc]
  simp [hG'G]

end Uniqueness

end Matrix
