/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import TauCeti.Analysis.InnerProductSpace.Projection.FrobeniusSine
public import TauCeti.Analysis.InnerProductSpace.Spectrum
public import TauCeti.Analysis.InnerProductSpace.Orthonormal.Family
public import TauCeti.Analysis.InnerProductSpace.YuWangSamworth

/-!
# Population-gap Frobenius sin-theta bound

The Yu--Wang--Samworth population-gap residual sandwich already bounds the squared
cross-block overlap of the ordered eigenbases of two symmetric operators. This
module identifies that overlap with the squared Frobenius sine of the corresponding
subspaces and states the two-branch perturbation bound in subspace notation.

Only the eigenvalues of the population operator are assumed separated. No spectral
gap is imposed on the perturbed operator. The selected eigenblocks are those of
the canonical eigenbases at the same indices.

## Main result

* `LinearMap.IsSymmetric.sinThetaFrobenius_eigenvectorSpan_le`: the population-gap
  Frobenius sine estimate with the minimum of the dimension-scaled operator norm
  and the Frobenius norm of the perturbation.

## References

* TauCetiRoadmap, `SpectralSubspacePerturbation`, target SSP-D16.
* Y. Yu, T. Wang, and R. J. Samworth, *A useful variant of the Davis--Kahan
  theorem for statisticians*, Biometrika **102** (2015), 315--323.
* AIQ-Kitware DKPS formalization, `YuWangSamworth2015/Core/Statistics.lean`.
-/

public section

open Module (finrank)
open scoped InnerProductSpace

namespace LinearMap.IsSymmetric

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {A B : E →ₗ[𝕜] E} {n : ℕ}

/-! ### Connecting the cross-block overlap to the Frobenius sine -/

/-- For the eigenblocks selected by `s`, the squared Frobenius sine equals the
sum of squared overlaps between the perturbed block and the orthogonal
complement of the population block. -/
theorem sq_sinThetaFrobenius_eigenvectorSpan (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (hn : finrank 𝕜 E = n) (s : Finset (Fin n)) :
    (hB.eigenvectorSpan hn (↑s : Set (Fin n))).sinThetaFrobenius
      (hA.eigenvectorSpan hn (↑s : Set (Fin n))) ^ 2 =
      ∑ j ∈ s, ∑ k ∈ sᶜ,
        ‖⟪hA.eigenvectorBasis hn k, hB.eigenvectorBasis hn j⟫_𝕜‖ ^ 2 := by
  classical
  let a := hA.eigenvectorBasis hn
  let b := hB.eigenvectorBasis hn
  let U := a.spanIndices (↑s : Set (Fin n))
  let V := b.spanIndices (↑s : Set (Fin n))
  -- The eigenvector span is opaque across modules. Relate it to the
  -- selected orthonormal-basis span using the exported range theorem.
  let inclusion : (↑s : Set (Fin n)) ↪ Fin n :=
    ⟨(Subtype.val : (↑s : Set (Fin n)) → Fin n), Subtype.val_injective⟩
  -- The embedding and its underlying function are extensionally equal. Their
  -- coerced function expressions are not syntactically the same after `simp`.
  have hcoe :
      (inclusion : (↑s : Set (Fin n)) → Fin n) =
        (Subtype.val : (↑s : Set (Fin n)) → Fin n) := by
    funext i
    rfl
  have hrange : Set.range inclusion = (↑s : Set (Fin n)) := by
    calc
      Set.range inclusion =
          Set.range (Subtype.val : (↑s : Set (Fin n)) → Fin n) :=
            congrArg Set.range hcoe
      _ = (↑s : Set (Fin n)) := Subtype.range_coe
  have hfamilyA :
      (fun i : (↑s : Set (Fin n)) => hA.eigenvectorBasis hn (inclusion i)) =
        (a ∘ (Subtype.val : (↑s : Set (Fin n)) → Fin n)) := by
    funext i
    change hA.eigenvectorBasis hn (inclusion i) = hA.eigenvectorBasis hn (i : Fin n)
    exact congrArg (hA.eigenvectorBasis hn) (congrFun hcoe i)
  have hfamilyB :
      (fun i : (↑s : Set (Fin n)) => hB.eigenvectorBasis hn (inclusion i)) =
        (b ∘ (Subtype.val : (↑s : Set (Fin n)) → Fin n)) := by
    funext i
    change hB.eigenvectorBasis hn (inclusion i) = hB.eigenvectorBasis hn (i : Fin n)
    exact congrArg (hB.eigenvectorBasis hn) (congrFun hcoe i)
  have hspanA :
      hA.eigenvectorSpan hn (↑s : Set (Fin n)) = a.spanIndices (↑s : Set (Fin n)) := by
    calc
      _ = hA.eigenvectorSpan hn (Set.range inclusion) := by rw [hrange]
      _ = Submodule.span 𝕜
            (Set.range fun i : (↑s : Set (Fin n)) => hA.eigenvectorBasis hn (inclusion i)) :=
              (hA.span_range_eigenvectorBasis_apply_eq_eigenvectorSpan hn inclusion).symm
      _ = Submodule.span 𝕜
            (Set.range (a ∘ (Subtype.val : (↑s : Set (Fin n)) → Fin n))) := by
              rw [hfamilyA]
      _ = a.spanIndices (↑s : Set (Fin n)) :=
            a.span_range_comp_subtypeVal_eq_spanIndices (↑s : Set (Fin n))
  have hspanB :
      hB.eigenvectorSpan hn (↑s : Set (Fin n)) = b.spanIndices (↑s : Set (Fin n)) := by
    calc
      _ = hB.eigenvectorSpan hn (Set.range inclusion) := by rw [hrange]
      _ = Submodule.span 𝕜
            (Set.range fun i : (↑s : Set (Fin n)) => hB.eigenvectorBasis hn (inclusion i)) :=
              (hB.span_range_eigenvectorBasis_apply_eq_eigenvectorSpan hn inclusion).symm
      _ = Submodule.span 𝕜
            (Set.range (b ∘ (Subtype.val : (↑s : Set (Fin n)) → Fin n))) := by
              rw [hfamilyB]
      _ = b.spanIndices (↑s : Set (Fin n)) :=
            b.span_range_comp_subtypeVal_eq_spanIndices (↑s : Set (Fin n))
  rw [hspanA, hspanB]
  have hb (j : Fin n) :
      (V.sinThetaMap U) (b j) =
        if j ∈ s then Uᗮ.starProjection (b j) else 0 := by
    by_cases hj : j ∈ s
    · simp [hj, Submodule.sinThetaMap_apply,
        V.starProjection_eq_self_iff.mpr (b.mem_spanIndices_of_mem hj)]
    · have horth : b j ∈ Vᗮ := by
        rw [b.orthogonal_spanIndices]
        exact b.mem_spanIndices_of_mem (by simpa using hj)
      simp [hj, Submodule.sinThetaMap_apply,
        V.starProjection_apply_eq_zero_iff.mpr horth]
  have hcomp : Submodule.span 𝕜
        (Set.range (a ∘ ((↑) : (sᶜ : Finset (Fin n)) → Fin n))) = Uᗮ := by
    rw [a.orthogonal_spanIndices, ← Finset.coe_compl,
      a.span_range_comp_subtypeVal_eq_spanIndices]
  have hcoord (j : Fin n) :
      ‖Uᗮ.starProjection (b j)‖ ^ 2 =
        ∑ k ∈ sᶜ, ‖⟪a k, b j⟫_𝕜‖ ^ 2 := by
    rw [(a.orthonormal.comp _ Subtype.val_injective).norm_starProjection_sq_eq_sum hcomp]
    exact Finset.sum_coe_sort sᶜ fun k ↦ ‖⟪a k, b j⟫_𝕜‖ ^ 2
  calc
    V.sinThetaFrobenius U ^ 2 =
        ∑ j, ‖(V.sinThetaMap U) (b j)‖ ^ 2 := by
          rw [Submodule.sinThetaFrobenius_def]
          exact TauCeti.UnitarilyInvariantSeminorm.sq_frobenius_apply b _
    _ = ∑ j ∈ s, ‖(V.sinThetaMap U) (b j)‖ ^ 2 := by
          exact (Finset.sum_subset (Finset.subset_univ s)
            (by
              intro j _ hj
              rw [hb j]
              simp [hj])).symm
    _ = ∑ j ∈ s, ‖Uᗮ.starProjection (b j)‖ ^ 2 := by
          exact Finset.sum_congr rfl fun j hj ↦ by
            rw [hb j]
            simp [hj]
    _ = ∑ j ∈ s, ∑ k ∈ sᶜ, ‖⟪a k, b j⟫_𝕜‖ ^ 2 :=
          Finset.sum_congr rfl fun j _ ↦ hcoord j

/-- The elementary square-root step in the population-gap estimate. -/
private theorem le_two_mul_div_of_sq_mul_sq_le {x delta c : ℝ} (hd : 0 < delta)
    (hc : 0 ≤ c) (h : delta ^ 2 * x ^ 2 ≤ 4 * c ^ 2) :
    x ≤ 2 * c / delta := by
  rw [le_div_iff₀ hd]
  nlinarith [h, hc, sq_nonneg (x * delta - 2 * c),
    sq_nonneg (x * delta + 2 * c)]

/-! ### The SSP-D16 population-gap estimate -/

/-- **Population-gap Frobenius sin-theta theorem (SSP-D16).**

For the blocks selected from the canonical eigenbases of the symmetric
population operator `A` and perturbed operator `B` by the same index set `s`,
a gap in the population eigenvalues alone yields

`‖sin Θ‖_F ≤ 2 min(√|s| ‖B - A‖, ‖B - A‖_F) / Δ`.

No gap is required in the spectrum of `B`. This is the canonical-eigenbasis
specialization of SSP-D16, not the full arbitrary-ordered-eigenframe statement. -/
theorem sinThetaFrobenius_eigenvectorSpan_le (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (hn : finrank 𝕜 E = n) (s : Finset (Fin n)) {delta : ℝ} (hd : 0 < delta)
    (hgap : ∀ j ∈ s, ∀ k ∉ s,
      delta ≤ |hA.eigenvalues hn j - hA.eigenvalues hn k|) :
    (hB.eigenvectorSpan hn (↑s : Set (Fin n))).sinThetaFrobenius
        (hA.eigenvectorSpan hn (↑s : Set (Fin n))) ≤
      2 * min (Real.sqrt s.card * ‖(B - A).toContinuousLinearMap‖)
        (TauCeti.UnitarilyInvariantSeminorm.frobenius 𝕜 E E (B - A)) / delta := by
  let U := hA.eigenvectorSpan hn (↑s : Set (Fin n))
  let V := hB.eigenvectorSpan hn (↑s : Set (Fin n))
  let F := TauCeti.UnitarilyInvariantSeminorm.frobenius 𝕜 E E (B - A)
  let op := ‖(B - A).toContinuousLinearMap‖
  have hsq : V.sinThetaFrobenius U ^ 2 =
      ∑ j ∈ s, ∑ k ∈ sᶜ,
        ‖⟪hA.eigenvectorBasis hn k, hB.eigenvectorBasis hn j⟫_𝕜‖ ^ 2 :=
    hA.sq_sinThetaFrobenius_eigenvectorSpan hB hn s
  have hfrobsq : delta ^ 2 * (V.sinThetaFrobenius U) ^ 2 ≤ 4 * F ^ 2 := by
    rw [hsq]
    exact hA.sq_mul_sum_sum_norm_inner_sq_le_four_mul_frobenius_sq hB hn hd.le hgap
  have hopsq : delta ^ 2 * (V.sinThetaFrobenius U) ^ 2 ≤
      4 * (Real.sqrt s.card * op) ^ 2 := by
    rw [hsq]
    have hε : ∀ x : E, ‖(B - A) x‖ ≤ op * ‖x‖ := by
      intro x
      have hx := (B - A).toContinuousLinearMap.le_opNorm x
      simpa only [LinearMap.coe_toContinuousLinearMap'] using hx
    have h := hA.sq_mul_sum_sum_norm_inner_sq_le_four_mul_card_mul_sq
      hB hn hd.le hgap hε
    convert h using 1
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg s.card)]
    ring
  have hfrob : V.sinThetaFrobenius U ≤ 2 * F / delta :=
    le_two_mul_div_of_sq_mul_sq_le hd
      (apply_nonneg (TauCeti.UnitarilyInvariantSeminorm.frobenius 𝕜 E E) _) hfrobsq
  have hop : V.sinThetaFrobenius U ≤
      2 * (Real.sqrt s.card * op) / delta :=
    le_two_mul_div_of_sq_mul_sq_le hd (by positivity) hopsq
  rcases le_total (Real.sqrt s.card * op) F with h | h
  · rw [min_eq_left h]
    exact hop
  · rw [min_eq_right h]
    exact hfrob

end LinearMap.IsSymmetric
