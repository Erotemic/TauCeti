/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import TauCeti.Analysis.InnerProductSpace.Orthonormal.Overlap
public import TauCeti.Analysis.InnerProductSpace.Spectrum
public import TauCeti.Analysis.InnerProductSpace.YuWangSamworth.Basic

/-!
# Population-gap Frobenius sin-theta bound

The Yu--Wang--Samworth population-gap residual estimate bounds the squared
cross-block overlap of the ordered eigenbases of two symmetric operators.
The orthonormal-basis overlap formula identifies this with the squared
Frobenius sine of the corresponding selected subspaces.

Only the eigenvalues of the population operator are assumed separated. No spectral
gap is imposed on the perturbed operator. Both subspaces are selected from the
canonical ordered eigenbases at the same indices.

## Main result

* `LinearMap.IsSymmetric.sinThetaFrobenius_eigenvectorSpan_le`: a population-gap
  estimate with the minimum of the rank-scaled operator norm and Frobenius norm
  of the perturbation.

## References

* Y. Yu, T. Wang, and R. J. Samworth, *A useful variant of the Davis--Kahan
  theorem for statisticians*, Biometrika 102 (2015), 315--323.
* AIQ-Kitware DKPS formalization, `YuWangSamworth2015/Core/Statistics.lean`
  (Kitware, Inc.; Apache-2.0).
-/

public section

open Module (finrank)
open scoped InnerProductSpace

namespace LinearMap.IsSymmetric

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {A B : E →ₗ[𝕜] E} {n : ℕ}

/-! ### The eigenbasis overlap identity -/

/-- For the canonical eigenblocks selected by `s`, the squared Frobenius sine equals
the sum of squared overlaps between the perturbed block and the complementary
population block. -/
theorem sq_sinThetaFrobenius_eigenvectorSpan (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (hn : finrank 𝕜 E = n) (s : Finset (Fin n)) :
    (hB.eigenvectorSpan hn (↑s : Set (Fin n))).sinThetaFrobenius
      (hA.eigenvectorSpan hn (↑s : Set (Fin n))) ^ 2 =
      ∑ j ∈ s, ∑ k ∈ sᶜ,
        ‖⟪hA.eigenvectorBasis hn k, hB.eigenvectorBasis hn j⟫_𝕜‖ ^ 2 := by
  rw [hA.eigenvectorSpan_eq_spanIndices, hB.eigenvectorSpan_eq_spanIndices]
  exact (hA.eigenvectorBasis hn).sq_sinThetaFrobenius_spanIndices
    (hB.eigenvectorBasis hn) s

/-! ### The population-gap estimate -/

/-- **Population-gap Frobenius sin-theta theorem.**
For the subspaces selected by the same indices in the canonical eigenbases of
symmetric operators `A` (population) and `B` (perturbed), a gap in the population
eigenvalues alone gives

`norm(sin Theta)_F <= 2 * min(sqrt(card s) * norm(B - A), norm(B - A)_F) / delta`.

No gap is required in the spectrum of `B`. The bases used are `eigenvectorBasis`;
other orthonormal eigenframes of `B` within repeated eigenspaces are not included. -/
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
    have hE : ∀ x : E, ‖(B - A) x‖ ≤ op * ‖x‖ := by
      intro x
      have hx := (B - A).toContinuousLinearMap.le_opNorm x
      simpa only [LinearMap.coe_toContinuousLinearMap'] using hx
    have h := hA.sq_mul_sum_sum_norm_inner_sq_le_four_mul_card_mul_sq
      hB hn hd.le hgap hE
    convert h using 1
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg s.card)]
    ring
  have hfrob : V.sinThetaFrobenius U ≤ 2 * F / delta := by
    rw [le_div_iff₀ hd]
    have hF : 0 ≤ F :=
      apply_nonneg (TauCeti.UnitarilyInvariantSeminorm.frobenius 𝕜 E E) _
    refine le_of_sq_le_sq ?_ (mul_nonneg (by norm_num) hF)
    calc
      (V.sinThetaFrobenius U * delta) ^ 2 =
          delta ^ 2 * (V.sinThetaFrobenius U) ^ 2 := by ring
      _ ≤ 4 * F ^ 2 := hfrobsq
      _ = (2 * F) ^ 2 := by ring
  have hop : V.sinThetaFrobenius U ≤ 2 * (Real.sqrt s.card * op) / delta := by
    rw [le_div_iff₀ hd]
    have hC : 0 ≤ Real.sqrt s.card * op := by positivity
    refine le_of_sq_le_sq ?_ (mul_nonneg (by norm_num) hC)
    calc
      (V.sinThetaFrobenius U * delta) ^ 2 =
          delta ^ 2 * (V.sinThetaFrobenius U) ^ 2 := by ring
      _ ≤ 4 * (Real.sqrt s.card * op) ^ 2 := hopsq
      _ = (2 * (Real.sqrt s.card * op)) ^ 2 := by ring
  rcases le_total (Real.sqrt s.card * op) F with h | h
  · rw [min_eq_left h]
    exact hop
  · rw [min_eq_right h]
    exact hfrob

end LinearMap.IsSymmetric
