/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 High, Claude Fable 5
-/
module

public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Analysis.Convex.FiniteMean

/-!
# Centered scatter operators

For a finite family `z : Fin n → E` in an inner-product space, the canonical
`TauCeti.finiteMean` from `Analysis.Convex.FiniteMean` is its arithmetic mean
(zero for the empty family). The unnormalized centered scatter is

`centeredScatter 𝕜 z = ∑ i, rankOne 𝕜 (z i - finiteMean 𝕜 z) (z i - finiteMean 𝕜 z)`.

The exact add-one identity is

`S(Fin.snoc z y) = S(z) + n/(n+1) • rankOne 𝕜 (y - mean z) (y - mean z)`.

It implies monotonicity in the Löwner order and an explicit update of the
quadratic form. The rank-one summands and their sum are continuous linear maps;
no completeness assumption on `E` is needed.

## Main results

* `TauCeti.centeredScatter_append`: the exact add-one operator identity.
* `TauCeti.re_inner_centeredScatter_self`: the scatter quadratic form.
* `TauCeti.centeredScatter_isPositive` and `TauCeti.centeredScatter_le_append`:
  positivity and monotonicity.
* `TauCeti.re_inner_centeredScatter_append`: the quadratic-form add-one identity.

## Source

Adapted from the Apache-2.0 DKPS formalization
(https://github.com/AIQ-Kitware/aiq-dkps-formalization), originally
`ForMathlib/Analysis/InnerProductSpace/CenteredScatter.lean` at commit `fc38eb4`.
The author and copyright attribution is retained above.
The finite-mean identities are reused from `TauCeti.Analysis.Convex.FiniteMean`.
-/

public section

namespace TauCeti

open Module InnerProductSpace
open scoped BigOperators

variable (𝕜 : Type*) {E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Unnormalized centered scatter operator `∑ i, (zᵢ - mean z) ⊗ (zᵢ - mean z)`.

The rank-one convention is chosen so its quadratic form is
`∑ i, ‖⟪zᵢ - mean z, x⟫‖²`. -/
noncomputable def centeredScatter {n : ℕ} (z : Fin n → E) : E →L[𝕜] E :=
  ∑ i, rankOne 𝕜 (z i - finiteMean 𝕜 z) (z i - finiteMean 𝕜 z)

/-- **Exact add-one centered-scatter identity**:
`S(z ++ [y]) = S(z) + n/(n+1) • ((y - mean z) ⊗ (y - mean z))`. -/
theorem centeredScatter_append {n : ℕ} (z : Fin n → E) (y : E) :
    centeredScatter 𝕜 (Fin.snoc z y) = centeredScatter 𝕜 z +
      ((n : 𝕜) / ((n : 𝕜) + 1)) •
        rankOne 𝕜 (y - finiteMean 𝕜 z) (y - finiteMean 𝕜 z) := by
  have hn1 : (n : 𝕜) + 1 ≠ 0 := by
    have : ((n + 1 : ℕ) : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
    push_cast at this
    exact this
  set m := finiteMean 𝕜 z with hm
  set δ := y - m with hδ
  set c : 𝕜 := ((n : 𝕜) + 1)⁻¹ with hc
  have hconjc : (starRingEnd 𝕜) c = c := by
    simp [hc]
  have hmean' : finiteMean 𝕜 (Fin.snoc z y) = m + c • δ := by
    simpa only [hm, hc, hδ] using (finiteMean_snoc (R := 𝕜) z y)
  have hzero : ∑ i, (z i - m) = 0 := by
    simpa only [hm] using (sum_sub_finiteMean (R := 𝕜) z)
  apply ContinuousLinearMap.ext
  intro x
  have hterm : ∀ a : E,
      inner 𝕜 (a - c • δ) x • (a - c • δ) =
        inner 𝕜 a x • a - inner 𝕜 a x • (c • δ) - (c * inner 𝕜 δ x) • a +
          (c * (c * inner 𝕜 δ x)) • δ := by
    intro a
    rw [inner_sub_left, inner_smul_left, hconjc]
    module
  have hzero' : ∑ i, inner 𝕜 (z i - m) x = 0 := by
    rw [← sum_inner, hzero, inner_zero_left]
  simp only [centeredScatter, sum_apply, add_apply,
    smul_apply, rankOne_apply]
  rw [hmean', Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  have hres : ∀ i : Fin n, z i - (m + c • δ) = (z i - m) - c • δ := fun i => by
    rw [sub_add_eq_sub_sub]
  have hlast : y - (m + c • δ) = δ - c • δ := by
    rw [sub_add_eq_sub_sub, ← hδ]
  calc (∑ i, inner 𝕜 (z i - (m + c • δ)) x • (z i - (m + c • δ))) +
        inner 𝕜 (y - (m + c • δ)) x • (y - (m + c • δ))
      = (∑ i, (inner 𝕜 (z i - m) x • (z i - m) - inner 𝕜 (z i - m) x • (c • δ) -
            (c * inner 𝕜 δ x) • (z i - m) + (c * (c * inner 𝕜 δ x)) • δ)) +
          (inner 𝕜 δ x • δ - inner 𝕜 δ x • (c • δ) - (c * inner 𝕜 δ x) • δ +
            (c * (c * inner 𝕜 δ x)) • δ) := by
        rw [hlast, hterm δ]
        congr 1
        exact Finset.sum_congr rfl fun i _ => by rw [hres i, hterm (z i - m)]
    _ = ((∑ i, inner 𝕜 (z i - m) x • (z i - m)) -
          (∑ i, inner 𝕜 (z i - m) x) • (c • δ) -
          (c * inner 𝕜 δ x) • (∑ i, (z i - m)) + (n : 𝕜) • ((c * (c * inner 𝕜 δ x)) • δ)) +
          (inner 𝕜 δ x • δ - inner 𝕜 δ x • (c • δ) - (c * inner 𝕜 δ x) • δ +
            (c * (c * inner 𝕜 δ x)) • δ) := by
        congr 1
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
          Finset.sum_smul, ← Finset.smul_sum]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          ← Nat.cast_smul_eq_nsmul 𝕜]
    _ = (∑ i, inner 𝕜 (z i - m) x • (z i - m)) +
          ((n : 𝕜) / ((n : 𝕜) + 1)) • (inner 𝕜 δ x • δ) := by
        rw [hzero', hzero, zero_smul, smul_zero, sub_zero, sub_zero]
        match_scalars
        all_goals simp only [hc]
        all_goals field_simp
        all_goals ring

/-- The scatter quadratic form is the sum of squared centered inner products. -/
theorem re_inner_centeredScatter_self {n : ℕ} (z : Fin n → E) (x : E) :
    RCLike.re (inner 𝕜 (centeredScatter 𝕜 z x) x) =
      ∑ i, ‖inner 𝕜 (z i - finiteMean 𝕜 z) x‖ ^ 2 := by
  have h1 : inner 𝕜 (centeredScatter 𝕜 z x) x =
      ((∑ i, ‖inner 𝕜 (z i - finiteMean 𝕜 z) x‖ ^ 2 : ℝ) : 𝕜) := by
    rw [centeredScatter, sum_apply, sum_inner]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [rankOne_apply, inner_smul_left, RCLike.conj_mul]
  rw [h1, RCLike.ofReal_re]

/-- The centered scatter operator is positive. -/
theorem centeredScatter_isPositive {n : ℕ} (z : Fin n → E) :
    (centeredScatter 𝕜 z).IsPositive := by
  constructor
  · intro u v
    simp only [centeredScatter, ContinuousLinearMap.toLinearMap_sum, LinearMap.sum_apply,
      ContinuousLinearMap.coe_coe, sum_inner, inner_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [rankOne_apply, rankOne_apply, inner_smul_left,
      inner_smul_right, inner_conj_symm]
    ring
  · intro u
    rw [ContinuousLinearMap.reApplyInnerSelf_apply, re_inner_centeredScatter_self]
    exact Finset.sum_nonneg fun i _ => sq_nonneg _

/-- Appending a point can only increase the centered scatter in Löwner order. -/
theorem centeredScatter_le_append {n : ℕ} (z : Fin n → E) (y : E) :
    centeredScatter 𝕜 z ≤ centeredScatter 𝕜 (Fin.snoc z y) := by
  rw [ContinuousLinearMap.le_def, centeredScatter_append, add_sub_cancel_left]
  set δ := y - finiteMean 𝕜 z with hδ
  have hcoef : (starRingEnd 𝕜) ((n : 𝕜) / ((n : 𝕜) + 1)) = (n : 𝕜) / ((n : 𝕜) + 1) := by
    simp
  have hre : ∀ u : E, RCLike.re (inner 𝕜
      ((((n : 𝕜) / ((n : 𝕜) + 1)) • rankOne 𝕜 δ δ) u) u) =
      ((n : ℝ) / ((n : ℝ) + 1)) * ‖inner 𝕜 δ u‖ ^ 2 := by
    intro u
    rw [smul_apply, inner_smul_left, hcoef,
      rankOne_apply, inner_smul_left, RCLike.conj_mul]
    have hcast : ((n : 𝕜) / ((n : 𝕜) + 1)) = (((n : ℝ) / ((n : ℝ) + 1) : ℝ) : 𝕜) := by
      push_cast
      rfl
    rw [hcast, ← RCLike.ofReal_pow, ← RCLike.ofReal_mul, RCLike.ofReal_re]
  constructor
  · intro u v
    simp only [FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.coe_coe,
      inner_smul_left, inner_smul_right, hcoef, rankOne_apply]
    rw [inner_conj_symm]
    ring
  · intro u
    rw [ContinuousLinearMap.reApplyInnerSelf_apply, hre u]
    positivity

/-- Quadratic-form version of the add-one identity: adding one point adds the exact
nonnegative correction `n/(n+1) ⟪y - mean z, x⟫²` to the scatter quadratic form. -/
theorem re_inner_centeredScatter_append {n : ℕ} (z : Fin n → E) (y x : E) :
    RCLike.re (inner 𝕜 (centeredScatter 𝕜 (Fin.snoc z y) x) x) =
      RCLike.re (inner 𝕜 (centeredScatter 𝕜 z x) x) +
        (n : ℝ) / ((n : ℝ) + 1) * ‖inner 𝕜 (y - finiteMean 𝕜 z) x‖ ^ 2 := by
  rw [centeredScatter_append, add_apply, inner_add_left, map_add]
  congr 1
  set δ := y - finiteMean 𝕜 z with hδ
  have hcoef : (starRingEnd 𝕜) ((n : 𝕜) / ((n : 𝕜) + 1)) = (n : 𝕜) / ((n : 𝕜) + 1) := by
    simp
  rw [smul_apply, inner_smul_left, hcoef,
    rankOne_apply, inner_smul_left, RCLike.conj_mul]
  have hcast : ((n : 𝕜) / ((n : 𝕜) + 1)) = (((n : ℝ) / ((n : ℝ) + 1) : ℝ) : 𝕜) := by
    push_cast
    rfl
  rw [hcast, ← RCLike.ofReal_pow, ← RCLike.ofReal_mul, RCLike.ofReal_re]

end TauCeti
