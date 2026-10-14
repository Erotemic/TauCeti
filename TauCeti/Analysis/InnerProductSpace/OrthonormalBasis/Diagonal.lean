/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5, Claude Opus 4.8, Claude Opus 5
-/
module

public import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Diagonal linear operators in finite real orthonormal bases

Given an arbitrary finite orthonormal basis `b` and coefficients `c`, `b.diagonal c`
scales each basis vector `b i` by `c i`. This supplies the reusable diagonal
calculus needed for finite-dimensional spectral constructions, independently
of any near-isometry hypothesis.

The basis-vector action and the coordinate formula are `@[simp]` lemmas. We
also prove composition, subtraction of the identity, symmetry over the reals,
and pointwise norm estimates from coefficient bounds.

For diagonal sums of rank-one maps between possibly different spaces, see
`TauCeti.Analysis.InnerProductSpace.DiagonalSum` instead.

## Provenance

Extracted from `TauCeti.Analysis.InnerProductSpace.NearIsometry`, itself
adapted from the Apache-2.0 Kitware DKPS formalization.
-/

public section

open scoped RealInnerProductSpace InnerProductSpace

namespace OrthonormalBasis

variable {ι E : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The operator that scales the `k`-th vector of an orthonormal basis by `c k`. -/
noncomputable def diagonal (b : OrthonormalBasis ι ℝ E) (c : ι → ℝ) :
    E →ₗ[ℝ] E :=
  b.toBasis.constr ℝ fun j => c j • b j

/-- A diagonal operator scales each orthonormal-basis vector by its coefficient. -/
@[simp] theorem diagonal_basis (b : OrthonormalBasis ι ℝ E) (c : ι → ℝ)
    (k : ι) :
    diagonal b c (b k) = c k • b k := by
  classical
  have := b.toBasis.constr_basis ℝ (fun j => c j • b j) k
  rwa [OrthonormalBasis.coe_toBasis] at this

/-- **Diagonals compose pointwise.**  `diagonal b f ∘ₗ diagonal b g` is the
diagonal of the pointwise product. -/
theorem diagonal_comp_diagonal (b : OrthonormalBasis ι ℝ E)
    (f g : ι → ℝ) :
    diagonal b f ∘ₗ diagonal b g = diagonal b (fun k => f k * g k) := by
  classical
  refine b.toBasis.ext fun k => ?_
  simp only [OrthonormalBasis.coe_toBasis, LinearMap.comp_apply, diagonal_basis, map_smul,
    smul_smul, mul_comm]

/-- **A diagonal minus the identity is diagonal**, with factors `c k - 1`. -/
theorem diagonal_sub_id (b : OrthonormalBasis ι ℝ E) (c : ι → ℝ) :
    diagonal b c - LinearMap.id = diagonal b fun k => c k - 1 := by
  classical
  refine b.toBasis.ext fun k => ?_
  simp only [OrthonormalBasis.coe_toBasis, LinearMap.sub_apply, LinearMap.id_apply,
    diagonal_basis, sub_smul, one_smul]

/-- A diagonal operator acts on basis coordinates by scalar multiplication. -/
@[simp] theorem repr_diagonal (b : OrthonormalBasis ι ℝ E) (c : ι → ℝ) (x : E)
    (k : ι) : b.repr (diagonal b c x) k = c k * b.repr x k := by
  classical
  have hx : diagonal b c x = ∑ j : ι, b.repr x j • (c j • b j) := by
    conv_lhs => rw [← b.sum_repr x, map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_smul, diagonal_basis]
  rw [b.repr_apply_apply, hx, inner_sum, Finset.sum_eq_single k]
  · rw [real_inner_smul_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
      b.orthonormal.norm_eq_one k, b.repr_apply_apply]
    ring
  · intro j _ hjk
    rw [real_inner_smul_right, real_inner_smul_right, b.inner_eq_zero hjk.symm]
    ring
  · intro hk; exact absurd (Finset.mem_univ k) hk

/-- Every real diagonal operator in an orthonormal basis is symmetric. -/
theorem isSymmetric_diagonal (b : OrthonormalBasis ι ℝ E) (c : ι → ℝ) :
    (diagonal b c).IsSymmetric := by
  classical
  have key :
      ∀ u v : E, ⟪diagonal b c u, v⟫_ℝ =
        ∑ k : ι, c k * b.repr u k * b.repr v k := by
    intro u v
    conv_lhs => rw [← b.sum_repr v]
    rw [inner_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [real_inner_smul_right, real_inner_comm, ← b.repr_apply_apply, repr_diagonal]
    ring
  intro x y
  rw [key, real_inner_comm, key]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- A diagonal operator whose scaling factors are bounded by `δ` has operator norm at most
`δ`, by Parseval. -/
theorem norm_diagonal_apply_le (b : OrthonormalBasis ι ℝ E) (c : ι → ℝ)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hc : ∀ k, |c k| ≤ δ) (x : E) :
    ‖diagonal b c x‖ ≤ δ * ‖x‖ := by
  classical
  have hpars : ∀ y : E, ∑ k : ι, b.repr y k ^ 2 = ‖y‖ ^ 2 := by
    intro y
    rw [← b.sum_sq_inner_right y]
    exact Finset.sum_congr rfl fun k _ => by rw [b.repr_apply_apply]
  have hbnd : ‖diagonal b c x‖ ^ 2 ≤ δ ^ 2 * ‖x‖ ^ 2 := by
    rw [← hpars (diagonal b c x), ← hpars x, Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [repr_diagonal, mul_pow]
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    have := hc k
    nlinarith [abs_nonneg (c k), abs_le.mp (hc k), sq_abs (c k)]
  nlinarith [hbnd, norm_nonneg (diagonal b c x), mul_nonneg hδ0 (norm_nonneg x),
    sq_nonneg (‖diagonal b c x‖ - δ * ‖x‖)]

/-- A diagonal operator whose scaling factors are all within `δ` of `1` moves any vector `x` by at most `δ * ‖x‖`.

This is the operator form of the scalar estimate that makes the near-isometry constant sharp:
`diagonal b c - 1` is again diagonal, with factors `c k - 1`. -/
theorem norm_diagonal_apply_sub_self_le (b : OrthonormalBasis ι ℝ E)
    (c : ι → ℝ) {δ : ℝ} (hδ0 : 0 ≤ δ) (hc : ∀ k, |c k - 1| ≤ δ) (x : E) :
    ‖diagonal b c x - x‖ ≤ δ * ‖x‖ := by
  classical
  have hsub := diagonal_sub_id b c
  have hx : diagonal b c x - x = diagonal b (fun k => c k - 1) x := by
    have := congrArg (fun T : E →ₗ[ℝ] E => T x) hsub
    simpa using this
  rw [hx]
  exact norm_diagonal_apply_le b _ hδ0 hc x

end OrthonormalBasis

end
