/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 4.8
-/
module

public import TauCeti.Analysis.InnerProductSpace.PiL2

/-!
# Entrywise control of the Euclidean action of a matrix

For a square matrix over a real or complex scalar field, an upper bound on the norm of
every matrix entry gives a bound on the Euclidean norm of its action. For an `n` by `n`
matrix with all entry norms at most `epsilon`, the result is
`norm (A x) <= n * epsilon * norm x`. The statement includes the empty-matrix case.

## Main result

* `TauCeti.norm_toEuclideanLin_le_of_entry_le`: entrywise bounds control the action of
  `Matrix.toEuclideanLin` in Euclidean norm.

## Source

Ported from `ForTauCeti/Analysis/Matrix/EntrywiseOpNorm.lean` in the
[AIQ-Kitware DKPS formalization](https://github.com/AIQ-Kitware/aiq-dkps-formalization)
(Kitware, Inc.; Apache-2.0). The proof is unchanged.
-/

public section

namespace TauCeti

open scoped BigOperators
open Matrix

/-- An entrywise scalar-norm bound gives a Euclidean operator bound, over `RCLike`. -/
theorem norm_toEuclideanLin_le_of_entry_le {𝕜 : Type*} [RCLike 𝕜]
    {n : ℕ} {A : Matrix (Fin n) (Fin n) 𝕜}
    {ε : ℝ} (hentry : ∀ i j, ‖A i j‖ ≤ ε)
    (x : EuclideanSpace 𝕜 (Fin n)) :
    ‖Matrix.toEuclideanLin A x‖ ≤ (n : ℝ) * ε * ‖x‖ := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hzero : Matrix.toEuclideanLin A x = 0 := Subsingleton.elim _ _
    rw [hzero, norm_zero]
    simp
  · have heps : 0 ≤ ε := (norm_nonneg _).trans (hentry ⟨0, hn⟩ ⟨0, hn⟩)
    have hrow : ∀ i : Fin n,
        ‖(Matrix.toEuclideanLin A x) i‖ ≤ ε * (Real.sqrt n * ‖x‖) := by
      intro i
      have happ : (Matrix.toEuclideanLin A x) i = ∑ j : Fin n, A i j * x j := by
        change (A.mulVec (WithLp.ofLp x)) i = _
        simp [Matrix.mulVec, dotProduct]
      calc
        ‖(Matrix.toEuclideanLin A x) i‖ = ‖∑ j : Fin n, A i j * x j‖ := by rw [happ]
        _ ≤ ∑ j : Fin n, ‖A i j * x j‖ := norm_sum_le _ _
        _ = ∑ j : Fin n, ‖A i j‖ * ‖x j‖ := by simp only [norm_mul]
        _ ≤ ∑ j : Fin n, ε * ‖x j‖ :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hentry i j) (norm_nonneg _)
        _ = ε * ∑ j : Fin n, ‖x j‖ := by rw [Finset.mul_sum]
        _ ≤ ε * (Real.sqrt n * ‖x‖) := by
          exact mul_le_mul_of_nonneg_left
            (by simpa using sum_norm_le_sqrt_card_mul_norm x) heps
    have hnorm_sq : ‖Matrix.toEuclideanLin A x‖ ^ 2
        ≤ (n : ℝ) * (ε * (Real.sqrt n * ‖x‖)) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      calc
        ∑ i : Fin n, ‖(Matrix.toEuclideanLin A x) i‖ ^ 2
            ≤ ∑ _i : Fin n, (ε * (Real.sqrt n * ‖x‖)) ^ 2 := by
          exact Finset.sum_le_sum fun i _ =>
            pow_le_pow_left₀ (norm_nonneg _) (hrow i) 2
        _ = (n : ℝ) * (ε * (Real.sqrt n * ‖x‖)) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hs : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) := Real.sq_sqrt (by positivity)
    have hsq_eq : ((n : ℝ) * ε * ‖x‖) ^ 2 =
        (n : ℝ) * (ε * (Real.sqrt n * ‖x‖)) ^ 2 := by
      simp only [mul_pow, hs]
      ring
    have hle : ‖Matrix.toEuclideanLin A x‖ ^ 2
        ≤ ((n : ℝ) * ε * ‖x‖) ^ 2 := by
      rw [hsq_eq]
      exact hnorm_sq
    exact (abs_le_of_sq_le_sq' hle (by positivity)).2

end TauCeti
