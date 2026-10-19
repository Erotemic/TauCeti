/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Reassembling lower bounds from norm-splitting blocks

A family of bounded operators may split squared vector norms even when the
operators are not spectral projections. If a lower bound holds after applying
all the blocks to a pair of vectors, it also holds for the original vectors.

The result uses extended nonnegative norms, so neither summability nor finiteness
of the index type needs to be assumed.

Adapted from the Kitware DKPS formalization,
`ForTauCeti/Analysis/InnerProductSpace/BlockLowerBound.lean`.
-/

public section

open scoped ENNReal

namespace TauCeti

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A lower bound holding on every member of a squared-norm-splitting family of
bounded operators also holds for the original pair of vectors. -/
theorem enorm_ge_of_blocks {c : ℝ≥0∞} {ι : Type*}
    (blocks : ι → (H →L[ℂ] H))
    (hsplit : ∀ f : H, ∑' i, ‖blocks i f‖ₑ ^ 2 = ‖f‖ₑ ^ 2)
    {x y : H} (hblock : ∀ i, c * ‖blocks i x‖ₑ ≤ ‖blocks i y‖ₑ) :
    c * ‖x‖ₑ ≤ ‖y‖ₑ := by
  have hsq : (c * ‖x‖ₑ) ^ 2 ≤ ‖y‖ₑ ^ 2 := by
    calc
      (c * ‖x‖ₑ) ^ 2 = c ^ 2 * ∑' i, ‖blocks i x‖ₑ ^ 2 := by
        rw [mul_pow, hsplit]
      _ = ∑' i, (c * ‖blocks i x‖ₑ) ^ 2 := by
        simp_rw [mul_pow]
        exact (ENNReal.tsum_mul_left).symm
      _ ≤ ∑' i, ‖blocks i y‖ₑ ^ 2 :=
        ENNReal.tsum_le_tsum fun i => by gcongr; exact hblock i
      _ = ‖y‖ₑ ^ 2 := hsplit _
  by_contra hcon
  push Not at hcon
  exact absurd ((ENNReal.pow_lt_pow_left_iff (n := 2) two_ne_zero).mpr hcon)
    (not_lt.mpr hsq)

end TauCeti
