/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Absolute sine identities

The absolute value of sine is periodic with period `π` and is invariant under reflection
of its argument. These identities are used when reducing sine Laplace integrals to one period.
-/

public section

namespace Real


/-- Shifting by an integer multiple of `π` preserves the absolute sine. -/
theorem abs_sin_add_nat_mul_pi (s : ℝ) (n : ℕ) :
    |Real.sin (s + n * Real.pi)| = |Real.sin s| := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hstep : s + ((n + 1 : ℕ) : ℝ) * Real.pi =
          (s + (n : ℝ) * Real.pi) + Real.pi := by
        push_cast
        ring
      rw [hstep, Real.sin_add_pi, abs_neg, ih]

/-- The absolute sine is invariant under absolute value of the argument. -/
theorem abs_sin_abs (t : ℝ) : |Real.sin (|t|)| = |Real.sin t| := by
  rcases abs_cases t with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]
  · rw [h, Real.sin_neg, abs_neg]

end Real
