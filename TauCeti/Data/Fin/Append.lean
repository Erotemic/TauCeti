/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 Thinking, Claude Fable 5, Claude Opus 5, GPT-6
-/
/-
Generalized from the zero-tail evaluation lemma in the DKPS formalization:
https://github.com/AIQ-Kitware/aiq-dkps-formalization (Apache-2.0).
-/
module

public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Evaluating tuples with an appended zero tail

The evaluation formula for `Fin.append x 0` separates the coordinates of
`x` from those in the appended zero tuple. It is valid for any type with a
zero element, independent of ordering or a norm.
-/

public section

namespace Fin

variable {α : Type*} [Zero α] {n m : ℕ}

/-- Appending a zero tuple leaves indices below `n` unchanged and sets all
later coordinates to zero. -/
theorem append_zero_apply (x : Fin n → α) (i : Fin (n + m)) :
    (Fin.append x (0 : Fin m → α)) i =
      if hi : (i : ℕ) < n then x (Fin.castLT i hi) else 0 := by
  dsimp only [Fin.append, Fin.addCases]
  split_ifs with h
  · simp
  · simp

end Fin
