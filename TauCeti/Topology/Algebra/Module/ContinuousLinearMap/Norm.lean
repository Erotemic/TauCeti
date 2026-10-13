/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5, OpenAI GPT-5.6 Thinking
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Norm inequalities for continuous linear maps

Two-sided operator-norm composition inequalities for seminormed spaces over a
nontrivially normed field, without inner-product or completeness assumptions.

Adapted from the Apache-2.0 DKPS formalization (Kitware, Inc.).
-/

public section

/-- Operator-norm submultiplicativity for a two-sided composition. -/
theorem ContinuousLinearMap.opNorm_comp_comp_le
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E F G H : Type*}
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
    [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]
    [SeminormedAddCommGroup H] [NormedSpace 𝕜 H]
    (L : F →L[𝕜] G) (A : E →L[𝕜] F) (R : H →L[𝕜] E) :
    ‖L ∘L A ∘L R‖ ≤ ‖L‖ * ‖A‖ * ‖R‖ :=
  calc ‖L ∘L A ∘L R‖ ≤ ‖L‖ * ‖A ∘L R‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖L‖ * (‖A‖ * ‖R‖) :=
        mul_le_mul_of_nonneg_left
          (ContinuousLinearMap.opNorm_comp_le A R) (norm_nonneg L)
    _ = ‖L‖ * ‖A‖ * ‖R‖ := (mul_assoc _ _ _).symm

end
