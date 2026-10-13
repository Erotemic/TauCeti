/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import TauCeti.Analysis.InnerProductSpace.Sylvester.Bound

/-! # The bounded Sylvester operator

The map `X ↦ A ∘L X - X ∘L B` is linear and continuous in `X` on
normed spaces over any nontrivially normed field. The bundled map permits
injectivity, lower-bound, and invertibility statements for Sylvester equations.

Source: `AIQ-Kitware/aiq-dkps-formalization`,
`ForTauCeti/Analysis/InnerProductSpace/Sylvester/Operator.lean` (Apache-2.0).
-/

public section


/-! The Sylvester operator is a statement about composition, so it is declared
over normed spaces rather than inner product spaces: nothing here, and nothing
proved about it downstream, uses an inner product.  Consumers that do work in a
Hilbert space are unaffected, since `InnerProductSpace.toNormedSpace` supplies
the instance. -/

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]

namespace ContinuousLinearMap

/-- The Sylvester operator `X ↦ A X - X B`. -/
def sylvesterOperator (A : F →L[𝕜] F) (B : E →L[𝕜] E)
    (X : E →L[𝕜] F) : E →L[𝕜] F :=
  A ∘L X - X ∘L B

private theorem sylvesterOperator_apply_aux (A : F →L[𝕜] F) (B : E →L[𝕜] E)
    (X : E →L[𝕜] F) : sylvesterOperator A B X = A ∘L X - X ∘L B := rfl

/-- Formula for the unbundled Sylvester operator. -/
@[simp]
theorem sylvesterOperator_apply (A : F →L[𝕜] F) (B : E →L[𝕜] E)
    (X : E →L[𝕜] F) : sylvesterOperator A B X = A ∘L X - X ∘L B :=
  sylvesterOperator_apply_aux A B X

/-- The Sylvester operator `X ↦ A X - X B`, bundled as a continuous linear map.

`sylvesterOperator` is its underlying function.  The bundled form is what lets
the Sylvester operator be *called* injective, bounded below, or invertible:
those are statements about an operator, not about a family of values.  It is a
difference of the two one-sided composition maps, each of which is continuous
and linear in `X`. -/
noncomputable def sylvesterOperatorL (A : F →L[𝕜] F) (B : E →L[𝕜] E) :
    (E →L[𝕜] F) →L[𝕜] (E →L[𝕜] F) :=
  compL 𝕜 E F F A - (compL 𝕜 E E F).flip B

/-- Applying the bundled Sylvester operator is applying the formula. -/
@[simp]
theorem sylvesterOperatorL_apply (A : F →L[𝕜] F) (B : E →L[𝕜] E) (X : E →L[𝕜] F) :
    sylvesterOperatorL A B X = A ∘L X - X ∘L B :=
  (rfl)

/-- The bundled and unbundled Sylvester operators agree extensionally. -/
theorem coe_sylvesterOperatorL (A : F →L[𝕜] F) (B : E →L[𝕜] E) :
    ⇑(sylvesterOperatorL A B) = sylvesterOperator A B := by
  funext X
  exact (sylvesterOperatorL_apply A B X).trans (sylvesterOperator_apply A B X).symm

/-- The Sylvester operator sends `0` to `0`. -/
@[simp] theorem sylvesterOperator_zero
    (A : F →L[𝕜] F) (B : E →L[𝕜] E) :
    sylvesterOperator A B (0 : E →L[𝕜] F) = 0 := by
  simp [sylvesterOperator]

/-- The Sylvester operator is additive. -/
theorem sylvesterOperator_add
    (A : F →L[𝕜] F) (B : E →L[𝕜] E) (X Y : E →L[𝕜] F) :
    sylvesterOperator A B (X + Y) =
      sylvesterOperator A B X + sylvesterOperator A B Y := by
  simp only [sylvesterOperator, ContinuousLinearMap.comp_add,
    ContinuousLinearMap.add_comp]
  abel

/-- The Sylvester operator commutes with subtraction. -/
theorem sylvesterOperator_sub
    (A : F →L[𝕜] F) (B : E →L[𝕜] E) (X Y : E →L[𝕜] F) :
    sylvesterOperator A B (X - Y) =
      sylvesterOperator A B X - sylvesterOperator A B Y := by
  simp only [sylvesterOperator, ContinuousLinearMap.comp_sub,
    ContinuousLinearMap.sub_comp]
  abel

/-- The Sylvester operator is homogeneous. -/
theorem sylvesterOperator_smul
    (A : F →L[𝕜] F) (B : E →L[𝕜] E) (c : 𝕜) (X : E →L[𝕜] F) :
    sylvesterOperator A B (c • X) = c • sylvesterOperator A B X := by
  ext x
  simp [sylvesterOperator, smul_sub]

/-- Elementary operator-norm bound. -/
theorem norm_sylvesterOperator_le
    (A : F →L[𝕜] F) (B : E →L[𝕜] E) (X : E →L[𝕜] F) :
    ‖sylvesterOperator A B X‖ ≤ (‖A‖ + ‖B‖) * ‖X‖ := by
  calc
    ‖sylvesterOperator A B X‖ ≤ ‖A ∘L X‖ + ‖X ∘L B‖ := norm_sub_le _ _
    _ ≤ ‖A‖ * ‖X‖ + ‖X‖ * ‖B‖ :=
      add_le_add (ContinuousLinearMap.opNorm_comp_le A X)
        (ContinuousLinearMap.opNorm_comp_le X B)
    _ = (‖A‖ + ‖B‖) * ‖X‖ := by ring

end ContinuousLinearMap
