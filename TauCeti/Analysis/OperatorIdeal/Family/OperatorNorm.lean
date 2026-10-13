/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5, OpenAI GPT-5.6 Thinking
-/
module

public import TauCeti.Analysis.OperatorIdeal.Family.Basic
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Norm

/-!
# Operator norm ideal families

The operator norm defines an operator ideal containing all bounded maps and a
symmetric family on Hilbert spaces. The ideal-element norm agrees with the
ordinary operator norm; completeness transfers from the bounded operators.

The general two-sided composition bound is in
`TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Norm`.

Adapted from the Apache-2.0 DKPS formalization (Kitware, Inc.).
-/

public section

open scoped ENNReal

universe u v w


namespace TauCeti

section Base

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} {F : Type w}
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The operator norm, as an operator ideal family: every bounded operator is a
member, and the gauge is the operator norm. -/
noncomputable def operatorNormIdealFamily (𝕜 : Type u) [RCLike 𝕜] :
    OperatorIdealFamily.{u, v, w} 𝕜 where
  gauge A := ‖A‖ₑ
  gauge_add_le A B := by
    simpa [enorm_eq_nnnorm, ← ENNReal.coe_add] using nnnorm_add_le A B
  gauge_smul c A := by
    simp [enorm_eq_nnnorm, nnnorm_smul]
  enorm_le_gauge _ := le_rfl
  gauge_comp_le L A R := by
    have h : ‖L ∘L A ∘L R‖ ≤ ‖L‖ * ‖A‖ * ‖R‖ :=
      ContinuousLinearMap.opNorm_comp_comp_le L A R
    calc ‖L ∘L A ∘L R‖ₑ ≤ ‖(‖L‖ * ‖A‖ * ‖R‖ : ℝ)‖ₑ := by
          rw [← ofReal_norm, ← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (h.trans (le_abs_self _))
      _ = ‖L‖ₑ * ‖A‖ₑ * ‖R‖ₑ := by
          rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ofReal_norm]
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity),
            ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (norm_nonneg _)]

/-- The operator-norm ideal gauge agrees with the extended operator norm. -/
@[simp]
theorem gauge_operatorNormIdealFamily (A : E →L[𝕜] F) :
    (operatorNormIdealFamily.{u, v, w} 𝕜).gauge A = ‖A‖ₑ := by
  unfold operatorNormIdealFamily
  rfl

/-- Every bounded operator belongs to the operator-norm ideal, because
its norm is finite. -/
@[simp]
theorem carrier_operatorNormIdealFamily :
    (operatorNormIdealFamily.{u, v, w} 𝕜).carrier (E := E) (F := F) = ⊤ := by
  ext A
  simp

/-- The ideal of the operator-norm family is all of `E →L[𝕜] F`, isometrically:
its ideal norm *is* the operator norm. -/
noncomputable def operatorNormIdealFamilyElemEquiv :
    (operatorNormIdealFamily.{u, v, w} 𝕜).Elem E F ≃ₗᵢ[𝕜] (E →L[𝕜] F) where
  toFun A := A.val
  invFun A := OperatorIdealFamily.Elem.mk (N := operatorNormIdealFamily 𝕜) (by simp)
  left_inv _ := OperatorIdealFamily.Elem.ext (OperatorIdealFamily.Elem.val_mk _)
  right_inv _ := OperatorIdealFamily.Elem.val_mk _
  map_add' A B := OperatorIdealFamily.Elem.val_add A B
  map_smul' c A := OperatorIdealFamily.Elem.val_smul c A
  norm_map' A := by
    -- names the application so the norm bound applies to it directly.
    change ‖A.val‖ = ‖A‖
    rw [OperatorIdealFamily.Elem.norm_def, gauge_operatorNormIdealFamily, toReal_enorm]

/-- The operator-norm ideal is complete, transported along the isometry
`operatorNormIdealFamilyElemEquiv` from completeness of `E →L[𝕜] F`. -/
instance instIsCompleteOperatorNormIdealFamily :
    (operatorNormIdealFamily.{u, v, w} 𝕜).IsComplete where
  completeSpace := by
    intro E F _ _ _ _ _
    exact (operatorNormIdealFamilyElemEquiv
      (𝕜 := 𝕜) (E := E) (F := F)).toIsometryEquiv.completeSpace

end Base

section Symmetric

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The operator norm, as a *symmetric* ideal family: the adjoint is an
isometry, so the operator norm is adjoint-invariant. -/
noncomputable def operatorNormFamily (𝕜 : Type u) [RCLike 𝕜] :
    SymmetricOperatorIdealFamily.{u, v} 𝕜 where
  toOperatorIdealFamily := operatorNormIdealFamily 𝕜
  gauge_adjoint A := by
    simp only [gauge_operatorNormIdealFamily, ← ofReal_norm]
    rw [ContinuousLinearMap.adjoint.norm_map]

/-- Completeness transfers to the symmetric view, which shares its underlying
family with `operatorNormIdealFamily`.  The instance has to be restated rather
than inherited: `instIsCompleteOperatorNormIdealFamily` is stated at three
independent universes, and the symmetric family constrains the last two to be
equal, so instance search does not find it without this specialization. -/
instance : (operatorNormFamily.{u, v} 𝕜).toOperatorIdealFamily.IsComplete :=
  inferInstanceAs (operatorNormIdealFamily.{u, v, v} 𝕜).IsComplete

/-- The symmetric operator-norm family has the same gauge as the plain one; the
symmetric structure adds adjoint-invariance, not a different norm. -/
@[simp]
theorem gauge_operatorNormFamily (A : E →L[𝕜] F) :
    (operatorNormFamily.{u, v} 𝕜).gauge A = ‖A‖ₑ := by
  unfold operatorNormFamily
  exact gauge_operatorNormIdealFamily A
end Symmetric

end TauCeti
