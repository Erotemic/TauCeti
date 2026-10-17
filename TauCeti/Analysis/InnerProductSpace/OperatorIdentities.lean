/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5, qwen3.8-27b-dbirks-hyperqwen-huge
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Tactic.Ring

/-!
# Diagonal and absorption identities for continuous linear operators

This module collects operator identities independent of projection-valued measures.

* `ContinuousLinearMap.eq_of_diagonal` uses complex polarization to identify operators from
  their diagonal inner products.
* `ContinuousLinearMap.norm_sub_sq_of_selfAdjoint_idempotent_absorption` computes the squared
  distance between `S x` and `T x` when `S` is a self-adjoint idempotent absorbed by `T`.

These proofs were extracted from the DKPS projection-valued-measure port. Self-adjointness
identities already available as `IsSelfAdjoint.isSymmetric` are used directly.
-/

public section

open scoped InnerProduct InnerProductSpace

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Complex polarization: equality of all diagonal inner products determines a continuous
linear operator. This specializes Mathlib's `ext_inner_map` to continuous linear maps. -/
theorem eq_of_diagonal (S T : H →L[ℂ] H)
    (h : ∀ x : H, ⟪x, S x⟫_ℂ = ⟪x, T x⟫_ℂ) : S = T := by
  refine ContinuousLinearMap.coe_injective ((ext_inner_map _ _).mp fun x => ?_)
  -- `ext_inner_map` compares linear maps; applying a continuous linear map is the same.
  change ⟪S x, x⟫_ℂ = ⟪T x, x⟫_ℂ
  rw [← inner_conj_symm (S x) x, ← inner_conj_symm (T x) x, h x]

variable [CompleteSpace H]

/-- If `S` is self-adjoint, idempotent, and satisfies `S * T = S`, then the
squared norm of `(S - T) x` is the difference of the squared norms. The operator
`T` need not be self-adjoint. -/
theorem norm_sub_sq_of_selfAdjoint_idempotent_absorption
    (S T : H →L[ℂ] H) (hS : IsSelfAdjoint S)
    (hSS : S * S = S) (hST : S * T = S) (x : H) :
    ‖S x - T x‖ ^ 2 = ‖T x‖ ^ 2 - ‖S x‖ ^ 2 := by
  have hcross : ⟪S x, T x⟫_ℂ = ⟪S x, S x⟫_ℂ := by
    calc
      ⟪S x, T x⟫_ℂ = ⟪x, S (T x)⟫_ℂ := hS.isSymmetric x (T x)
      _ = ⟪x, S x⟫_ℂ := by rw [← mul_apply_eq_comp, hST]
      _ = ⟪x, S (S x)⟫_ℂ := by rw [← mul_apply_eq_comp, hSS]
      _ = ⟪S x, S x⟫_ℂ := (hS.isSymmetric x (S x)).symm
  rw [norm_sub_sq (𝕜 := ℂ), hcross, ← norm_sq_eq_re_inner (𝕜 := ℂ)]
  ring

end ContinuousLinearMap
