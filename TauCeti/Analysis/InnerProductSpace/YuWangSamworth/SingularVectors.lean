/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5, GPT-6
-/
module

public import TauCeti.Analysis.InnerProductSpace.Gram.Perturbation
public import TauCeti.Analysis.InnerProductSpace.YuWangSamworth

/-!
# Population-gap bounds for right singular vectors

For rectangular maps `A` and `Â`, pointwise bounds with constants `a`, `â`, and `ε` on
`A`, `Â`, and `Â - A` give a pointwise Gram perturbation bound with constant `(a + â) * ε`.
Combining this with the symmetric Yu--Wang--Samworth theorem bounds the squared
cross-block overlap of the right singular eigenframes by
`4 * s.card * ((a + â) * ε) ^ 2 / Γ ^ 2` when the population gap `Γ` is positive.
The theorem is stated in multiplied form, which also covers `Γ = 0`.

The separation is imposed only on the squared singular values of the population
operator. No gap is required for the perturbed operator, and the trial index
block need not be contiguous. The proof uses the continuous Gram operator-norm
estimate and converts its pointwise consequence back to algebraic linear maps.

## Provenance

Adapted from the maintained
[AIQ-Kitware DKPS formalization](https://github.com/AIQ-Kitware/aiq-dkps-formalization)
(Apache-2.0):

* `ForTauCeti/Analysis/InnerProductSpace/Singular/Subspace.lean`
  (original Gram perturbation reduction, Jon Crall and Claude Opus 4.8).
* `YuWangSamworth2015/YuWangSamworth2015/Core/SingularSubspace.lean`
  (singular-vector population bound, Jon Crall and GPT 5.6 High).

## References

* Y. Yu, T. Wang and R. J. Samworth, *A useful variant of the Davis--Kahan
  theorem for statisticians*, Biometrika **102** (2015), 315--323.
-/

public section

namespace LinearMap

open Module (finrank)
open scoped InnerProductSpace BigOperators

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- **Yu–Wang–Samworth bound for right singular vectors.** A population gap in squared
singular values gives
`Γ² ∑_{j ∈ s} ∑_{k ∉ s} |⟪v_k, v̂_j⟫|² ≤ 4 |s| ((a + â) ε)²`,
where `v_k` and `v̂_j` are eigenvectors of `A† A` and `Â† Â`. Only the population
spectrum needs a gap. -/
theorem sq_mul_sum_sum_norm_inner_eigenvectorBasis_adjoint_comp_self_sq_le_four_mul_card_mul_sq
    (A Â : E →ₗ[𝕜] F) {Γ a â ε : ℝ} (hΓ : 0 ≤ Γ) (hâ : 0 ≤ â) (hε : 0 ≤ ε)
    (hA : ∀ x, ‖A x‖ ≤ a * ‖x‖) (hÂ : ∀ x, ‖Â x‖ ≤ â * ‖x‖)
    (hE : ∀ x, ‖(Â - A) x‖ ≤ ε * ‖x‖)
    {n : ℕ} (hn : finrank 𝕜 E = n) (s : Finset (Fin n))
    (hgap : ∀ j ∈ s, ∀ k ∉ s,
      Γ ≤ |A.isSymmetric_adjoint_comp_self.eigenvalues hn j
            - A.isSymmetric_adjoint_comp_self.eigenvalues hn k|) :
    Γ ^ 2 * ∑ j ∈ s, ∑ k ∈ sᶜ,
        ‖⟪A.isSymmetric_adjoint_comp_self.eigenvectorBasis hn k,
            Â.isSymmetric_adjoint_comp_self.eigenvectorBasis hn j⟫_𝕜‖ ^ 2
      ≤ 4 * s.card * ((a + â) * ε) ^ 2 := by
  refine A.isSymmetric_adjoint_comp_self.sq_mul_sum_sum_norm_inner_sq_le_four_mul_card_mul_sq
    Â.isSymmetric_adjoint_comp_self hn hΓ hgap ?_
  intro x
  by_cases hx : x = 0
  · simp [hx]
  have ha : 0 ≤ a :=
    nonneg_of_mul_nonneg_left ((norm_nonneg (A x)).trans (hA x)) (norm_pos_iff.mpr hx)
  have := FiniteDimensional.complete 𝕜 E
  have := FiniteDimensional.complete 𝕜 F
  have hAop : ‖A.toContinuousLinearMap‖ ≤ a :=
    A.toContinuousLinearMap.opNorm_le_bound ha hA
  have hÂop : ‖Â.toContinuousLinearMap‖ ≤ â :=
    Â.toContinuousLinearMap.opNorm_le_bound hâ hÂ
  have hEop : ‖Â.toContinuousLinearMap - A.toContinuousLinearMap‖ ≤ ε :=
    (Â.toContinuousLinearMap - A.toContinuousLinearMap).opNorm_le_bound hε hE
  have hGram :
      ‖Â.toContinuousLinearMap.adjoint ∘L Â.toContinuousLinearMap -
        A.toContinuousLinearMap.adjoint ∘L A.toContinuousLinearMap‖ ≤ (a + â) * ε := by
    refine (ContinuousLinearMap.norm_adjoint_comp_self_sub_adjoint_comp_self_le
      Â.toContinuousLinearMap A.toContinuousLinearMap).trans ?_
    calc
      _ ≤ (â + a) * ε :=
        mul_le_mul (add_le_add hÂop hAop) hEop (norm_nonneg _) (add_nonneg hâ ha)
      _ = (a + â) * ε := by rw [add_comm â a]
  simpa only [_root_.sub_apply, ContinuousLinearMap.comp_apply,
    ← adjoint_toContinuousLinearMap, coe_toContinuousLinearMap',
    LinearMap.sub_apply, LinearMap.comp_apply] using
    (ContinuousLinearMap.le_of_opNorm_le _ hGram x)

end LinearMap
