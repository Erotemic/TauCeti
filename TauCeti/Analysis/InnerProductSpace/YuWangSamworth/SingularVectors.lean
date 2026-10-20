/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5, GPT-6
-/
module

public import TauCeti.Analysis.InnerProductSpace.Adjoint
public import TauCeti.Analysis.InnerProductSpace.YuWangSamworth

/-!
# Population-gap bounds for right singular vectors

The population-gap overlap estimate for the eigenvectors of two Gram operators
is a direct consequence of the symmetric Yu--Wang--Samworth theorem and a
pointwise perturbation estimate for Gram operators.

The separation is imposed only on the squared singular values of the population
operator. No gap is required for the perturbed operator, and the trial index
block need not be contiguous.

This file proves the right-singular-vector half of SSP-D19. The corresponding
left-singular-vector statement is a separate target, not claimed here.

## Provenance

Adapted from the maintained AIQ-Kitware DKPS formalization (Apache-2.0):
* `ForTauCeti/Analysis/InnerProductSpace/Singular/Subspace.lean`
  (pointwise Gram perturbation proof, Jon Crall and Claude Opus 5).
* `YuWangSamworth2015/YuWangSamworth2015/Core/SingularSubspace.lean`
  (singular-vector population bound, Jon Crall and GPT-5.6 High).

## References

Y. Yu, T. Wang and R. J. Samworth, *A useful variant of the Davis--Kahan
theorem for statisticians*, Biometrika 102 (2015), 315--323.
-/

public section

namespace TauCeti

open LinearMap
open Module (finrank)
open scoped InnerProductSpace BigOperators

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- A pointwise bound for the difference of the right Gram operators. Unlike
an operator-norm statement, this takes a nonnegative perturbation bound and
pointwise bounds on the two rectangular operators. -/
theorem norm_gram_sub_gram_apply_le {A Â : E →ₗ[𝕜] F} {a â ε : ℝ}
    (hâ : 0 ≤ â) (hε : 0 ≤ ε)
    (hA : ∀ x, ‖A x‖ ≤ a * ‖x‖) (hÂ : ∀ x, ‖Â x‖ ≤ â * ‖x‖)
    (hE : ∀ x, ‖(Â - A) x‖ ≤ ε * ‖x‖) (x : E) :
    ‖(Â.adjoint ∘ₗ Â - A.adjoint ∘ₗ A) x‖ ≤ (a + â) * ε * ‖x‖ := by
  have hadj : (Â - A).adjoint = Â.adjoint - A.adjoint := map_sub _ _ _
  have hsplit : (Â.adjoint ∘ₗ Â - A.adjoint ∘ₗ A) x
      = Â.adjoint ((Â - A) x) + (Â - A).adjoint (A x) := by
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, map_sub, hadj]
    abel
  rw [hsplit]
  calc ‖Â.adjoint ((Â - A) x) + (Â - A).adjoint (A x)‖
      ≤ ‖Â.adjoint ((Â - A) x)‖ + ‖(Â - A).adjoint (A x)‖ := norm_add_le _ _
    _ ≤ â * ‖(Â - A) x‖ + ε * ‖A x‖ := by
        gcongr
        · exact LinearMap.norm_adjoint_apply_le hâ hÂ _
        · exact LinearMap.norm_adjoint_apply_le hε hE _
    _ ≤ â * (ε * ‖x‖) + ε * (a * ‖x‖) := by
        gcongr
        · exact hE x
        · exact hA x
    _ = (a + â) * ε * ‖x‖ := by ring

/-- **SSP-D19 (right singular vectors).** A population gap in squared
singular values controls the overlap of the right singular eigenframes
under rectangular perturbations. No gap in the perturbed Gram spectrum is
required. -/
theorem sq_gap_mul_sum_cross_singularVectors_le
    {A Â : E →ₗ[𝕜] F} {Γ a â ε : ℝ} (hΓ : 0 ≤ Γ) (hâ : 0 ≤ â) (hε : 0 ≤ ε)
    (hA : ∀ x, ‖A x‖ ≤ a * ‖x‖) (hÂ : ∀ x, ‖Â x‖ ≤ â * ‖x‖)
    (hE : ∀ x, ‖(Â - A) x‖ ≤ ε * ‖x‖)
    {n : ℕ} (hn : finrank 𝕜 E = n) (s : Finset (Fin n))
    (hgap : ∀ j ∈ s, ∀ k ∉ s,
      Γ ≤ |A.isSymmetric_adjoint_comp_self.eigenvalues hn j
            - A.isSymmetric_adjoint_comp_self.eigenvalues hn k|) :
    Γ ^ 2 * ∑ j ∈ s, ∑ k ∈ sᶜ,
        ‖⟪A.isSymmetric_adjoint_comp_self.eigenvectorBasis hn k,
            Â.isSymmetric_adjoint_comp_self.eigenvectorBasis hn j⟫_𝕜‖ ^ 2
      ≤ 4 * s.card * ((a + â) * ε) ^ 2 :=
  A.isSymmetric_adjoint_comp_self.sq_mul_sum_sum_norm_inner_sq_le_four_mul_card_mul_sq
    Â.isSymmetric_adjoint_comp_self hn hΓ hgap
    (fun x => norm_gram_sub_gram_apply_le hâ hε hA hÂ hE x)

end TauCeti
