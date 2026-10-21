/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import TauCeti.Analysis.InnerProductSpace.Projection.PrincipalAngle
import Mathlib.Tactic.Module
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Rectangular double-angle Gram identities

For rectangular linear maps `T : K₁ → K₀` and `C : K₀ → L`, suppose
`C† C = 1 - T T†`. The Gram operator of their composite is
`(CT)†(CT) = M - M²`, where `M = T†T`. Thus doubling the composite gives
`(2 CT)†(2 CT) = 4 (M - M²)`, the squared operator form of
`sin (2θ) = 2 sin θ cos θ`.

The identities use no equality-of-dimensions assumption. They also apply to
complementary isometric coordinate blocks and to a reflected cross block,
as in the Davis--Kahan double-angle argument.

## Provenance

Adapted from the maintained AIQ-Kitware DKPS formalization (Apache-2.0),
`ForTauCeti/Analysis/InnerProductSpace/DoubleAngle/Gram.lean`.

## Reference

C. Davis and W. Kahan, *The rotation of eigenvectors by a perturbation. III*,
SIAM Journal on Numerical Analysis 7 (1970), 1--46, Section 7.
-/

public section

namespace TauCeti

open scoped InnerProductSpace

/-! ### The scalar double-angle transfer -/

/-- For `-1 ≤ s ≤ 1`, the sine of twice the angle with sine `s` is
`2 * s * √(1 - s²)`. The formula holds for either sign of `s`. -/
theorem sin_two_mul_arcsin {s : ℝ} (h₀ : -1 ≤ s) (h₁ : s ≤ 1) :
    Real.sin (2 * Real.arcsin s) = 2 * s * √(1 - s ^ 2) := by
  rw [Real.sin_two_mul, Real.sin_arcsin h₀ h₁, Real.cos_arcsin]

/-- The squared double-angle sine of an angle with sine `s`, as a polynomial:
`sin (2 arcsin s) ^ 2 = 4 s² (1 - s²)`. -/
theorem sin_two_mul_arcsin_sq {s : ℝ} (h₀ : -1 ≤ s) (h₁ : s ≤ 1) :
    Real.sin (2 * Real.arcsin s) ^ 2 = 4 * s ^ 2 * (1 - s ^ 2) := by
  have hnn : (0 : ℝ) ≤ 1 - s ^ 2 := by nlinarith
  rw [sin_two_mul_arcsin h₀ h₁, mul_pow, mul_pow, Real.sq_sqrt hnn]
  ring

/-! ### The rectangular double-angle Gram identity -/

section Rectangular

variable {𝕜 : Type*} [RCLike 𝕜]
variable {K₀ K₁ L : Type*}
  [NormedAddCommGroup K₀] [InnerProductSpace 𝕜 K₀] [FiniteDimensional 𝕜 K₀]
  [NormedAddCommGroup K₁] [InnerProductSpace 𝕜 K₁] [FiniteDimensional 𝕜 K₁]
  [NormedAddCommGroup L] [InnerProductSpace 𝕜 L] [FiniteDimensional 𝕜 L]

/-- **The rectangular double-angle Gram identity.**  If `C⋆C = 1 - T T⋆` then
the Gram operator of the composite `C ∘ T` is `M - M²` for `M = T⋆T`.

The three spaces are independent: `T : K₁ →ₗ K₀` and `C : K₀ →ₗ L` need not have
equal-dimensional domains and codomains, and no direct rotation between them is
assumed.  This is what makes the `sin 2θ` estimate survive the dimension
mismatch `dim 𝔛(E₀) < dim 𝔛(F₀)` of Davis--Kahan 1970. -/
theorem gram_comp_of_gram_eq_id_sub {C : K₀ →ₗ[𝕜] L} {T : K₁ →ₗ[𝕜] K₀}
    (hC : LinearMap.adjoint C ∘ₗ C = LinearMap.id - T ∘ₗ LinearMap.adjoint T) :
    LinearMap.adjoint (C ∘ₗ T) ∘ₗ (C ∘ₗ T) =
      (LinearMap.adjoint T ∘ₗ T) -
        (LinearMap.adjoint T ∘ₗ T) ∘ₗ (LinearMap.adjoint T ∘ₗ T) := by
  ext x
  have hx := LinearMap.congr_fun hC (T x)
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply] at hx
  rw [LinearMap.adjoint_comp]
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, hx, map_sub]

/-- The Gram operator of `2 (C ∘ T)` is `4 (M - M²)`, `M = T⋆T`: the operator
form of `sin 2θ = 2 sin θ cos θ`, squared. -/
theorem gram_two_smul_comp {C : K₀ →ₗ[𝕜] L} {T : K₁ →ₗ[𝕜] K₀}
    (hC : LinearMap.adjoint C ∘ₗ C = LinearMap.id - T ∘ₗ LinearMap.adjoint T) :
    LinearMap.adjoint ((2 : 𝕜) • (C ∘ₗ T)) ∘ₗ ((2 : 𝕜) • (C ∘ₗ T)) =
      (4 : 𝕜) • ((LinearMap.adjoint T ∘ₗ T) -
        (LinearMap.adjoint T ∘ₗ T) ∘ₗ (LinearMap.adjoint T ∘ₗ T)) := by
  have hadj : LinearMap.adjoint ((2 : 𝕜) • (C ∘ₗ T)) =
      (2 : 𝕜) • LinearMap.adjoint (C ∘ₗ T) := by
    rw [map_smulₛₗ, map_ofNat]
  rw [hadj, LinearMap.smul_comp, LinearMap.comp_smul, gram_comp_of_gram_eq_id_sub hC,
    smul_smul]
  norm_num

/-- **Squared double-angle Gram action.** If `x` satisfies `M x = s² • x` for
`M = T⋆T` and `-1 ≤ s ≤ 1`, then the Gram operator of `2 (C ∘ T)` acts on `x`
by `sin (2 * arcsin s)²`. This statement also includes negative `s` and `x = 0`.
For `x ≠ 0`, the corresponding singular value is `|sin (2 * arcsin s)|`. -/
theorem gram_two_smul_comp_apply_of_eigenvector {C : K₀ →ₗ[𝕜] L} {T : K₁ →ₗ[𝕜] K₀}
    (hC : LinearMap.adjoint C ∘ₗ C = LinearMap.id - T ∘ₗ LinearMap.adjoint T)
    {s : ℝ} (h₀ : -1 ≤ s) (h₁ : s ≤ 1) {x : K₁}
    (hx : (LinearMap.adjoint T ∘ₗ T) x = ((s ^ 2 : ℝ) : 𝕜) • x) :
    (LinearMap.adjoint ((2 : 𝕜) • (C ∘ₗ T)) ∘ₗ ((2 : 𝕜) • (C ∘ₗ T))) x =
      ((Real.sin (2 * Real.arcsin s) ^ 2 : ℝ) : 𝕜) • x := by
  rw [gram_two_smul_comp hC]
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.comp_apply, hx,
    map_smul, smul_smul]
  rw [sin_two_mul_arcsin_sq h₀ h₁]
  push_cast
  module

end Rectangular

end TauCeti

open scoped InnerProductSpace

/-! ### The Davis--Kahan isometry blocks -/

section IsometryBlocks

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {K₀ K₁ L : Type*}
  [NormedAddCommGroup K₀] [InnerProductSpace 𝕜 K₀] [FiniteDimensional 𝕜 K₀]
  [NormedAddCommGroup K₁] [InnerProductSpace 𝕜 K₁] [FiniteDimensional 𝕜 K₁]
  [NormedAddCommGroup L] [InnerProductSpace 𝕜 L] [FiniteDimensional 𝕜 L]

/-- **Pythagorean Gram identity for complementary linear blocks.** If the ranges
of linear maps `F₀` and `F₁` satisfy `F₀F₀⋆ + F₁F₁⋆ = 1` and `E₀` is an
isometry, then `(F₀⋆E₀)⋆(F₀⋆E₀) = 1 - (E₀⋆F₁)(E₀⋆F₁)⋆`.
No isometry hypothesis on `F₀` or `F₁` is needed. -/
theorem LinearIsometry.gram_isometryBlock_eq_id_sub (E₀ : K₀ →ₗᵢ[𝕜] E)
    (F₀ : L →ₗ[𝕜] E) (F₁ : K₁ →ₗ[𝕜] E)
    (hF : F₀ ∘ₗ LinearMap.adjoint F₀ +
        F₁ ∘ₗ LinearMap.adjoint F₁ = LinearMap.id) :
    LinearMap.adjoint (LinearMap.adjoint F₀ ∘ₗ E₀.toLinearMap) ∘ₗ
        (LinearMap.adjoint F₀ ∘ₗ E₀.toLinearMap) =
      LinearMap.id -
        (LinearMap.adjoint E₀.toLinearMap ∘ₗ F₁) ∘ₗ
          LinearMap.adjoint
            (LinearMap.adjoint E₀.toLinearMap ∘ₗ F₁) := by
  ext x
  have hx := LinearMap.congr_fun hF (E₀ x)
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.id_apply] at hx
  rw [LinearMap.adjoint_comp, LinearMap.adjoint_comp, LinearMap.adjoint_adjoint,
    LinearMap.adjoint_adjoint]
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
    LinearIsometry.coe_toLinearMap]
  rw [eq_sub_iff_add_eq, ← map_add, hx]
  simpa only [LinearMap.comp_apply, LinearMap.id_apply,
    LinearIsometry.coe_toLinearMap] using
    (LinearMap.congr_fun (LinearIsometry.adjoint_comp_self' E₀) x)

/-- Complementary isometry blocks have orthogonal ranges: `F₀⋆F₁ = 0`.
Here the isometry hypotheses are essential to deduce orthogonality from
`F₀F₀⋆ + F₁F₁⋆ = 1`. -/
theorem LinearIsometry.adjoint_comp_isometryBlock_eq_zero
    (F₀ : L →ₗᵢ[𝕜] E) (F₁ : K₁ →ₗᵢ[𝕜] E)
    (hF : F₀.toLinearMap ∘ₗ LinearMap.adjoint F₀.toLinearMap +
        F₁.toLinearMap ∘ₗ LinearMap.adjoint F₁.toLinearMap = LinearMap.id) :
    LinearMap.adjoint F₀.toLinearMap ∘ₗ F₁.toLinearMap = 0 := by
  ext y
  have hy := LinearMap.congr_fun hF (F₁ y)
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.id_apply,
    LinearIsometry.coe_toLinearMap] at hy
  have hF₁ : LinearMap.adjoint F₁.toLinearMap (F₁ y) = y := by
    simpa only [LinearMap.comp_apply, LinearMap.id_apply,
      LinearIsometry.coe_toLinearMap] using
      (LinearMap.congr_fun (LinearIsometry.adjoint_comp_self' F₁) y)
  rw [hF₁] at hy
  have h0 : F₀ (LinearMap.adjoint F₀.toLinearMap (F₁ y)) = 0 := by
    have := hy
    rwa [add_eq_right] at this
  have := congrArg (LinearMap.adjoint F₀.toLinearMap) h0
  have hF₀ : LinearMap.adjoint F₀.toLinearMap
      (F₀ (LinearMap.adjoint F₀.toLinearMap (F₁ y))) =
      LinearMap.adjoint F₀.toLinearMap (F₁ y) := by
    simpa only [LinearMap.comp_apply, LinearMap.id_apply,
      LinearIsometry.coe_toLinearMap] using
      (LinearMap.congr_fun (LinearIsometry.adjoint_comp_self' F₀)
        (LinearMap.adjoint F₀.toLinearMap (F₁ y)))
  rw [map_zero, hF₀] at this
  simpa only [LinearMap.comp_apply, LinearMap.zero_apply,
    LinearIsometry.coe_toLinearMap] using this

omit [FiniteDimensional 𝕜 K₁] in
/-- **Cross-block identity under orthogonality.** For arbitrary linear maps
`E₀`, `F₀`, and `F₁` with `F₀⋆F₁ = 0`, the adjoint cross block of
`(2 E₀E₀⋆ - 1) F₀` equals `2 (F₀⋆E₀)(E₀⋆F₁)`.
For general `E₀` the operator `2 E₀E₀⋆ - 1` need not be a reflection. -/
theorem LinearMap.adjoint_reflection_comp_of_adjoint_comp_eq_zero
    (E₀ : K₀ →ₗ[𝕜] E) (F₀ : L →ₗ[𝕜] E) (F₁ : K₁ →ₗ[𝕜] E)
    (horth : LinearMap.adjoint F₀ ∘ₗ F₁ = 0) :
    LinearMap.adjoint
        (((2 : 𝕜) • (E₀ ∘ₗ LinearMap.adjoint E₀) -
          LinearMap.id) ∘ₗ F₀) ∘ₗ F₁ =
      (2 : 𝕜) • ((LinearMap.adjoint F₀ ∘ₗ E₀) ∘ₗ
        (LinearMap.adjoint E₀ ∘ₗ F₁)) := by
  have hX : LinearMap.adjoint
      ((2 : 𝕜) • (E₀ ∘ₗ LinearMap.adjoint E₀) - LinearMap.id) =
      (2 : 𝕜) • (E₀ ∘ₗ LinearMap.adjoint E₀) - LinearMap.id := by
    rw [map_sub, map_smulₛₗ, map_ofNat, LinearMap.adjoint_comp,
      LinearMap.adjoint_adjoint, LinearMap.adjoint_id]
  rw [LinearMap.adjoint_comp, hX]
  ext y
  have hy := LinearMap.congr_fun horth y
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hy
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.sub_apply,
    LinearMap.id_apply, map_sub, map_smul, hy, sub_zero]

/-- **Davis--Kahan reflected cross block for isometries.** Complementary
isometric blocks satisfy `F₀⋆F₁ = 0`, so the orthogonal linear-map formula
specializes to the reflection `2 E₀E₀⋆ - 1`. -/
theorem LinearIsometry.adjoint_reflection_comp_isometryBlock
    (E₀ : K₀ →ₗᵢ[𝕜] E) (F₀ : L →ₗᵢ[𝕜] E) (F₁ : K₁ →ₗᵢ[𝕜] E)
    (hF : F₀.toLinearMap ∘ₗ LinearMap.adjoint F₀.toLinearMap +
        F₁.toLinearMap ∘ₗ LinearMap.adjoint F₁.toLinearMap = LinearMap.id) :
    LinearMap.adjoint
        (((2 : 𝕜) • (E₀.toLinearMap ∘ₗ LinearMap.adjoint E₀.toLinearMap) -
          LinearMap.id) ∘ₗ F₀.toLinearMap) ∘ₗ F₁.toLinearMap =
      (2 : 𝕜) • ((LinearMap.adjoint F₀.toLinearMap ∘ₗ E₀.toLinearMap) ∘ₗ
        (LinearMap.adjoint E₀.toLinearMap ∘ₗ F₁.toLinearMap)) := by
  exact LinearMap.adjoint_reflection_comp_of_adjoint_comp_eq_zero
    E₀.toLinearMap F₀.toLinearMap F₁.toLinearMap
    (LinearIsometry.adjoint_comp_isometryBlock_eq_zero F₀ F₁ hF)

/-- **Reflected cross-block Gram identity for linear blocks.** If `E₀` is an
isometry and `F₀`, `F₁` are linear maps with complementary final operators
and orthogonal cross block, the reflected cross block has Gram operator
`4 (M - M²)` for `M = T⋆T` and `T = E₀⋆F₁`.
Orthogonality does not follow from complementarity without the isometry
hypotheses on `F₀` and `F₁`, so it is explicitly assumed. -/
theorem LinearIsometry.gram_adjoint_reflection_comp_isometryBlock_of_orthogonality
    (E₀ : K₀ →ₗᵢ[𝕜] E) (F₀ : L →ₗ[𝕜] E) (F₁ : K₁ →ₗ[𝕜] E)
    (hF : F₀ ∘ₗ LinearMap.adjoint F₀ +
        F₁ ∘ₗ LinearMap.adjoint F₁ = LinearMap.id)
    (horth : LinearMap.adjoint F₀ ∘ₗ F₁ = 0) :
    LinearMap.adjoint (LinearMap.adjoint
          (((2 : 𝕜) • (E₀.toLinearMap ∘ₗ LinearMap.adjoint E₀.toLinearMap) -
            LinearMap.id) ∘ₗ F₀) ∘ₗ F₁) ∘ₗ
        (LinearMap.adjoint
          (((2 : 𝕜) • (E₀.toLinearMap ∘ₗ LinearMap.adjoint E₀.toLinearMap) -
            LinearMap.id) ∘ₗ F₀) ∘ₗ F₁) =
      (4 : 𝕜) • ((LinearMap.adjoint (LinearMap.adjoint E₀.toLinearMap ∘ₗ
            F₁) ∘ₗ (LinearMap.adjoint E₀.toLinearMap ∘ₗ F₁)) -
        (LinearMap.adjoint (LinearMap.adjoint E₀.toLinearMap ∘ₗ F₁) ∘ₗ
            (LinearMap.adjoint E₀.toLinearMap ∘ₗ F₁)) ∘ₗ
          (LinearMap.adjoint (LinearMap.adjoint E₀.toLinearMap ∘ₗ F₁) ∘ₗ
            (LinearMap.adjoint E₀.toLinearMap ∘ₗ F₁))) := by
  rw [LinearMap.adjoint_reflection_comp_of_adjoint_comp_eq_zero
    E₀.toLinearMap F₀ F₁ horth]
  exact TauCeti.gram_two_smul_comp
    (LinearIsometry.gram_isometryBlock_eq_id_sub E₀ F₀ F₁ hF)

/-- **Reflected cross-block Gram identity for complementary isometries.**
For `T = E₀⋆F₁`, the Gram operator of `(X F₀)⋆F₁` with
`X = 2 E₀E₀⋆ - 1` equals `4 (M - M²)` where `M = T⋆T`.
No equality-of-dimensions hypothesis is required. -/
theorem LinearIsometry.gram_adjoint_reflection_comp_isometryBlock
    (E₀ : K₀ →ₗᵢ[𝕜] E) (F₀ : L →ₗᵢ[𝕜] E) (F₁ : K₁ →ₗᵢ[𝕜] E)
    (hF : F₀.toLinearMap ∘ₗ LinearMap.adjoint F₀.toLinearMap +
        F₁.toLinearMap ∘ₗ LinearMap.adjoint F₁.toLinearMap = LinearMap.id) :
    LinearMap.adjoint (LinearMap.adjoint
          (((2 : 𝕜) • (E₀.toLinearMap ∘ₗ LinearMap.adjoint E₀.toLinearMap) -
            LinearMap.id) ∘ₗ F₀.toLinearMap) ∘ₗ F₁.toLinearMap) ∘ₗ
        (LinearMap.adjoint
          (((2 : 𝕜) • (E₀.toLinearMap ∘ₗ LinearMap.adjoint E₀.toLinearMap) -
            LinearMap.id) ∘ₗ F₀.toLinearMap) ∘ₗ F₁.toLinearMap) =
      (4 : 𝕜) • ((LinearMap.adjoint (LinearMap.adjoint E₀.toLinearMap ∘ₗ
            F₁.toLinearMap) ∘ₗ (LinearMap.adjoint E₀.toLinearMap ∘ₗ F₁.toLinearMap)) -
        (LinearMap.adjoint (LinearMap.adjoint E₀.toLinearMap ∘ₗ F₁.toLinearMap) ∘ₗ
            (LinearMap.adjoint E₀.toLinearMap ∘ₗ F₁.toLinearMap)) ∘ₗ
          (LinearMap.adjoint (LinearMap.adjoint E₀.toLinearMap ∘ₗ F₁.toLinearMap) ∘ₗ
            (LinearMap.adjoint E₀.toLinearMap ∘ₗ F₁.toLinearMap))) := by
  exact LinearIsometry.gram_adjoint_reflection_comp_isometryBlock_of_orthogonality
    E₀ F₀.toLinearMap F₁.toLinearMap hF
    (LinearIsometry.adjoint_comp_isometryBlock_eq_zero F₀ F₁ hF)

end IsometryBlocks
