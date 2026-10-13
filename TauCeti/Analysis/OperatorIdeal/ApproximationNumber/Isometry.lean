/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Equivalence
public import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-!
# Approximation numbers under isometric changes of coordinates

Pre- and postcomposition with linear isometric equivalences preserve the
`ℝ≥0`-valued approximation-number sequence. The result is valid for maps
between different normed spaces and does not require finite dimension or
completeness. The proof uses the two-sided ideal inequality from the canonical
`ContinuousLinearMap.singularValue` API and applies it again to the inverses.

Adapted from the DKPS formalization's isometric-invariance argument. The
real-valued legacy `approximationNumber` API is not reintroduced.

The core invariance theorem is a prerequisite for OperatorIdeals target `OI-B72`:
the donor proof of `symmetricGaugeFamily_injective` invokes it to transport a
diagonal model through independent universe lifts.
-/

public section

namespace ContinuousLinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- Sandwiching an operator by linear isometric equivalences does not increase
its approximation numbers. -/
private theorem singularValue_linearIsometryEquiv_sandwich_le {X Y X' Y' : Type*}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [NormedAddCommGroup X'] [NormedSpace 𝕜 X'] [NormedAddCommGroup Y'] [NormedSpace 𝕜 Y']
    (a : X' ≃ₗᵢ[𝕜] X) (b : Y ≃ₗᵢ[𝕜] Y') (S : X →L[𝕜] Y) (n : ℕ) :
    (b.toLinearIsometry.toContinuousLinearMap ∘L S ∘L
        a.toLinearIsometry.toContinuousLinearMap).singularValue n
      ≤ S.singularValue n := by
  calc
    _ ≤ ‖b.toLinearIsometry.toContinuousLinearMap‖₊ * S.singularValue n *
        ‖a.toLinearIsometry.toContinuousLinearMap‖₊ :=
      singularValue_comp_comp_le _ _ _ n
    _ ≤ 1 * S.singularValue n * 1 := by
      gcongr <;>
        first
          | apply NNReal.coe_le_coe.mp
            simpa only [coe_nnnorm, NNReal.coe_one] using
              b.toLinearIsometry.norm_toContinuousLinearMap_le
          | apply NNReal.coe_le_coe.mp
            simpa only [coe_nnnorm, NNReal.coe_one] using
              a.toLinearIsometry.norm_toContinuousLinearMap_le
    _ = _ := by simp

variable {E F E' F' : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F'] [NormedSpace 𝕜 F']

/-- Linear isometric changes of domain and codomain preserve the canonical
nonnegative approximation numbers, even across different universes. -/
theorem singularValue_comp_linearIsometryEquiv
    (e : E' ≃ₗᵢ[𝕜] E) (f : F ≃ₗᵢ[𝕜] F') (T : E →L[𝕜] F) (n : ℕ) :
    (f.toLinearIsometry.toContinuousLinearMap ∘L T ∘L
        e.toLinearIsometry.toContinuousLinearMap).singularValue n =
      T.singularValue n := by
  refine le_antisymm (singularValue_linearIsometryEquiv_sandwich_le e f T n) ?_
  have h := singularValue_linearIsometryEquiv_sandwich_le e.symm f.symm
    (f.toLinearIsometry.toContinuousLinearMap ∘L T ∘L
      e.toLinearIsometry.toContinuousLinearMap) n
  have heq : f.symm.toLinearIsometry.toContinuousLinearMap ∘L
      (f.toLinearIsometry.toContinuousLinearMap ∘L T ∘L
        e.toLinearIsometry.toContinuousLinearMap) ∘L
        e.symm.toLinearIsometry.toContinuousLinearMap = T := by
    ext x
    simp
  rwa [heq] at h

/-- A change of isometric coordinates preserves the equivalence class of the
approximation-number sequence. -/
theorem sameSingularValues_comp_linearIsometryEquiv
    (e : E' ≃ₗᵢ[𝕜] E) (f : F ≃ₗᵢ[𝕜] F') (T : E →L[𝕜] F) :
    SameSingularValues
      (f.toLinearIsometry.toContinuousLinearMap ∘L T ∘L
        e.toLinearIsometry.toContinuousLinearMap) T := by
  apply (sameSingularValues_iff _ _).2
  intro n
  exact singularValue_comp_linearIsometryEquiv e f T n

/-- Ky Fan prefix gauges are invariant under linear isometric coordinate changes. -/
theorem kyFanGauge_comp_linearIsometryEquiv
    (e : E' ≃ₗᵢ[𝕜] E) (f : F ≃ₗᵢ[𝕜] F') (T : E →L[𝕜] F) (k : ℕ) :
    (f.toLinearIsometry.toContinuousLinearMap ∘L T ∘L
      e.toLinearIsometry.toContinuousLinearMap).kyFanGauge k = T.kyFanGauge k :=
  (sameSingularValues_comp_linearIsometryEquiv e f T).kyFanGauge_eq k

end ContinuousLinearMap
