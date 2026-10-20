/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.Polarization
public import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic

/-!
# The sharp variation estimate for polarized spectral measures

For the complex measure `P.polarizedComplexMeasure ψ ξ` associated with a normalized
projection-valued measure, we prove

`(P.polarizedComplexMeasure ψ ξ).variation univ ≤ ofReal (‖ψ‖ * ‖ξ‖)`.

The central argument is the weighted arithmetic-geometric mean inequality. For a measurable
set `B`, the projection identity and Cauchy-Schwarz show that

`‖⟪ψ, P(B) ξ⟫‖ ≤ ‖P(B) ψ‖ * ‖P(B) ξ‖`.

Weighting the two finite diagonal measures by `‖ξ‖/(2‖ψ‖)` and `‖ψ‖/(2‖ξ‖)`
gives a positive measure dominating the vector measure's total variation and having
mass exactly `‖ψ‖ * ‖ξ‖`. Zero vectors are handled separately.

The underlying PVM and polarized-measure constructions are adapted from the
AIQ-Kitware DKPS formalization (Apache-2.0):
https://github.com/AIQ-Kitware/aiq-dkps-formalization.
-/

public section

open MeasureTheory
open scoped InnerProductSpace ENNReal NNReal

namespace TauCeti.ProjValMeasure

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The variation of a polarized spectral measure has the sharp mass bound. -/
theorem polarizedComplexMeasure_variation_univ_le (P : ProjValMeasure X H) (ψ ξ : H) :
    (P.polarizedComplexMeasure ψ ξ).variation Set.univ ≤
      ENNReal.ofReal (‖ψ‖ * ‖ξ‖) := by
  by_cases hψz : ψ = 0
  · subst ψ
    rw [P.polarizedComplexMeasure_zero_left, VectorMeasure.variation_zero]
    simp
  by_cases hξz : ξ = 0
  · subst ξ
    rw [P.polarizedComplexMeasure_zero_right, VectorMeasure.variation_zero]
    simp
  have hψ : 0 < ‖ψ‖ := norm_pos_iff.mpr hψz
  have hξ : 0 < ‖ξ‖ := norm_pos_iff.mpr hξz
  let a : ℝ≥0 := ⟨‖ξ‖ / (2 * ‖ψ‖), by positivity⟩
  let b : ℝ≥0 := ⟨‖ψ‖ / (2 * ‖ξ‖), by positivity⟩
  have ha : (a : ℝ) = ‖ξ‖ / (2 * ‖ψ‖) := rfl
  have hb : (b : ℝ) = ‖ψ‖ / (2 * ‖ξ‖) := rfl
  let m : Measure X := a • P.diag ψ + b • P.diag ξ
  have hm (B : Set X) :
      m.real B = (a : ℝ) * (P.diag ψ).real B +
        (b : ℝ) * (P.diag ξ).real B := by
    simp only [m]
    rw [measureReal_add_apply, measureReal_nnreal_smul_apply,
      measureReal_nnreal_smul_apply]
  have hbound (B : Set X) (hB : MeasurableSet B) :
      ‖P.polarizedComplexMeasure ψ ξ B‖ ≤ m.real B := by
    let T := P.proj B hB
    have hcs :
        ‖P.polarizedComplexMeasure ψ ξ B‖ ≤ ‖T ψ‖ * ‖T ξ‖ := by
      rw [P.polarizedComplexMeasure_apply ψ ξ B hB]
      rw [P.inner_proj_eq_inner_proj_proj B hB ψ ξ]
      exact norm_inner_le_norm _ _
    have hy :
        ‖T ψ‖ * ‖T ξ‖ ≤
          (‖ξ‖ / (2 * ‖ψ‖)) * ‖T ψ‖ ^ 2 +
            (‖ψ‖ / (2 * ‖ξ‖)) * ‖T ξ‖ ^ 2 := by
      have hdenom : 0 < 2 * ‖ψ‖ * ‖ξ‖ := by positivity
      have hfraction :
          ‖ξ‖ / (2 * ‖ψ‖) * ‖T ψ‖ ^ 2 +
              ‖ψ‖ / (2 * ‖ξ‖) * ‖T ξ‖ ^ 2 =
            ((‖ξ‖ * ‖T ψ‖) ^ 2 +
                (‖ψ‖ * ‖T ξ‖) ^ 2) /
              (2 * ‖ψ‖ * ‖ξ‖) := by
        field_simp [ne_of_gt hψ, ne_of_gt hξ]
      rw [hfraction]
      apply (le_div_iff₀ hdenom).2
      nlinarith only [two_mul_le_add_sq
        (‖ξ‖ * ‖T ψ‖) (‖ψ‖ * ‖T ξ‖)]
    rw [P.norm_sq_proj_apply B hB ψ, P.norm_sq_proj_apply B hB ξ] at hy
    calc
      ‖P.polarizedComplexMeasure ψ ξ B‖ ≤ ‖T ψ‖ * ‖T ξ‖ := hcs
      _ ≤ m.real B := by
        rw [hm B, ha, hb]
        simpa only [measureReal_def] using hy
  have hmajor : (P.polarizedComplexMeasure ψ ξ).variation ≤ m := by
    apply VectorMeasure.variation_le_of_forall_enorm_le
    intro B hB
    simpa only [measureReal_def, ofReal_norm] using
      (ENNReal.ofReal_le_of_le_toReal (hbound B hB))
  have hmass : m.real Set.univ = ‖ψ‖ * ‖ξ‖ := by
    rw [hm Set.univ, P.diag_real_univ, P.diag_real_univ, ha, hb]
    field_simp [ne_of_gt hψ, ne_of_gt hξ]
    ring
  calc
    (P.polarizedComplexMeasure ψ ξ).variation Set.univ ≤ m Set.univ :=
      hmajor Set.univ
    _ = ENNReal.ofReal (‖ψ‖ * ‖ξ‖) := by
      calc
        m Set.univ = ENNReal.ofReal (m.real Set.univ) :=
          (ofReal_measureReal (μ := m) (s := Set.univ)).symm
        _ = ENNReal.ofReal (‖ψ‖ * ‖ξ‖) := by rw [hmass]

/-- The variation of a polarized complex measure is finite. -/
instance instIsFiniteMeasurePolarizedVariation (P : ProjValMeasure X H) (ψ ξ : H) :
    IsFiniteMeasure (P.polarizedComplexMeasure ψ ξ).variation := by
  refine ⟨?_⟩
  exact (P.polarizedComplexMeasure_variation_univ_le ψ ξ).trans_lt
    ENNReal.ofReal_lt_top

end TauCeti.ProjValMeasure
