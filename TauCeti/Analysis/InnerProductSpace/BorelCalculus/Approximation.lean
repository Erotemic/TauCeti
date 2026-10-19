/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import TauCeti.Analysis.InnerProductSpace.BorelCalculus.DiagonalMeasure
public import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# Simultaneous continuous approximation on a compact spectrum

A complex-valued integrable symbol on the spectrum of a bounded operator can be approximated
in `L¹` by a continuous symbol. For a finite family of finite measures, a *single* continuous
symbol approximates against every measure: approximate in the sum measure, then use monotonicity.

The result supplies the approximation step used later to transport continuous functional-calculus
identities to bounded Borel symbols.

## Provenance

Adapted from `ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Polarization.lean` in the
Kitware DKPS formalization. The one-measure proof is retained; the finite-family result isolates
its simultaneous form for use without the polarized pairing or Borel-operator construction.
-/

public section

open MeasureTheory
open scoped InnerProductSpace ENNReal CompactlySupported

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {a : H →L[ℂ] H}

namespace MeasureTheory.Measure

/-- Every integrable complex symbol on the compact spectrum of a bounded operator can be
approximated in `L¹` by a continuous symbol. -/
theorem exists_continuous_integral_norm_sub_le (ν : Measure (spectrum ℂ a))
    [IsFiniteMeasure ν] {f : spectrum ℂ a → ℂ} (hf : Integrable f ν)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : C(spectrum ℂ a, ℂ), Integrable (fun x => g x) ν ∧
      ∫ x, ‖f x - g x‖ ∂ν ≤ ε := by
  have hmem : MemLp f 1 ν := memLp_one_iff_integrable.mpr hf
  obtain ⟨g, hgle, hgmem⟩ :=
    hmem.exists_boundedContinuous_eLpNorm_sub_le (p := 1) (by simp)
      (ε := ENNReal.ofReal ε) (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hε)
  have hgint : Integrable (fun x => g x) ν := memLp_one_iff_integrable.mp hgmem
  have hsub_meas : AEStronglyMeasurable (f - ⇑g) ν :=
    (hf.sub hgint).aestronglyMeasurable
  have hint : ∫ x, ‖f x - g x‖ ∂ν = (eLpNorm (f - ⇑g) 1 ν).toReal := by
    rw [eLpNorm_one_eq_lintegral_enorm hsub_meas,
      integral_norm_eq_lintegral_enorm (μ := ν) (f := fun x => f x - g x)
        hsub_meas]
    rfl
  have happrox : (∫ x, ‖f x - g x‖ ∂ν) ≤ ε := by
    rw [hint]
    calc
      (eLpNorm (f - ⇑g) 1 ν).toReal ≤ (ENNReal.ofReal ε).toReal := by
        apply ENNReal.toReal_mono _ hgle
        simp
      _ = ε := ENNReal.toReal_ofReal hε.le
  refine ⟨g.toContinuousMap, ?_, ?_⟩
  · simpa only [BoundedContinuousFunction.coe_toContinuousMap] using hgint
  · simpa only [BoundedContinuousFunction.coe_toContinuousMap] using happrox

end MeasureTheory.Measure

namespace TauCeti.BorelCalculus

/-- A symbol integrable against every measure in a finite family of finite Borel measures
on a compact operator spectrum has a single continuous approximant whose `L¹` error is
at most `ε` for every measure. -/
theorem exists_continuous_simultaneous_integral_norm_sub_le
    {ι : Type*} [Finite ι] (μ : ι → Measure (spectrum ℂ a))
    (hμ : ∀ i, μ i Set.univ < ⊤)
    {f : spectrum ℂ a → ℂ} (hf : ∀ i, Integrable f (μ i))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : C(spectrum ℂ a, ℂ), ∀ i,
      ∫ x, ‖f x - g x‖ ∂(μ i) ≤ ε := by
  classical
  let fintype : Fintype ι := Fintype.ofFinite ι
  let ν : Measure (spectrum ℂ a) := ∑ i, μ i
  have hν : IsFiniteMeasure ν := by
    refine ⟨?_⟩
    dsimp [ν]
    rw [Measure.coe_finsetSum, Finset.sum_apply]
    exact ENNReal.sum_lt_top.mpr (fun i _ => hμ i)
  have hfi : Integrable f ν := by
    dsimp [ν]
    exact integrable_finsetSum_measure.mpr (fun i _ => hf i)
  obtain ⟨g, hg, hgle⟩ := ν.exists_continuous_integral_norm_sub_le hfi hε
  refine ⟨g, fun i => ?_⟩
  have hdom : μ i ≤ ν := by
    dsimp [ν]
    exact Finset.single_le_sum (f := fun j => μ j) (fun _ _ => Measure.zero_le _)
      (Finset.mem_univ i)
  exact (integral_mono_measure hdom (Filter.Eventually.of_forall fun _ => norm_nonneg _)
    (hfi.sub hg).norm).trans hgle

end TauCeti.BorelCalculus
