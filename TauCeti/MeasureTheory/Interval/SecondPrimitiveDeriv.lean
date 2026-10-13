/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
/-
Ported from AIQ-Kitware/aiq-dkps-formalization,
ForTauCeti/MeasureTheory/IntervalSecondPrimitiveDeriv.lean (Apache-2.0).
Source: https://github.com/AIQ-Kitware/aiq-dkps-formalization
-/
module

public import TauCeti.MeasureTheory.Interval.WeakSecondDeriv
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Derivatives of the second primitive

The second primitive `K w` from `IntervalWeakSecondDeriv` is globally differentiable with
derivative the running integral of the density. If the density is continuous on `[0,1]`,
the running integral is differentiable within the interval with derivative equal to the
density (the fundamental theorem of calculus).

These two steps are the engine of the free-beam eigenfunction bootstrap: a weak eigenfunction
is an affine function plus a second primitive twice over, so it acquires a full fourth-order
derivative chain within `[0,1]` and the interval ODE classification applies.

The scalar field is an arbitrary `RCLike` `𝕜`.

## Main results

* `TauCeti.hasDerivAt_secondPrimitive`: `(K w)' = firstPrimitive w` everywhere.
* `TauCeti.hasDerivWithinAt_firstPrimitive_of_continuous`: `(firstPrimitive w)' = w` within
  `[0,1]` for continuous `w`.
-/

public section

namespace TauCeti

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

variable {𝕜 : Type*} [RCLike 𝕜]

/-- Running integral of a density on the unit interval, cut off below the parameter. -/
def firstPrimitive (w : ℝ → 𝕜) (t : ℝ) : 𝕜 :=
  ∫ s, (Set.Iio t).indicator w s ∂unitIocMeasure

/-- The first primitive is the integral of the density below its parameter. -/
theorem firstPrimitive_def (w : ℝ → 𝕜) (t : ℝ) :
    firstPrimitive w t = ∫ s, (Set.Iio t).indicator w s ∂unitIocMeasure := (rfl)

/-- The first primitive of the zero density vanishes. -/
@[simp] theorem firstPrimitive_zero_density (t : ℝ) :
    firstPrimitive (fun _ => (0 : 𝕜)) t = 0 := by
  simp [firstPrimitive_def]

/-- The first primitive vanishes at the left endpoint of the unit interval. -/
@[simp] theorem firstPrimitive_zero (w : ℝ → 𝕜) : firstPrimitive w 0 = 0 := by
  rw [firstPrimitive_def]
  have hz : (Set.Iio (0 : ℝ)).indicator w =ᵐ[unitIocMeasure]
      (fun _ => (0 : 𝕜)) := by
    filter_upwards [ae_mem_unitIocMeasure] with s hs
    rw [Set.indicator_of_notMem (by simp only [Set.mem_Iio]; exact not_lt.mpr hs.1.le)]
  rw [integral_congr_ae hz]
  simp

/-- The first primitive is additive for integrable densities. -/
theorem firstPrimitive_add {w v : ℝ → 𝕜}
    (hw : Integrable w unitIocMeasure) (hv : Integrable v unitIocMeasure)
    (t : ℝ) :
    firstPrimitive (fun s => w s + v s) t = firstPrimitive w t + firstPrimitive v t := by
  rw [firstPrimitive_def, firstPrimitive_def, firstPrimitive_def,
    ← integral_add (hw.indicator measurableSet_Iio) (hv.indicator measurableSet_Iio)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun s => by
    by_cases hs : s ∈ Set.Iio t
    · simp only [Set.indicator_of_mem hs]
    · simp only [Set.indicator_of_notMem hs, add_zero]

/-- The first primitive commutes with scalar multiplication of its density. -/
theorem firstPrimitive_mul (c : 𝕜) (w : ℝ → 𝕜) (t : ℝ) :
    firstPrimitive (fun s => c * w s) t = c * firstPrimitive w t := by
  rw [firstPrimitive_def, firstPrimitive_def, ← MeasureTheory.integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun s => by
    by_cases hs : s ∈ Set.Iio t
    · simp only [Set.indicator_of_mem hs]
    · simp only [Set.indicator_of_notMem hs, mul_zero]

/-- The running integral depends only on the almost-everywhere class of the density. -/
theorem firstPrimitive_congr_ae {w w' : ℝ → 𝕜} (h : w =ᵐ[unitIocMeasure] w') :
    firstPrimitive w = firstPrimitive w' := by
  funext t
  refine integral_congr_ae ?_
  filter_upwards [h] with s hs
  by_cases hst : s ∈ Set.Iio t
  · rw [Set.indicator_of_mem hst, Set.indicator_of_mem hst, hs]
  · rw [Set.indicator_of_notMem hst, Set.indicator_of_notMem hst]

/-- **Differentiation under the integral**: the second primitive is everywhere
differentiable, with derivative the running integral of the density. -/
theorem hasDerivAt_secondPrimitive {w : ℝ → 𝕜} (hw : Integrable w unitIocMeasure)
    (t₀ : ℝ) : HasDerivAt (secondPrimitive w) (firstPrimitive w t₀) t₀ := by
  have hnull : unitIocMeasure {t₀} = 0 := unitIocMeasure_singleton t₀
  have hmeasF : ∀ t : ℝ, AEStronglyMeasurable
      (fun s => (secondPrimitiveKernel t s : 𝕜) * w s) unitIocMeasure := fun t =>
    ((RCLike.continuous_ofReal.comp
      (continuous_secondPrimitiveKernel.comp
        (Continuous.prodMk continuous_const continuous_id))).aestronglyMeasurable).mul
      hw.aestronglyMeasurable
  have key := hasDerivAt_integral_of_dominated_loc_of_lip
    (F := fun t s => (secondPrimitiveKernel t s : 𝕜) * w s)
    (F' := fun s => (Set.Iio t₀).indicator w s)
    (bound := fun s => ‖w s‖)
    (μ := unitIocMeasure) (x₀ := t₀)
    (Filter.univ_mem)
    (Filter.Eventually.of_forall hmeasF)
    (integrable_secondPrimitiveKernel_mul hw t₀)
    (hw.aestronglyMeasurable.indicator measurableSet_Iio)
    ?_ hw.norm ?_
  · have hfun : secondPrimitive w =
        (fun t : ℝ => ∫ s, (secondPrimitiveKernel t s : 𝕜) * w s ∂unitIocMeasure) := by
        funext t
        exact secondPrimitive_def w t
    rw [hfun, firstPrimitive_def]
    exact key.2
  · refine Filter.Eventually.of_forall fun s => ?_
    refine LipschitzOnWith.of_dist_le_mul fun t _ t' _ => ?_
    rw [dist_eq_norm, dist_eq_norm]
    have hdiff : (secondPrimitiveKernel t s : 𝕜) * w s
        - (secondPrimitiveKernel t' s : 𝕜) * w s
        = ((secondPrimitiveKernel t s - secondPrimitiveKernel t' s : ℝ) : 𝕜) * w s := by
      push_cast
      ring
    rw [hdiff, norm_mul, RCLike.norm_ofReal, Real.norm_eq_abs]
    have hcoe : ((Real.nnabs ‖w s‖ : ℝ≥0) : ℝ) = ‖w s‖ := by
      simp
    rw [hcoe]
    calc |secondPrimitiveKernel t s - secondPrimitiveKernel t' s| * ‖w s‖
        ≤ |t - t'| * ‖w s‖ :=
          mul_le_mul_of_nonneg_right (abs_secondPrimitiveKernel_sub_le t t' s)
            (norm_nonneg _)
      _ = ‖w s‖ * ‖t - t'‖ := by rw [Real.norm_eq_abs]; ring
  · have hae : ∀ᵐ s ∂unitIocMeasure, s ≠ t₀ := by
      rw [MeasureTheory.ae_iff]
      refine measure_mono_null (fun s hs => ?_) hnull
      simpa using hs
    filter_upwards [hae] with s hs
    rcases lt_or_gt_of_ne hs with hlt | hgt
    · -- `s < t₀`: locally the kernel is `t - s`.
      have hlin : HasDerivAt (fun t : ℝ => ((t - s : ℝ) : 𝕜) * w s) ((1 : 𝕜) * w s) t₀ := by
        have h1 : HasDerivAt (fun t : ℝ => ((t - s : ℝ) : 𝕜)) 1 t₀ := by
          have hbase : HasDerivAt (fun t : ℝ => t - s) 1 t₀ :=
            (hasDerivAt_id t₀).sub_const s
          have hcomp := (RCLike.ofRealCLM (K := 𝕜)).hasDerivAt.scomp t₀ hbase
          simpa only [Function.comp_def, RCLike.ofRealCLM_apply, RCLike.ofReal_one,
            one_smul] using hcomp
        simpa using h1.mul_const (w s)
      have heq : (fun t : ℝ => ((t - s : ℝ) : 𝕜) * w s)
          =ᶠ[nhds t₀] fun t : ℝ => (secondPrimitiveKernel t s : 𝕜) * w s := by
        filter_upwards [eventually_gt_nhds hlt] with t ht
        rw [secondPrimitiveKernel_of_le ht.le]
      have hres := heq.hasDerivAt_iff.mp hlin
      rw [Set.indicator_of_mem (Set.mem_Iio.mpr hlt)]
      simpa using hres
    · -- `s > t₀`: locally the kernel vanishes.
      have hzero : HasDerivAt (fun _ : ℝ => (0 : 𝕜)) 0 t₀ := hasDerivAt_const _ _
      have heq : (fun _ : ℝ => (0 : 𝕜))
          =ᶠ[nhds t₀] fun t : ℝ => (secondPrimitiveKernel t s : 𝕜) * w s := by
        filter_upwards [eventually_lt_nhds hgt] with t ht
        rw [secondPrimitiveKernel_of_ge ht.le]
        simp
      have hres := heq.hasDerivAt_iff.mp hzero
      rw [Set.indicator_of_notMem (by simpa using hgt.le)]
      simpa using hres

/-- On the unit interval the running integral is the interval integral of the density. -/
theorem firstPrimitive_eq_intervalIntegral {w : ℝ → 𝕜}
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    firstPrimitive w t = ∫ s in (0 : ℝ)..t, w s := by
  have hset : Set.Ioc (0 : ℝ) 1 ∩ Set.Iio t = Set.Ioo 0 t := by
    ext s
    constructor
    · rintro ⟨⟨hs0, _⟩, hst⟩
      exact ⟨hs0, hst⟩
    · rintro ⟨hs0, hst⟩
      exact ⟨⟨hs0, le_trans (le_of_lt hst) ht.2⟩, hst⟩
  rw [firstPrimitive, unitIocMeasure_def, integral_indicator measurableSet_Iio,
    Measure.restrict_restrict measurableSet_Iio, Set.inter_comm, hset,
    intervalIntegral.integral_of_le ht.1, ← integral_Ioc_eq_integral_Ioo]

/-- **Fundamental theorem of calculus within the interval**: for a continuous density the
running integral is differentiable within `[0,1]` with derivative the density. -/
theorem hasDerivWithinAt_firstPrimitive_of_continuous {w : ℝ → 𝕜}
    (hw : ContinuousOn w (Set.Icc (0 : ℝ) 1))
    {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivWithinAt (firstPrimitive w) (w t₀) (Set.Icc 0 1) t₀ := by
  have hsubset : Set.uIcc (0 : ℝ) t₀ ⊆ Set.Icc (0 : ℝ) 1 := by
    rw [Set.uIcc_of_le ht₀.1]
    exact Set.Icc_subset_Icc le_rfl ht₀.2
  have hwInt : IntervalIntegrable w volume 0 t₀ :=
    (hw.mono hsubset).intervalIntegrable
  have : Fact (t₀ ∈ Set.Icc (0 : ℝ) 1) := ⟨ht₀⟩
  have hFTC : HasDerivWithinAt (fun u => ∫ x in (0 : ℝ)..u, w x)
      (w t₀) (Set.Icc 0 1) t₀ :=
    intervalIntegral.integral_hasDerivWithinAt_right hwInt
      (hw.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t₀)
      (hw t₀ ht₀)
  refine hFTC.congr ?_ ?_
  · intro y hy
    exact firstPrimitive_eq_intervalIntegral hy
  · exact firstPrimitive_eq_intervalIntegral ht₀

end

end TauCeti
