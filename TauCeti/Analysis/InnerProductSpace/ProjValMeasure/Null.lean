/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.Basic
public import Mathlib.MeasureTheory.OuterMeasure.AE

/-!
# Null sets of a projection-valued measure

A projection-valued measure `P` has a diagonal scalar measure `P.diag ξ` for each vector `ξ`.
The filter `P.ae` records sets that are conull for *every* diagonal measure. A measurable set
is null for this filter precisely when its spectral projection vanishes.

The null measurable sets are closed under taking measurable subsets and countable unions.
This is the shared almost-everywhere interface needed for the bounded Borel spectral integral.

## Provenance

The finite diagonal scalar measures and projection identities are from the maintained
AIQ-Kitware DKPS formalization (Kitware, Inc.; Apache-2.0):
https://github.com/AIQ-Kitware/aiq-dkps-formalization
(`ForTauCeti/Analysis/InnerProductSpace/ProjValMeasure/Basic.lean`).
The filter packages those existing results with Mathlib's native almost-everywhere API.
-/

public section

open MeasureTheory Filter
open scoped InnerProductSpace

namespace TauCeti
namespace ProjValMeasure

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The filter of sets conull for every diagonal measure of the PVM. -/
@[expose]
noncomputable def ae (P : ProjValMeasure X H) : Filter X :=
  ⨆ ξ : H, MeasureTheory.ae (P.diag ξ)

/-- Membership in the PVM's almost-everywhere filter is simultaneous conullity
for all its diagonal scalar measures. -/
@[simp]
theorem mem_ae_iff (P : ProjValMeasure X H) (s : Set X) :
    s ∈ P.ae ↔ ∀ ξ : H, (P.diag ξ) sᶜ = 0 := by
  simp only [ae, Filter.mem_iSup, MeasureTheory.mem_ae_iff]

/-- A set is null for the PVM iff each diagonal measure vanishes on it. -/
theorem compl_mem_ae_iff (P : ProjValMeasure X H) (s : Set X) :
    sᶜ ∈ P.ae ↔ ∀ ξ : H, (P.diag ξ) s = 0 := by
  simpa only [compl_compl] using P.mem_ae_iff sᶜ

/-- A measurable spectral projection is zero exactly when every diagonal measure
assigns its set zero mass. -/
theorem proj_eq_zero_iff_diag_zero (P : ProjValMeasure X H)
    (s : Set X) (hs : MeasurableSet s) :
    P.proj s hs = 0 ↔ ∀ ξ : H, (P.diag ξ) s = 0 := by
  constructor
  · intro h ξ
    have hr : ((P.diag ξ) s).toReal = 0 := by
      simpa [h] using (P.norm_sq_proj_apply s hs ξ).symm
    have hfin : (P.diag ξ) s ≠ ⊤ :=
      ne_of_lt ((measure_mono (Set.subset_univ s)).trans_lt
        (P.diag_finite ξ).measure_univ_lt_top)
    exact ((ENNReal.toReal_eq_zero_iff _).mp hr).resolve_right hfin
  · intro h
    apply ContinuousLinearMap.eq_of_diagonal
    intro ξ
    rw [P.inner_proj s hs ξ, h ξ]
    simp

/-- A measurable set is PVM-null iff its orthogonal projection vanishes. -/
theorem proj_eq_zero_iff_compl_mem_ae (P : ProjValMeasure X H)
    (s : Set X) (hs : MeasurableSet s) :
    P.proj s hs = 0 ↔ sᶜ ∈ P.ae := by
  rw [P.proj_eq_zero_iff_diag_zero s hs, P.compl_mem_ae_iff]

/-- PVM-null measurable sets are downward closed. -/
theorem proj_eq_zero_of_subset (P : ProjValMeasure X H)
    {s t : Set X} (hst : s ⊆ t) (hs : MeasurableSet s)
    (ht : MeasurableSet t) (h : P.proj t ht = 0) :
    P.proj s hs = 0 := by
  apply (P.proj_eq_zero_iff_diag_zero s hs).2
  intro ξ
  exact measure_mono_null hst ((P.proj_eq_zero_iff_diag_zero t ht).1 h ξ)

/-- PVM-null measurable sets are closed under countable unions. -/
theorem proj_iUnion_eq_zero (P : ProjValMeasure X H)
    (s : ℕ → Set X) (hs : ∀ i, MeasurableSet (s i))
    (h : ∀ i, P.proj (s i) (hs i) = 0) :
    P.proj (⋃ i, s i) (MeasurableSet.iUnion hs) = 0 := by
  apply (P.proj_eq_zero_iff_diag_zero _ _).2
  intro ξ
  exact measure_iUnion_null fun i =>
    (P.proj_eq_zero_iff_diag_zero (s i) (hs i)).1 (h i) ξ

end ProjValMeasure
end TauCeti
