/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import TauCeti.MeasureTheory.Function.Lp.Multiplication
public import TauCeti.MeasureTheory.Function.Lp.ExtendByZero
public import TauCeti.MeasureTheory.Function.Lp.CastMeasure
public import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Orthogonal decomposition of L² along measurable partitions

The existing `TauCeti.extendByZeroLpₗᵢ` embeds L² of a restricted measure
into ambient L². Its ranges over disjoint measurable sets are orthogonal.
For a countable partition whose union is conull, those ranges form a Hilbert sum.

The module also records intertwining of extension and restriction with bounded
multiplication and pointwise conjugation. The extension is constructed by composing
existing TauCeti isometries, not reproving its norm bound.
-/

public section

open MeasureTheory

open scoped ENNReal InnerProductSpace

namespace TauCeti

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {s t : Set α}

section Indicator

/-- Extension by zero is well defined on almost-everywhere classes: functions that agree
`μ|_s`-almost everywhere have indicators that agree `μ`-almost everywhere. -/
theorem indicator_ae_eq_of_restrict (hs : MeasurableSet s) {f g : α → ℂ}
    (h : f =ᵐ[μ.restrict s] g) : s.indicator f =ᵐ[μ] s.indicator g := by
  rw [Filter.EventuallyEq, ae_restrict_iff' hs] at h
  filter_upwards [h] with x hx
  by_cases hxs : x ∈ s
  · simp [hxs, hx hxs]
  · simp [hxs]

/-- Extension by zero from a measurable set to the ambient L² space.

This is TauCeti's existing `extendByZeroLpₗᵢ` followed by the canonical
isometric cast from `μ.restrict univ` to `μ`. -/
noncomputable def extendLp (μ : Measure α) (hs : MeasurableSet s) :
    Lp ℂ 2 (μ.restrict s) →ₗᵢ[ℂ] Lp ℂ 2 μ :=
  (castLpₗᵢ (𝕜 := ℂ) (Measure.restrict_univ (μ := μ))).toLinearIsometry.comp
    (extendByZeroLpₗᵢ ℂ μ hs (Set.subset_univ s))

/-- Representatives of extension by zero are the set indicator. -/
theorem coeFn_extendLp (μ : Measure α) (hs : MeasurableSet s)
    (F : Lp ℂ 2 (μ.restrict s)) :
    (extendLp μ hs F : α → ℂ) =ᵐ[μ] s.indicator (F : α → ℂ) := by
  have h := coeFn_extendByZeroLpₗᵢ ℂ hs (Set.subset_univ s) F
  have h' :
      ((extendByZeroLpₗᵢ ℂ μ hs (Set.subset_univ s) F :
          Lp ℂ 2 (μ.restrict Set.univ)) : α → ℂ)
      =ᵐ[μ] s.indicator (F : α → ℂ) := by
    simpa only [Measure.restrict_univ] using h
  filter_upwards [h'] with x hx
  -- The cast along `μ.restrict univ = μ` does not change a representative.
  change (((castLpₗᵢ (𝕜 := ℂ) (Measure.restrict_univ (μ := μ)))
      (extendByZeroLpₗᵢ ℂ μ hs (Set.subset_univ s) F) : Lp ℂ 2 μ) : α → ℂ) x = _
  rw [coeFn_castLpₗᵢ, hx]

/-- **Restriction**, on representatives: an ambient `L²` class restricts to an `L²` class for the
restricted measure.

Only used to feed the density argument, so it is not packaged as a map. -/
noncomputable def restrictLp (μ : Measure α) (s : Set α) (g : Lp ℂ 2 μ) :
    Lp ℂ 2 (μ.restrict s) :=
  ((Lp.memLp g).restrict s).toLp (g : α → ℂ)

/-- Restriction, on representatives: the restricted class is represented by the same function. -/
theorem coeFn_restrictLp (μ : Measure α) (s : Set α) (g : Lp ℂ 2 μ) :
    (restrictLp μ s g : α → ℂ) =ᵐ[μ.restrict s] (g : α → ℂ) :=
  MemLp.coeFn_toLp _

/-- The extension of the restriction of `g` is the indicator of `g`. -/
theorem coeFn_extendLp_restrictLp (μ : Measure α) (hs : MeasurableSet s) (g : Lp ℂ 2 μ) :
    (extendLp μ hs (restrictLp μ s g) : α → ℂ) =ᵐ[μ] s.indicator (g : α → ℂ) :=
  (coeFn_extendLp μ hs _).trans (indicator_ae_eq_of_restrict hs (coeFn_restrictLp μ s g))

end Indicator

section Orthogonality

/-- **Extensions from disjoint sets are orthogonal.**  Their representatives have disjoint
supports, so the integrand of the inner product vanishes pointwise. -/
theorem inner_extendLp_eq_zero_of_disjoint (μ : Measure α) (hs : MeasurableSet s)
    (ht : MeasurableSet t) (hst : Disjoint s t) (F : Lp ℂ 2 (μ.restrict s))
    (G : Lp ℂ 2 (μ.restrict t)) : ⟪extendLp μ hs F, extendLp μ ht G⟫_ℂ = 0 := by
  rw [L2.inner_def]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [coeFn_extendLp μ hs F, coeFn_extendLp μ ht G] with x h1 h2
  rw [Pi.zero_apply, h1, h2]
  by_cases hxs : x ∈ s
  · have hxt : x ∉ t := Set.disjoint_left.mp hst hxs
    simp [hxt]
  · simp [hxs]

/-- **The indicator is a self-adjoint idempotent**, in the only form needed here: the inner
product of `1_s g` with `g` equals its inner product with itself. -/
theorem inner_extendLp_restrictLp_self (μ : Measure α) (hs : MeasurableSet s) (g : Lp ℂ 2 μ) :
    ⟪extendLp μ hs (restrictLp μ s g), g⟫_ℂ
      = ⟪extendLp μ hs (restrictLp μ s g), extendLp μ hs (restrictLp μ s g)⟫_ℂ := by
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_extendLp_restrictLp μ hs g] with x hx
  rw [hx]
  by_cases hxs : x ∈ s
  · simp [hxs]
  · simp [hxs]

/-- **A vector orthogonal to the range of an extension vanishes on that set.** -/
theorem indicator_ae_eq_zero_of_inner_eq_zero (μ : Measure α) (hs : MeasurableSet s)
    {g : Lp ℂ 2 μ} (h : ∀ F : Lp ℂ 2 (μ.restrict s), ⟪extendLp μ hs F, g⟫_ℂ = 0) :
    s.indicator (g : α → ℂ) =ᵐ[μ] 0 := by
  have hzero : extendLp μ hs (restrictLp μ s g) = 0 :=
    inner_self_eq_zero.mp ((inner_extendLp_restrictLp_self μ hs g).symm.trans
      (h (restrictLp μ s g)))
  refine (coeFn_extendLp_restrictLp μ hs g).symm.trans ?_
  rw [hzero]
  exact Lp.coeFn_zero ℂ 2 μ

end Orthogonality

section Partition

variable {ι : Type*} [Countable ι] {B : ι → Set α}

/-- **`L²` of a measure is the Hilbert sum of the `L²` spaces of its restrictions to the pieces
of a countable measurable partition.**

The partition hypotheses are the weakest possible: the pieces are measurable and pairwise
disjoint, and what they miss is null. -/
theorem isHilbertSum_extendLp (μ : Measure α) (hB : ∀ i, MeasurableSet (B i))
    (hdisj : Pairwise fun i j => Disjoint (B i) (B j)) (hcover : μ (⋃ i, B i)ᶜ = 0) :
    IsHilbertSum ℂ (fun i => Lp ℂ 2 (μ.restrict (B i))) (fun i => extendLp μ (hB i)) := by
  refine IsHilbertSum.mk (𝕜 := ℂ) (fun i j hij F G => ?_) ?_
  · exact inner_extendLp_eq_zero_of_disjoint μ (hB i) (hB j) (hdisj hij) F G
  · refine (Submodule.topologicalClosure_eq_top_iff.mpr ?_).ge
    rw [Submodule.eq_bot_iff]
    intro g hg
    have hgi : ∀ i, (B i).indicator (g : α → ℂ) =ᵐ[μ] 0 := by
      intro i
      refine indicator_ae_eq_zero_of_inner_eq_zero μ (hB i) fun F => ?_
      refine (Submodule.mem_orthogonal _ g).mp hg _ ?_
      exact le_iSup (fun i => LinearMap.range (extendLp μ (hB i)).toLinearMap) i
        ⟨F, rfl⟩
    have hnull : ∀ i, μ (B i ∩ {x | (g : α → ℂ) x ≠ 0}) = 0 := by
      intro i
      have := hgi i
      rw [Filter.EventuallyEq, ae_iff] at this
      refine measure_mono_null (fun x hx => ?_) this
      have hxB : x ∈ B i := hx.1
      have hxg : (g : α → ℂ) x ≠ 0 := hx.2
      have hne : ¬ (B i).indicator (g : α → ℂ) x = (0 : α → ℂ) x := by
        rw [Set.indicator_of_mem hxB]
        exact hxg
      exact hne
    refine Lp.ext ?_
    refine (Filter.EventuallyEq.trans ?_ (Lp.coeFn_zero ℂ 2 μ).symm)
    rw [Filter.EventuallyEq, ae_iff]
    refine measure_mono_null
      (show {x | ¬ (g : α → ℂ) x = (0 : α → ℂ) x}
        ⊆ (⋃ i, B i)ᶜ ∪
            ⋃ i, B i ∩ {x | (g : α → ℂ) x ≠ 0} from fun x hx => ?_) ?_
    · by_cases hxU : x ∈ ⋃ i, B i
      · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxU
        exact Or.inr (Set.mem_iUnion.mpr ⟨i, hi, by simpa using hx⟩)
      · exact Or.inl hxU
    · exact measure_union_null hcover (measure_iUnion_null hnull)

end Partition

section Multiplication

/-- **Extension by zero intertwines the multiplication operators.**  The symbol is the same
function on both sides; restricting it to `s` is what the restricted measure sees. -/
theorem extendLp_mulLp (μ : Measure α) (hs : MeasurableSet s) {g : α → ℂ} (hg : Measurable g)
    {C : ℝ} (hgC : ∀ x, ‖g x‖ ≤ C) (F : Lp ℂ 2 (μ.restrict s)) :
    extendLp μ hs (mulLp (μ.restrict s) hg hgC F) = mulLp μ hg hgC (extendLp μ hs F) := by
  refine Lp.ext ?_
  filter_upwards [coeFn_extendLp μ hs (mulLp (μ.restrict s) hg hgC F),
    indicator_ae_eq_of_restrict (μ := μ) hs (coeFn_mulLp (μ.restrict s) hg hgC F),
    coeFn_mulLp μ hg hgC (extendLp μ hs F), coeFn_extendLp μ hs F] with x h1 h2 h3 h4
  rw [h1, h2, h3, h4]
  by_cases hxs : x ∈ s <;> simp [hxs]

end Multiplication

section Star

omit [MeasurableSpace α] in
/-- Pointwise conjugation passes through an indicator, because it fixes zero. -/
theorem star_indicator_apply (s : Set α) (u : α → ℂ) (x : α) :
    star (s.indicator u x) = s.indicator (star u) x := by
  by_cases hxs : x ∈ s
  · rw [Set.indicator_of_mem hxs, Set.indicator_of_mem hxs, Pi.star_apply]
  · rw [Set.indicator_of_notMem hxs, Set.indicator_of_notMem hxs, star_zero]

/-- **Extension by zero is `star`-equivariant.**  Conjugation fixes the zero that the extension
inserts, so it commutes with the indicator. -/
theorem star_extendLp (μ : Measure α) (hs : MeasurableSet s) (F : Lp ℂ 2 (μ.restrict s)) :
    star (extendLp μ hs F) = extendLp μ hs (star F) := by
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_star (extendLp μ hs F), coeFn_extendLp μ hs F,
    coeFn_extendLp μ hs (star F),
    indicator_ae_eq_of_restrict (μ := μ) hs (Lp.coeFn_star F)] with x h1 h2 h3 h4
  calc ((star (extendLp μ hs F) : Lp ℂ 2 μ) : α → ℂ) x
      = star (s.indicator (F : α → ℂ) x) := by rw [h1, Pi.star_apply, h2]
    _ = s.indicator (star (F : α → ℂ)) x := star_indicator_apply s _ x
    _ = s.indicator ((star F : Lp ℂ 2 (μ.restrict s)) : α → ℂ) x := (h4 ▸ rfl)
    _ = ((extendLp μ hs (star F) : Lp ℂ 2 μ) : α → ℂ) x := h3.symm

/-- **Restriction is `star`-equivariant**: both sides are represented by the same function. -/
theorem star_restrictLp (μ : Measure α) (s : Set α) (g : Lp ℂ 2 μ) :
    star (restrictLp μ s g) = restrictLp μ s (star g) := by
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_star (restrictLp μ s g), coeFn_restrictLp μ s g,
    coeFn_restrictLp μ s (star g), ae_restrict_of_ae (Lp.coeFn_star g)] with x h1 h2 h3 h4
  calc ((star (restrictLp μ s g) : Lp ℂ 2 (μ.restrict s)) : α → ℂ) x
      = star ((g : α → ℂ) x) := by rw [h1, Pi.star_apply, h2]
    _ = ((star g : Lp ℂ 2 μ) : α → ℂ) x := by rw [h4, Pi.star_apply]
    _ = ((restrictLp μ s (star g) : Lp ℂ 2 (μ.restrict s)) : α → ℂ) x := h3.symm

end Star

end TauCeti
