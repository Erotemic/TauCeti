/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import TauCeti.MeasureTheory.Function.Lp.CompMeasurePreservingEquiv
public import TauCeti.MeasureTheory.Function.Lp.Multiplication

/-!
# L² transport along measurable embeddings and relabellings

Mathlib supplies the composition isometry `MeasureTheory.Lp.compMeasurePreservingₗᵢ`.
TauCeti already supplies `MeasureTheory.Lp.compMeasurePreservingₗᵢEquiv` for maps
inverse almost everywhere. This module only adds the surjectivity and equivalence for
measurable embeddings, and laws intertwining composition with multiplication operators
and complex conjugation.
-/

public section

open MeasureTheory

open scoped ENNReal

namespace TauCeti

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable {μ : Measure α} {ν : Measure β} {f : α → β}


section Comp

/-- Representatives of Mathlib's measure-preserving composition linear isometry. -/
private theorem coeFn_compMeasurePreserving_isometry (hf : MeasurePreserving f μ ν)
    (F : Lp ℂ 2 ν) :
    ((Lp.compMeasurePreservingₗᵢ ℂ f hf) F : α → ℂ) =ᵐ[μ] fun x => F (f x) := by
  rw [Lp.compMeasurePreservingₗᵢ_apply]
  simpa only [Function.comp_def] using (Lp.coeFn_compMeasurePreserving F hf)

/-- A measurable map is measure preserving onto its own pushforward.  Named so that the
pushforward unitary below has a stable proof term to refer to. -/
theorem measurePreserving_of_measurableEmbedding {e : α → β} (he : MeasurableEmbedding e)
    (ρ : Measure α) : MeasurePreserving e ρ (Measure.map e ρ) :=
  ⟨he.measurable, rfl⟩

/-- Composition with a measurable embedding is surjective onto `L²` of the source: every
square-integrable class extends measurably to the target. -/
theorem surjective_compMeasurePreserving_of_measurableEmbedding
    {e : α → β} (he : MeasurableEmbedding e) (ρ : Measure α) :
    Function.Surjective
      (Lp.compMeasurePreservingₗᵢ (E := ℂ) (p := (2 : ENNReal)) ℂ e
        (measurePreserving_of_measurableEmbedding he ρ)) := by
  have hpres : MeasurePreserving e ρ (Measure.map e ρ) :=
    measurePreserving_of_measurableEmbedding he ρ
  intro F
  obtain ⟨f, hfmeas, hfae⟩ : ∃ f : α → ℂ, Measurable f ∧ (F : α → ℂ) =ᵐ[ρ] f :=
    ⟨(Lp.aestronglyMeasurable F).mk (F : α → ℂ),
      (Lp.aestronglyMeasurable F).stronglyMeasurable_mk.measurable,
      (Lp.aestronglyMeasurable F).ae_eq_mk⟩
  have hge : (Function.extend e f (0 : β → ℂ)) ∘ e = f :=
    funext fun x => he.injective.extend_apply f 0 x
  have hgmem : MemLp (Function.extend e f (0 : β → ℂ)) 2 (Measure.map e ρ) := by
    rw [he.memLp_map_measure_iff, hge]
    exact (Lp.memLp F).ae_eq hfae
  refine ⟨hgmem.toLp (Function.extend e f (0 : β → ℂ)), Lp.ext ?_⟩
  filter_upwards [coeFn_compMeasurePreserving_isometry hpres
    (hgmem.toLp (Function.extend e f (0 : β → ℂ))),
    hpres.quasiMeasurePreserving.ae (MemLp.coeFn_toLp hgmem), hfae] with x h1 h2 h3
  rw [h1, h2, h3]
  simpa using congrFun hge x

/-- **Transport along a measurable embedding.**  For a measurable embedding `e`, composition with
`e` is a unitary `L²(map e ρ) ≃ₗᵢ[ℂ] L²(ρ)`.

Injectivity is what makes it surjective: a square-integrable class on the source extends to the
target by `Function.extend`, measurably, because a measurable embedding carries measurable sets
to measurable sets.  This is the form used to move the scalar spectral measures off the
`spectrum` subtype and onto `ℂ`, where the models of two different operators can be compared. -/
noncomputable def embLpEquiv {e : α → β} (he : MeasurableEmbedding e) (ρ : Measure α) :
    Lp ℂ 2 (Measure.map e ρ) ≃ₗᵢ[ℂ] Lp ℂ 2 ρ :=
  LinearIsometryEquiv.ofSurjective
    (Lp.compMeasurePreservingₗᵢ ℂ e (measurePreserving_of_measurableEmbedding he ρ))
    (surjective_compMeasurePreserving_of_measurableEmbedding he ρ)

/-- The pushforward unitary is composition with the embedding; stated for the same reason as
`Lp.compMeasurePreservingₗᵢ_apply`. -/
@[simp]
theorem embLpEquiv_apply {e : α → β} (he : MeasurableEmbedding e) (ρ : Measure α)
    (F : Lp ℂ 2 (Measure.map e ρ)) :
    embLpEquiv he ρ F =
      (Lp.compMeasurePreservingₗᵢ ℂ e (measurePreserving_of_measurableEmbedding he ρ)) F :=
  (rfl)

/-- **The intertwining law.**  Composition with `f` carries multiplication by `G` on `L²(ν)` to
multiplication by `G ∘ f` on `L²(μ)`.

When `f` fixes the coordinate the symbol is unchanged -- `G ∘ f = G` -- and the law becomes the
statement that the unitary commutes with the multiplication operator. -/
theorem compMeasurePreserving_mulLp (hf : MeasurePreserving f μ ν)
    {G : β → ℂ} (hG : Measurable G) {C : ℝ}
    (hGC : ∀ y, ‖G y‖ ≤ C) (F : Lp ℂ 2 ν) :
    (Lp.compMeasurePreservingₗᵢ ℂ f hf) (mulLp ν hG hGC F)
      = mulLp μ (hG.comp hf.measurable) (fun x => hGC (f x))
          ((Lp.compMeasurePreservingₗᵢ ℂ f hf) F) := by
  refine Lp.ext ?_
  filter_upwards [coeFn_compMeasurePreserving_isometry hf (mulLp ν hG hGC F),
    hf.quasiMeasurePreserving.ae (coeFn_mulLp ν hG hGC F),
    coeFn_mulLp μ (hG.comp hf.measurable) (fun x => hGC (f x))
      ((Lp.compMeasurePreservingₗᵢ ℂ f hf) F),
    coeFn_compMeasurePreserving_isometry hf F] with x h1 h2 h3 h4
  simp only [Function.comp_apply] at h1 h2 h3 h4 ⊢
  rw [h1, h2, h3, h4]

/-- **The pushforward unitary intertwines the multiplication operators.**  The symbol on the
source is the symbol on the target composed with the embedding. -/
theorem embLpEquiv_mulLp {e : α → β} (he : MeasurableEmbedding e) (ρ : Measure α)
    {G : β → ℂ}
    (hG : Measurable G) {C : ℝ} (hGC : ∀ y, ‖G y‖ ≤ C) (F : Lp ℂ 2 (Measure.map e ρ)) :
    embLpEquiv he ρ (mulLp (Measure.map e ρ) hG hGC F)
      = mulLp ρ (hG.comp he.measurable) (fun x => hGC (e x)) (embLpEquiv he ρ F) :=
  compMeasurePreserving_mulLp (measurePreserving_of_measurableEmbedding he ρ) hG hGC F

/-- The inverse of the pushforward unitary intertwines the multiplication operators the other
way. -/
theorem embLpEquiv_symm_mulLp {e : α → β} (he : MeasurableEmbedding e) (ρ : Measure α)
    {G : β → ℂ} (hG : Measurable G) {C : ℝ}
    (hGC : ∀ y, ‖G y‖ ≤ C) (F : Lp ℂ 2 ρ) :
    (embLpEquiv he ρ).symm (mulLp ρ (hG.comp he.measurable) (fun x => hGC (e x)) F)
      = mulLp (Measure.map e ρ) hG hGC ((embLpEquiv he ρ).symm F) := by
  refine (embLpEquiv he ρ).injective ?_
  rw [LinearIsometryEquiv.apply_symm_apply, embLpEquiv_mulLp,
    LinearIsometryEquiv.apply_symm_apply]

end Comp

section Star

/-- **Relabelling is `star`-equivariant.**  Composition acts on the argument and `star` acts on
the value, so the two commute with nothing to prove beyond moving the representatives past each
other.

This is what carries the real (`star`-fixed) part of an `L²` space along the relabelling step of
the multiplicity model: `TauCeti.starFixedSubmodule` is a `star`-fixed set, so an equivariant
isometry maps it into the corresponding one. -/
theorem star_compMeasurePreserving (hf : MeasurePreserving f μ ν) (F : Lp ℂ 2 ν) :
    star ((Lp.compMeasurePreservingₗᵢ ℂ f hf) F) =
      (Lp.compMeasurePreservingₗᵢ ℂ f hf) (star F) := by
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_star ((Lp.compMeasurePreservingₗᵢ ℂ f hf) F),
    coeFn_compMeasurePreserving_isometry hf F,
    coeFn_compMeasurePreserving_isometry hf (star F),
    hf.quasiMeasurePreserving.ae (Lp.coeFn_star F)] with x h1 h2 h3 h4
  calc ((star ((Lp.compMeasurePreservingₗᵢ ℂ f hf) F) : Lp ℂ 2 μ) : α → ℂ) x
      = star ((F : β → ℂ) (f x)) := by rw [h1, Pi.star_apply, h2]
    _ = ((star F : Lp ℂ 2 ν) : β → ℂ) (f x) := by rw [h4, Pi.star_apply]
    _ = (((Lp.compMeasurePreservingₗᵢ ℂ f hf) (star F) : Lp ℂ 2 μ) : α → ℂ) x :=
      h3.symm

/-- **The pushforward unitary is `star`-equivariant.** -/
theorem star_embLpEquiv {e : α → β} (he : MeasurableEmbedding e) (ρ : Measure α)
    (F : Lp ℂ 2 (Measure.map e ρ)) :
    star (embLpEquiv he ρ F) = embLpEquiv he ρ (star F) :=
  star_compMeasurePreserving (measurePreserving_of_measurableEmbedding he ρ) F

/-- **The inverse of the pushforward unitary is `star`-equivariant**, which follows from
`star_embLpEquiv` by applying the unitary to both sides. -/
theorem star_embLpEquiv_symm {e : α → β} (he : MeasurableEmbedding e) (ρ : Measure α)
    (F : Lp ℂ 2 ρ) :
    star ((embLpEquiv he ρ).symm F) = (embLpEquiv he ρ).symm (star F) := by
  refine (embLpEquiv he ρ).injective ?_
  rw [LinearIsometryEquiv.apply_symm_apply, ← star_embLpEquiv,
    LinearIsometryEquiv.apply_symm_apply]

end Star

end TauCeti
