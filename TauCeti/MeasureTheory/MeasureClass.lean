/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# Equivalence of measure classes

Two measures are equivalent when they share null sets, i.e. each is absolutely continuous with
respect to the other. This relation is useful for spectral-multiplicity models: replacing a
measure by an equivalent measure does not alter the unitary class of its multiplication operators.

`MeasureEquiv_def`, `MeasureEquiv.of_absCont`, `MeasureEquiv.absCont_left`, and
`MeasureEquiv.absCont_right` give a stable public API. The restriction and density lemmas
connect equivalence of measure classes to Radon–Nikodym derivatives.
-/

public section

open MeasureTheory

open scoped ENNReal

namespace TauCeti

variable {α : Type*} [MeasurableSpace α] {μ ν ρ : Measure α}

/-- **Two measures are equivalent** when each is absolutely continuous with respect to the
other, i.e. they have the same null sets.

The characteristic theorem `MeasureEquiv_def` and the projection lemmas expose mutual absolute
continuity without unfolding the definition. -/
def MeasureEquiv (μ ν : Measure α) : Prop :=
  μ ≪ ν ∧ ν ≪ μ

/-- Characterization by mutual absolute continuity. -/
@[simp]
theorem MeasureEquiv_def (μ ν : Measure α) :
    MeasureEquiv μ ν ↔ μ ≪ ν ∧ ν ≪ μ := Iff.rfl

/-- Construct measure equivalence from mutual absolute continuity. -/
theorem MeasureEquiv.of_absCont (hμν : μ ≪ ν) (hνμ : ν ≪ μ) : MeasureEquiv μ ν :=
  (MeasureEquiv_def μ ν).2 ⟨hμν, hνμ⟩

/-- The first absolute-continuity projection. -/
theorem MeasureEquiv.absCont_left (h : MeasureEquiv μ ν) : μ ≪ ν :=
  ((MeasureEquiv_def μ ν).1 h).1

/-- The reverse absolute-continuity projection. -/
theorem MeasureEquiv.absCont_right (h : MeasureEquiv μ ν) : ν ≪ μ :=
  ((MeasureEquiv_def μ ν).1 h).2

/-- Measure equivalence is reflexive. -/
@[refl]
theorem MeasureEquiv.refl (μ : Measure α) : MeasureEquiv μ μ :=
  MeasureEquiv.of_absCont Measure.AbsolutelyContinuous.rfl Measure.AbsolutelyContinuous.rfl

/-- Measure equivalence is reflexive, with the measure implicit. -/
theorem MeasureEquiv.rfl : MeasureEquiv μ μ :=
  MeasureEquiv.refl μ

/-- Measure equivalence is symmetric. -/
@[symm]
theorem MeasureEquiv.symm (h : MeasureEquiv μ ν) : MeasureEquiv ν μ :=
  MeasureEquiv.of_absCont h.absCont_right h.absCont_left

/-- Measure equivalence is transitive. -/
theorem MeasureEquiv.trans (h : MeasureEquiv μ ν) (h' : MeasureEquiv ν ρ) : MeasureEquiv μ ρ :=
  MeasureEquiv.of_absCont (h.absCont_left.trans h'.absCont_left)
    (h'.absCont_right.trans h.absCont_right)

/-- Measure equivalence is an equivalence relation.  Proved at the point of definition so the
quotient by it -- the *measure class* proper -- can be formed later without disturbing any
consumer of the relation itself. -/
theorem measureEquiv_equivalence : Equivalence (@MeasureEquiv α _) where
  refl := MeasureEquiv.refl
  symm := MeasureEquiv.symm
  trans := MeasureEquiv.trans

/-- The setoid of measures under equivalence.  Its quotient is the type of **measure classes**. -/
def measureClassSetoid (α : Type*) [MeasurableSpace α] : Setoid (Measure α) where
  r := MeasureEquiv
  iseqv := measureEquiv_equivalence

/-- Two equivalent measures have the same null sets -- which is the relation unfolded, stated in
the form a call site usually wants. -/
theorem MeasureEquiv.measure_eq_zero_iff (h : MeasureEquiv μ ν) (s : Set α) :
    μ s = 0 ↔ ν s = 0 :=
  ⟨fun hs => h.absCont_right hs, fun hs => h.absCont_left hs⟩

/-- Equivalent measures have the same almost-everywhere filter. -/
theorem MeasureEquiv.ae_eq (h : MeasureEquiv μ ν) : (ae μ : Filter α) = ae ν :=
  le_antisymm h.absCont_left.ae_le h.absCont_right.ae_le

/-- Measure equivalence is preserved by restriction to a common set. -/
theorem MeasureEquiv.restrict (h : MeasureEquiv μ ν) (s : Set α) :
    MeasureEquiv (μ.restrict s) (ν.restrict s) :=
  MeasureEquiv.of_absCont (h.absCont_left.restrict s) (h.absCont_right.restrict s)

/-- Restricting one measure to two almost-equal sets gives literally the same measure, hence
equivalent ones.

This is what lets the multiplicity level sets of two operators be compared "up to a null set":
the models built from them are then built from *equal* measures. -/
theorem measureEquiv_restrict_congr {s t : Set α} (h : s =ᵐ[μ] t) :
    MeasureEquiv (μ.restrict s) (μ.restrict t) := by
  rw [Measure.restrict_congr_set h]

/-- **A density and the restriction to its support carry the same measure class.**

For measurable `f : α → ℝ≥0∞`, the measure `f · μ` and the restriction of `μ` to
`{x | f x ≠ 0}` have exactly the same null sets: a set is `f · μ`-null iff `f` vanishes
`μ`-almost everywhere on it, iff its intersection with the support of `f` is `μ`-null.

This is the step that turns a *dominated countable family* of measures into a family of
restrictions of a single measure: if every `μₙ` is absolutely continuous with respect to `ρ`
then `μₙ = ρ.withDensity (dμₙ/dρ)` is equivalent to `ρ.restrict {dμₙ/dρ ≠ 0}`, so all the
measures in the family become restrictions of the one measure `ρ` to Borel sets. -/
theorem measureEquiv_withDensity_restrict (μ : Measure α) {f : α → ℝ≥0∞} (hf : Measurable f) :
    MeasureEquiv (μ.withDensity f) (μ.restrict {x | f x ≠ 0}) := by
  have hmeas : MeasurableSet {x | f x ≠ 0} := (hf (measurableSet_singleton (0 : ℝ≥0∞))).compl
  have key : ∀ s : Set α, MeasurableSet s →
      (μ.withDensity f s = 0 ↔ μ.restrict {x | f x ≠ 0} s = 0) := by
    intro s hs
    have hrestrict : μ.restrict {x | f x ≠ 0} s = μ.restrict s {x | f x ≠ 0} := by
      rw [Measure.restrict_apply hs, Measure.restrict_apply hmeas, Set.inter_comm]
    rw [withDensity_apply _ hs, lintegral_eq_zero_iff hf, hrestrict]
    constructor
    · intro hzero
      rw [Filter.EventuallyEq, ae_iff] at hzero
      exact measure_mono_null (fun x hx => by simpa using hx) hzero
    · intro hzero
      rw [Filter.EventuallyEq, ae_iff]
      exact measure_mono_null (fun x hx => by simpa using hx) hzero
  exact MeasureEquiv.of_absCont
    (Measure.AbsolutelyContinuous.mk fun s hs hs0 => (key s hs).mpr hs0)
    (Measure.AbsolutelyContinuous.mk fun s hs hs0 => (key s hs).mp hs0)

/-- **Every measure absolutely continuous with respect to `ρ` is a restriction of `ρ`, up to
class.**  The set is the support of the Radon--Nikodym derivative.

This is `measureEquiv_withDensity_restrict` composed with `Measure.withDensity_rnDeriv_eq`, and
it is the form the multiplicity construction consumes. -/
theorem exists_measurableSet_measureEquiv_restrict (μ ρ : Measure α)
    [μ.HaveLebesgueDecomposition ρ] (h : μ ≪ ρ) :
    ∃ s : Set α, MeasurableSet s ∧ MeasureEquiv μ (ρ.restrict s) := by
  refine ⟨{x | μ.rnDeriv ρ x ≠ 0},
    (Measure.measurable_rnDeriv μ ρ (measurableSet_singleton 0)).compl, ?_⟩
  have := measureEquiv_withDensity_restrict ρ (Measure.measurable_rnDeriv μ ρ)
  rwa [Measure.withDensity_rnDeriv_eq μ ρ h] at this

end TauCeti
