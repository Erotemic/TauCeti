/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import TauCeti.MeasureTheory.Integral.ExpDecay

/-!
# Even integrable functions on the real line

An even function with values in a normed additive commutative group is integrable on `ℝ` if and
only if it is integrable on the positive half-line. Negation preserves Lebesgue measure, and the
origin is negligible for the half-line decomposition.
-/

public section

namespace MeasureTheory


/-- An even function is integrable on the line iff it is integrable on the
positive half-line. -/
theorem integrable_iff_integrableOn_Ioi_of_even {E : Type*} [NormedAddCommGroup E] {g : ℝ → E}
    (heven : ∀ t, g (-t) = g t) :
    Integrable g ↔ IntegrableOn g (Set.Ioi 0) := by
  refine ⟨fun hg => hg.integrableOn, fun hg => ?_⟩
  have hIic : IntegrableOn g (Set.Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    have m : MeasurableEmbedding fun x : ℝ => -x :=
      (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp only [Function.comp_def, heven, Set.neg_preimage, Set.neg_Iic, neg_zero]
    exact Iff.mpr (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)) hg
  rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (0 : ℝ))]
  exact hIic.union hg

end MeasureTheory
