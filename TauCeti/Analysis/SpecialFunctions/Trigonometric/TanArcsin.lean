/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# The sine-to-tangent transfer `tan ∘ arcsin`

Davis--Kahan tangent estimates convert each directed sine singular value `s` into the
tangent `tan (arcsin s) = s / √(1 - s²)` of the same angle. This module supplies the
nonnegativity and order properties of this scalar transfer.

## Main results

* `Real.tan_arcsin_nonneg`: nonnegative inputs give nonnegative tangent values.
* `Real.strictMonoOn_tan_arcsin`: the transfer is strictly increasing on `(-1, 1)`.
* `Real.tan_arcsin_le_tan_arcsin`: the transfer preserves inequalities in `(-1, 1)`.

## Provenance

Ported from `ForTauCeti/Analysis/SpecialFunctions/TanArcsin.lean` in the
[DKPS formalization](https://github.com/AIQ-Kitware/aiq-dkps-formalization),
released under the Apache 2.0 license.
-/

public section

namespace Real

/-- The sine-to-tangent transfer is nonnegative on nonnegative inputs. -/
theorem tan_arcsin_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ tan (arcsin t) := by
  rw [tan_arcsin]
  exact div_nonneg ht (sqrt_nonneg _)

/-- The sine-to-tangent transfer is strictly increasing on `(-1, 1)`. -/
theorem strictMonoOn_tan_arcsin :
    StrictMonoOn (fun s : ℝ => tan (arcsin s)) (Set.Ioo (-1) 1) := by
  intro a ha b hb hab
  exact strictMonoOn_tan
    ⟨neg_pi_div_two_lt_arcsin.2 ha.1, arcsin_lt_pi_div_two.2 ha.2⟩
    ⟨neg_pi_div_two_lt_arcsin.2 hb.1, arcsin_lt_pi_div_two.2 hb.2⟩
    (strictMonoOn_arcsin ⟨ha.1.le, ha.2.le⟩ ⟨hb.1.le, hb.2.le⟩ hab)

/-- The sine-to-tangent transfer preserves inequalities between inputs in `(-1, 1)`. -/
theorem tan_arcsin_le_tan_arcsin {a b : ℝ}
    (ha : -1 < a) (hab : a ≤ b) (hb : b < 1) :
    tan (arcsin a) ≤ tan (arcsin b) :=
  strictMonoOn_tan_arcsin.monotoneOn
    ⟨ha, hab.trans_lt hb⟩ ⟨ha.trans_le hab, hb⟩ hab

end Real
