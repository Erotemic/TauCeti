/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Opus 5, GPT-6
-/
module

public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Diagonal
import Mathlib.Analysis.InnerProductSpace.l2Space
public import TauCeti.Analysis.OperatorIdeal.Family.SymmetricGauge

/-!
# Faithfulness of induced symmetric operator-ideal families

Roadmap: OperatorIdeals, OI-B72.

The extension of a symmetric gauge to antitone sequences is determined by its
induced operator-ideal family.  The proof reuses TauCeti's existing diagonal
realization of every antitone sequence of nonnegative real numbers.  It does
not introduce a second diagonal-operator construction or a second ideal family.

An antitone `ENNReal`-valued sequence is either bounded by its finite initial
value, and hence realized by a diagonal operator on complex `ℓ²`, or its
initial value is `⊤`, forcing both extended gauges to equal `⊤`.

Adapted from `ForTauCeti/Analysis/OperatorIdeal/Family/SymmetricGauge.lean`
in the Kitware Davis--Kahan formalization (Apache-2.0).
-/

public section

open scoped ENNReal NNReal lp

namespace TauCeti
namespace SymmetricGauge

/-- **OI-B72.** Two symmetric gauges that induce the same complex operator-ideal
family have the same extensions on every antitone `ENNReal`-valued sequence. -/
theorem extend_eq_of_operatorIdealFamily_eq
    {Φ Ψ : SymmetricGauge}
    (h : Φ.operatorIdealFamily.{0, 0, 0} ℂ = Ψ.operatorIdealFamily.{0, 0, 0} ℂ)
    {a : ℕ → ℝ≥0∞} (ha : Antitone a) :
    Φ.extend a = Ψ.extend a := by
  classical
  by_cases htop : a 0 = ⊤
  · have htop_ext (Θ : SymmetricGauge) : Θ.extend a = ⊤ := by
      apply top_le_iff.mp
      calc
        ⊤ = a 0 := htop.symm
        _ ≤ ⨆ n, a n := le_iSup (fun n => a n) 0
        _ ≤ Θ.extend a := Θ.iSup_le_extend a
    rw [htop_ext Φ, htop_ext Ψ]
  · have hfinite (n : ℕ) : a n ≠ ⊤ :=
      ne_top_of_le_ne_top htop (ha (Nat.zero_le n))
    let c : ℕ → ℝ≥0 := fun n => (a n).toNNReal
    have hc (n : ℕ) : (c n : ℝ≥0∞) = a n :=
      ENNReal.coe_toNNReal (hfinite n)
    have hcanti : Antitone c := by
      intro i j hij
      apply ENNReal.coe_le_coe.mp
      simpa only [hc] using ha hij
    obtain ⟨d, hd⟩ :=
      lp.exists_singularValue_diagonalCLM_eq (p := 2) (𝕜 := ℂ) hcanti
    let T : ℓ²(ℕ, ℂ) →L[ℂ] ℓ²(ℕ, ℂ) := lp.diagonalCLM d
    have hs : (fun n => (T.singularValue n : ℝ≥0∞)) = a := by
      funext n
      change ((lp.diagonalCLM (p := 2) d).singularValue n : ℝ≥0∞) = a n
      rw [congrFun hd n]
      exact hc n
    have heq := congrArg
      (fun F : OperatorIdealFamily.{0, 0, 0} ℂ => F.gauge T) h
    simp only [operatorIdealFamily_gauge] at heq
    simpa only [opGauge_def, hs] using heq

end SymmetricGauge
end TauCeti
