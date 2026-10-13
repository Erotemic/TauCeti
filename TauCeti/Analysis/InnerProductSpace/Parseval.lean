/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Parseval's identity in norm-square form

Mathlib states Parseval's identity in polarized, `𝕜`-valued form:
`HilbertBasis.hasSum_inner_mul_inner` gives `∑' i, ⟪x, b i⟫ * ⟪b i, y⟫ = ⟪x, y⟫`. This file states
the diagonal, real-valued form `‖x‖² = ∑' i, ‖⟪b i, x⟫‖²`. The two differ in the type of their
summands, so the real-valued form is not a substitution instance of the polarized one.

The real-valued form is the shape consumers state coefficient decay in, and it is the
`OrthogonalL2Bases` roadmap's Part A3 acceptance criterion `‖f‖² = ∑' n, ‖⟪ψₙ, f⟫‖²`; its instance
for the Hermite basis is `TauCeti.tsum_norm_sq_inner_hermiteFunctionLp`.

## Main declarations

* `HilbertBasis.hasSum_norm_sq_inner` — Parseval in norm-square form, as a `HasSum` statement.
* `HilbertBasis.tsum_enorm_inner_sq` - the extended-real version.
* `HilbertBasis.tsum_norm_sq_inner` — the same identity as an equation between a `tsum` and `‖x‖²`.
-/

open scoped ENNReal InnerProductSpace

public section

namespace TauCeti

variable {ι : Type*} {𝕜 : Type*} {E : Type*}
variable [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **Parseval's identity, norm-square form.** The squared coordinates of `x` in a Hilbert basis
sum to `‖x‖²`, as a convergent series of real numbers. -/
theorem _root_.HilbertBasis.hasSum_norm_sq_inner (b : _root_.HilbertBasis ι 𝕜 E) (x : E) :
    HasSum (fun i => ‖inner 𝕜 (b i) x‖ ^ 2) (‖x‖ ^ 2) := by
  have h := lp.hasSum_norm (p := 2) (by norm_num) (b.repr x)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, b.repr_apply_apply, b.repr.norm_map] using h

/-- **Parseval's identity, norm-square form** (`tsum` version of
`HilbertBasis.hasSum_norm_sq_inner`). -/
theorem _root_.HilbertBasis.tsum_norm_sq_inner (b : _root_.HilbertBasis ι 𝕜 E) (x : E) :
    ∑' i : ι, ‖inner 𝕜 (b i) x‖ ^ 2 = ‖x‖ ^ 2 :=
  (b.hasSum_norm_sq_inner x).tsum_eq

/-- The squared coordinate family of a vector is summable. -/
theorem _root_.HilbertBasis.summable_norm_sq_inner (b : _root_.HilbertBasis ι 𝕜 E) (x : E) :
    Summable fun i => ‖inner 𝕜 (b i) x‖ ^ 2 :=
  (b.hasSum_norm_sq_inner x).summable

/-- **Parseval's identity** in `ℝ≥0∞`.  Unlike the real form this is an unconditional
equation between extended reals, which is what lets it be substituted under a `tsum`
without a summability hypothesis. -/
theorem _root_.HilbertBasis.tsum_enorm_inner_sq (b : HilbertBasis ι 𝕜 E) (v : E) :
    ∑' i, ‖⟪b i, v⟫_𝕜‖ₑ ^ 2 = ‖v‖ₑ ^ 2 := by
  have hnn : HasSum (fun i => ‖⟪b i, v⟫_𝕜‖₊ ^ 2) (‖v‖₊ ^ 2) := by
    rw [← NNReal.hasSum_coe]
    push_cast
    exact b.hasSum_norm_sq_inner v
  simp only [enorm_eq_nnnorm, ← ENNReal.coe_pow]
  rw [← ENNReal.coe_tsum hnn.summable, hnn.tsum_eq]

end TauCeti
