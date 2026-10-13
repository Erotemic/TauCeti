/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Extended-real infinite-sum inequalities

Fatou's lower-semicontinuity inequality for nonnegative infinite sums and the
extended-real Minkowski inequality hold for arbitrary index types. Neither
requires a counting measure or summability of the summands.

* `ENNReal.tsum_le_liminf_tsum`: a pointwise filter limit obeys Fatou's bound.
* `ENNReal.tsum_rpow_add_le`: the `l^p` triangle inequality for `p >= 1`.
* `ENNReal.tsum_sq_add_rpow_le`: the square-power specialization.

Adapted from the Apache-2.0 DKPS formalization (Kitware, Inc.).
-/

open scoped ENNReal

public section

namespace ENNReal

/-- **Fatou's lemma for `tsum` over `ℝ≥0∞`.**  A pointwise limit of summands cannot have a
larger sum than the summands do in the limit.

No hypothesis on `ι` is needed and no measure is involved: `∑'` is the supremum of its finite
partial sums, a finite sum of convergent terms converges, and a partial sum is at most the
whole.

**Both the index type and the filter are arbitrary.**  The filter is not restricted to `ℕ`
because a consumer may approximate along `Finset.atTop` — the finite subsets of a Hilbert
basis, ordered by inclusion — where extracting a sequence would need countable choice and
buy nothing: the proof uses only `NeBot` and continuity of finite sums. -/
theorem tsum_le_liminf_tsum {ι : Type*} {β : Type*} {u : Filter β} [u.NeBot]
    {f : β → ι → ℝ≥0∞} {g : ι → ℝ≥0∞}
    (h : ∀ i, Filter.Tendsto (fun n => f n i) u (nhds (g i))) :
    ∑' i, g i ≤ Filter.liminf (fun n => ∑' i, f n i) u := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  have hfin : Filter.Tendsto (fun n => ∑ i ∈ s, f n i) u (nhds (∑ i ∈ s, g i)) :=
    tendsto_finsetSum _ fun i _ => h i
  calc ∑ i ∈ s, g i
      = Filter.liminf (fun n => ∑ i ∈ s, f n i) u := hfin.liminf_eq.symm
    _ ≤ Filter.liminf (fun n => ∑' i, f n i) u :=
        Filter.liminf_le_liminf
          (Filter.Eventually.of_forall fun _ => ENNReal.sum_le_tsum s)


variable {ι : Type*}

/-- **Minkowski's inequality in `ℓᵖ` for `tsum`, over `ℝ≥0∞`.**  Mathlib's
`ENNReal.Lp_add_le` is stated for a `Finset`, and its `tsum` counterpart exists only over
`ℝ≥0` (`NNReal.Lp_add_le_tsum`), where it carries summability hypotheses on both summands.
This is the `ℝ≥0∞` version, which needs no summability hypothesis at all — that is exactly
why the operator-ideal gauges are `ℝ≥0∞`-valued, since it lets their laws hold
unconditionally at non-members.

The proof is the standard supremum argument: the finite inequality bounds every partial sum
of the left side by the `p`-th power of the right side, and `∑'` is the supremum of its
partial sums. -/
theorem tsum_rpow_add_le {p : ℝ} (hp : 1 ≤ p) (f g : ι → ℝ≥0∞) :
    (∑' i, (f i + g i) ^ p) ^ p⁻¹ ≤
      (∑' i, f i ^ p) ^ p⁻¹ + (∑' i, g i ^ p) ^ p⁻¹ := by
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  set A := (∑' i, f i ^ p) ^ p⁻¹ with hA
  set B := (∑' i, g i ^ p) ^ p⁻¹ with hB
  have hpow : ∀ x : ℝ≥0∞, (x ^ p⁻¹) ^ p = x := fun x => by
    rw [← ENNReal.rpow_mul, inv_mul_cancel₀ hp0.ne', ENNReal.rpow_one]
  have key : ∀ s : Finset ι, ∑ i ∈ s, (f i + g i) ^ p ≤ (A + B) ^ p := by
    intro s
    have hfin := ENNReal.Lp_add_le (s := s) (f := f) (g := g) (p := p) hp
    rw [one_div] at hfin
    have hfA : (∑ i ∈ s, f i ^ p) ^ p⁻¹ ≤ A :=
      ENNReal.rpow_le_rpow (ENNReal.sum_le_tsum s) (by positivity)
    have hgB : (∑ i ∈ s, g i ^ p) ^ p⁻¹ ≤ B :=
      ENNReal.rpow_le_rpow (ENNReal.sum_le_tsum s) (by positivity)
    calc ∑ i ∈ s, (f i + g i) ^ p
        = ((∑ i ∈ s, (f i + g i) ^ p) ^ p⁻¹) ^ p := (hpow _).symm
      _ ≤ (A + B) ^ p :=
          ENNReal.rpow_le_rpow (hfin.trans (add_le_add hfA hgB)) hp0.le
  have hsum : ∑' i, (f i + g i) ^ p ≤ (A + B) ^ p :=
    ENNReal.tsum_eq_iSup_sum.trans_le (iSup_le key)
  calc (∑' i, (f i + g i) ^ p) ^ p⁻¹
      ≤ ((A + B) ^ p) ^ p⁻¹ := ENNReal.rpow_le_rpow hsum (by positivity)
    _ = A + B := by rw [← ENNReal.rpow_mul, mul_inv_cancel₀ hp0.ne', ENNReal.rpow_one]

/-- **Minkowski's inequality at `p = 2` for `tsum`**, the instance the Hilbert--Schmidt
energy uses.  Stated separately because its consumers carry the `^ 2` in `ℕ`-power form. -/
theorem tsum_sq_add_rpow_le (f g : ι → ℝ≥0∞) :
    (∑' i, (f i + g i) ^ 2) ^ (2 : ℝ)⁻¹ ≤
      (∑' i, f i ^ 2) ^ (2 : ℝ)⁻¹ + (∑' i, g i ^ 2) ^ (2 : ℝ)⁻¹ := by
  simpa only [← ENNReal.rpow_two] using tsum_rpow_add_le (p := 2) one_le_two f g


end ENNReal

end
