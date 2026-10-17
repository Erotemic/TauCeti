/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5, qwen3.8-27b-dbirks-hyperqwen-huge
-/
/-
Adapted from: Spectra (https://github.com/adambornemann-glitch/Spectra),
  `Spectra/ProjValMeasure/Basic.lean` at commit
  `8dbaaf6728d1342ae16acf79fd7eef7c59b37e63`.
Copyright (c) 2026 Spectra Formalization Project.
Authors: Adam Bornemann
Released under the Apache 2.0 license.
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.MeasureTheory.Measure.Basic
public import Mathlib.MeasureTheory.Measure.CompleteLattice
public import Mathlib.MeasureTheory.Measure.Continuity
public import Mathlib.MeasureTheory.Measure.Filter
public import Mathlib.MeasureTheory.Measure.Interval
public import Mathlib.MeasureTheory.Measure.Module
public import Mathlib.MeasureTheory.Measure.OuterMeasure
public import Mathlib.MeasureTheory.Measure.Sum
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.Measure.NullMeasurable
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Projection-valued measures

A projection-valued measure on the measurable sets of an arbitrary measurable
space `X`, acting on a complex Hilbert space `H`.

The finite diagonal scalar measures `diag ξ` are fields of the structure,
related to the operator field by `inner_proj`. Countable additivity of these
scalar measures supplies strong countable additivity of the projections.
Idempotence, self-adjointness, positivity, and finite additivity are proved
from the structure's laws.

## Main declarations

* `ProjValMeasure X H`: the structure — a map `proj` from measurable sets to
  operators, the diagonal measures `diag : H → Measure X`, the weld
  `inner_proj`, the normalization `proj_univ : P(X) = 1`, and the
  multiplicativity law `proj_inter`.
* `proj_idem`, `isSelfAdjoint_proj`, `isPositive_proj`, `proj_mul_eq_left_of_subset`,
  `proj_range_mono`, `proj_union`, `proj_compl`, `norm_proj_apply_le`:
  the classical PVM laws, recovered from the structure.
* `tendsto_sum_proj_of_pairwise_disjoint`: strong countable additivity on a pairwise-disjoint
  measurable family.
* `ext_of_diag`, `ext_of_proj`, `ext_iff_diag`, `ext_iff_proj`: extensionality
  from either data field.

## References

* Adam Bornemann, *Spectra*, `Spectra/ProjValMeasure/Basic.lean`,
  https://github.com/adambornemann-glitch/Spectra
  (commit `8dbaaf6728d1342ae16acf79fd7eef7c59b37e63`).
* AIQ-Kitware, *DKPS formalization*,
  `ForTauCeti/Analysis/InnerProductSpace/ProjValMeasure/Basic.lean`,
  https://github.com/AIQ-Kitware/aiq-dkps-formalization.

-/

public section

open MeasureTheory Filter Function
open scoped InnerProduct InnerProductSpace ENNReal Topology

namespace TauCeti

variable {X : Type*} [MeasurableSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## The structure -/

/-- A **projection-valued measure** on the measurable sets of `X`, acting on a
complex Hilbert space `H`.

The diagonal scalar measures `diag ξ` are supplied as finite measures,
related to the projections by `inner_proj`. Idempotence, self-adjointness,
positivity, finite additivity, contraction, and strong countable additivity
follow from these laws. -/
structure ProjValMeasure (X : Type*) [MeasurableSpace X] (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- The projection assigned to each measurable set. -/
  proj : ∀ B : Set X, MeasurableSet B → (H →L[ℂ] H)
  /-- The diagonal scalar measures, carried as data. -/
  diag : H → Measure X
  /-- Each diagonal measure is finite (its mass is `‖ξ‖ ^ 2`, by `diag_univ_toReal`). -/
  diag_finite : ∀ ξ : H, IsFiniteMeasure (diag ξ)
  /-- The weld: diagonal matrix elements of the projections are the diagonal measures. -/
  inner_proj : ∀ (B : Set X) (hB : MeasurableSet B) (ξ : H),
    ⟪ξ, proj B hB ξ⟫_ℂ = (((diag ξ) B).toReal : ℂ)
  /-- The whole space carries the identity. -/
  proj_univ : proj Set.univ MeasurableSet.univ = ContinuousLinearMap.id ℂ H
  /-- Multiplicativity: intersection of sets is composition of projections. -/
  proj_inter : ∀ (B₁ B₂ : Set X) (hB₁ : MeasurableSet B₁) (hB₂ : MeasurableSet B₂),
    proj B₁ hB₁ * proj B₂ hB₂ = proj (B₁ ∩ B₂) (hB₁.inter hB₂)

namespace ProjValMeasure

/-! ## The classical axioms, recovered as theorems -/

/-- Every diagonal measure is finite, with total mass `‖ξ‖²`; unpacked from the
`diag_finite` field so instance search can use it. -/
instance instIsFiniteMeasureDiag (P : ProjValMeasure X H) (ξ : H) :
    IsFiniteMeasure (P.diag ξ) :=
  P.diag_finite ξ

/-- The projections do not depend on the measurability witness — proof
irrelevance: only the set matters. -/
lemma proj_congr (P : ProjValMeasure X H) {B₁ B₂ : Set X} (h : B₁ = B₂)
    (h₁ : MeasurableSet B₁) (h₂ : MeasurableSet B₂) :
    P.proj B₁ h₁ = P.proj B₂ h₂ := by
  subst h; rfl

/-- The projection of the empty measurable set is zero. -/
@[simp]
lemma proj_empty (P : ProjValMeasure X H) : P.proj ∅ MeasurableSet.empty = 0 := by
  refine ContinuousLinearMap.coe_injective ((ext_inner_map _ _).mp fun ξ => ?_)
  change ⟪P.proj ∅ MeasurableSet.empty ξ, ξ⟫_ℂ =
    ⟪(0 : H →L[ℂ] H) ξ, ξ⟫_ℂ
  rw [← inner_conj_symm (P.proj ∅ MeasurableSet.empty ξ) ξ,
    ← inner_conj_symm ((0 : H →L[ℂ] H) ξ) ξ,
    P.inner_proj, zero_apply, inner_zero_right, measure_empty]
  simp

/-- Every measurable-set projection is idempotent. -/
lemma proj_idem (P : ProjValMeasure X H) (B : Set X) (hB : MeasurableSet B) :
    P.proj B hB * P.proj B hB = P.proj B hB := by
  rw [P.proj_inter B B hB hB]
  exact P.proj_congr (Set.inter_self B) (hB.inter hB) hB

/-- Every measurable-set projection is self-adjoint. -/
lemma isSelfAdjoint_proj (P : ProjValMeasure X H) (B : Set X) (hB : MeasurableSet B) :
    IsSelfAdjoint (P.proj B hB) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  refine ContinuousLinearMap.coe_injective ((ext_inner_map _ _).mp fun ξ => ?_)
  change ⟪((P.proj B hB)†) ξ, ξ⟫_ℂ = ⟪P.proj B hB ξ, ξ⟫_ℂ
  rw [ContinuousLinearMap.adjoint_inner_left,
    ← inner_conj_symm (P.proj B hB ξ) ξ,
    P.inner_proj, Complex.conj_ofReal]

/-- For each measurable set `B`, the operator `P(B)` is positive. -/
theorem isPositive_proj (P : ProjValMeasure X H) (B : Set X) (hB : MeasurableSet B) :
    (P.proj B hB).IsPositive := by
  rw [ContinuousLinearMap.isPositive_def']
  constructor
  · exact P.isSelfAdjoint_proj B hB
  · intro ξ
    -- `reApplyInnerSelf` is `re ⟪T ξ, ξ⟫`; the weld gives `⟪ξ, T ξ⟫`, and its
    -- value is an embedded real, so flipping the slots by conjugation changes
    -- nothing — leaving the nonnegative real `toReal`:
    have hval : (⟪(P.proj B hB) ξ, ξ⟫_ℂ) = (((P.diag ξ) B).toReal : ℂ) := by
      -- flip the slots by conjugation, then the weld, then the real-ness of the
      -- embedded value:
      have hconj : (⟪(P.proj B hB) ξ, ξ⟫_ℂ) = star (⟪ξ, (P.proj B hB) ξ⟫_ℂ) := by
        simp
      have hslot : (⟪ξ, (P.proj B hB) ξ⟫_ℂ) = (((P.diag ξ) B).toReal : ℂ) :=
        P.inner_proj B hB ξ
      rw [hconj, hslot]
      simp
    rw [ContinuousLinearMap.reApplyInnerSelf, hval]
    simp

/-- For measurable `B ⊆ C`, the projection product `P(B) * P(C)` is `P(B)`. -/
theorem proj_mul_eq_left_of_subset (P : ProjValMeasure X H) {B C : Set X} (hBC : B ⊆ C)
    (hB : MeasurableSet B) (hC : MeasurableSet C) :
    P.proj B hB * P.proj C hC = P.proj B hB := by
  rw [P.proj_inter B C hB hC]
  -- `B ∩ C = B` because `B ⊆ C`:
  have hE : B ∩ C = B := by
    ext x
    rw [Set.mem_inter_iff]
    constructor
    · rintro ⟨h₁, h₂⟩
      exact h₁
    · rintro h₁
      exact ⟨h₁, hBC h₁⟩
  simp [hE]

/-- If measurable `B ⊆ C`, then the range of `P(B)` is contained in the
range of `P(C)`. -/
theorem proj_range_mono (P : ProjValMeasure X H) {B C : Set X}
    (hBC : B ⊆ C) (hB : MeasurableSet B) (hC : MeasurableSet C) :
    (P.proj B hB).range ≤ (P.proj C hC).range := by
  intro v hv
  obtain ⟨x, hvx⟩ := hv
  have hCB : C ∩ B = B := by
    rw [Set.inter_comm, Set.inter_eq_left.mpr hBC]
  -- `P(C) * P(B) = P(C ∩ B) = P(B)`: the absorption identity, by
  -- multiplicativity and the inclusion:
  have habs : (P.proj C hC) * (P.proj B hB) = P.proj B hB := by
    rw [P.proj_inter C B hC hB, P.proj_congr hCB (hC.inter hB) hB]
  -- `P(C) (P(B) x) = (P(C) * P(B)) x` definitionally (`mul_apply_eq_comp`):
  use (P.proj B hB) x
  change ((P.proj C hC) * (P.proj B hB)) x = v
  rw [habs]
  exact hvx

/-- For disjoint measurable sets, the projection of their union is the sum of
their projections. -/
lemma proj_union (P : ProjValMeasure X H) {B₁ B₂ : Set X}
    (hB₁ : MeasurableSet B₁) (hB₂ : MeasurableSet B₂) (hd : Disjoint B₁ B₂) :
    P.proj (B₁ ∪ B₂) (hB₁.union hB₂) = P.proj B₁ hB₁ + P.proj B₂ hB₂ := by
  have hdiag (ξ : H) :
      ⟪ξ, P.proj (B₁ ∪ B₂) (hB₁.union hB₂) ξ⟫_ℂ =
        ⟪ξ, (P.proj B₁ hB₁ + P.proj B₂ hB₂) ξ⟫_ℂ := by
    simp only [add_apply, inner_add_right, P.inner_proj, measure_union hd hB₂,
      ENNReal.toReal_add (measure_ne_top (μ := P.diag ξ) (s := B₁))
        (measure_ne_top (μ := P.diag ξ) (s := B₂))]
    push_cast
    ring
  refine ContinuousLinearMap.coe_injective ((ext_inner_map _ _).mp fun ξ => ?_)
  change ⟪P.proj (B₁ ∪ B₂) (hB₁.union hB₂) ξ, ξ⟫_ℂ =
    ⟪(P.proj B₁ hB₁ + P.proj B₂ hB₂) ξ, ξ⟫_ℂ
  rw [← inner_conj_symm (P.proj (B₁ ∪ B₂) (hB₁.union hB₂) ξ) ξ,
    ← inner_conj_symm ((P.proj B₁ hB₁ + P.proj B₂ hB₂) ξ) ξ, hdiag ξ]

/-- **Complementation**: the projection of a complement is the complementary
projection. -/
lemma proj_compl (P : ProjValMeasure X H) (B : Set X) (hB : MeasurableSet B) :
    P.proj Bᶜ hB.compl = ContinuousLinearMap.id ℂ H - P.proj B hB := by
  have hsum := P.proj_union hB hB.compl disjoint_compl_right
  rw [P.proj_congr (Set.union_compl_self B) (hB.union hB.compl) MeasurableSet.univ,
    P.proj_univ] at hsum
  linear_combination (norm := module) -hsum

/-- The squared norm of the projection of `ξ` equals its diagonal measure
on the measurable set, interpreted as a real number. -/
lemma norm_sq_proj_apply (P : ProjValMeasure X H) (B : Set X) (hB : MeasurableSet B)
    (ξ : H) :
    ‖P.proj B hB ξ‖ ^ 2 = ((P.diag ξ) B).toReal := by
  have h1 : ⟪P.proj B hB ξ, P.proj B hB ξ⟫_ℂ = ⟪ξ, P.proj B hB ξ⟫_ℂ := by
    rw [← ContinuousLinearMap.adjoint_inner_right,
      ← ContinuousLinearMap.star_eq_adjoint, P.isSelfAdjoint_proj B hB,
      ← mul_apply_eq_comp, P.proj_idem]
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), h1, P.inner_proj, RCLike.re_eq_complex_re,
    Complex.ofReal_re]

/-- Total mass: `diag ξ X = ‖ξ‖ ^ 2`. -/
lemma diag_univ_toReal (P : ProjValMeasure X H) (ξ : H) :
    ((P.diag ξ) Set.univ).toReal = ‖ξ‖ ^ 2 := by
  have h := P.inner_proj Set.univ MeasurableSet.univ ξ
  rw [P.proj_univ, ContinuousLinearMap.id_apply, inner_self_eq_norm_sq_to_K] at h
  -- `h : (‖ξ‖ : ℂ) ^ 2 = ((diag ξ univ).toReal : ℂ)`; the ENNReal→ℂ coercion is
  -- the real algebra map after `toReal`, so taking real parts both sides
  -- discharges it:
  have h1 : (‖ξ‖ : ℂ) ^ 2 = ((P.diag ξ Set.univ).toReal : ℝ) := by
    simpa using h
  have h2 : ‖ξ‖ ^ 2 = (P.diag ξ Set.univ).toReal := by
    have h3 : ((P.diag ξ Set.univ).toReal : ℝ) = ‖ξ‖ ^ 2 := by
      have h4 : RCLike.re ((‖ξ‖ : ℂ) ^ 2) = RCLike.re (((P.diag ξ Set.univ).toReal) : ℂ) :=
        congrArg RCLike.re h1
      rw [← RCLike.ofReal_re (K := ℂ) ((P.diag ξ Set.univ).toReal),
        ← RCLike.re_ofReal_pow (K := ℂ) (a := ‖ξ‖) (n := 2)]
      exact h4.symm
    exact h3.symm
  exact h2.symm

/-- For every measurable set `B`, `P(B)` is a contraction on vectors. -/
lemma norm_proj_apply_le (P : ProjValMeasure X H) (B : Set X) (hB : MeasurableSet B)
    (ξ : H) :
    ‖P.proj B hB ξ‖ ≤ ‖ξ‖ := by
  have hsq : ‖P.proj B hB ξ‖ ^ 2 ≤ ‖ξ‖ ^ 2 := by
    have h : IsFiniteMeasure (P.diag ξ) := P.diag_finite ξ
    rw [norm_sq_proj_apply, ← P.diag_univ_toReal ξ]
    exact ENNReal.toReal_mono (measure_ne_top (μ := P.diag ξ) (s := Set.univ))
      (measure_mono (Set.subset_univ B))
  calc ‖P.proj B hB ξ‖
      = Real.sqrt (‖P.proj B hB ξ‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (‖ξ‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖ξ‖ := Real.sqrt_sq (norm_nonneg _)

/-! ## Strong countable additivity

For a pairwise-disjoint measurable family `(B_k)` with measurable union `B`,
write `S n = ∑_{k < n} P(B_k)`.  The diagonal measures are genuine measures,
so `μ(B) = ∑' μ(B_k)` for every `ξ`; the squared distance
`‖(S n) ξ - P(B) ξ‖²` then equals `μ(B) - ∑_{k < n} μ(B_k)` — the mass of
`B` not yet covered — and that tends to `0`.  This is strong countable
additivity: the partial sums converge strongly to `P(B)`. -/

private def partialSum (P : ProjValMeasure X H) (f : ℕ → Set X)
    (hf : ∀ n, MeasurableSet (f n)) (n : ℕ) : H →L[ℂ] H :=
  ∑ k < n, P.proj (f k) (hf k)

private theorem partialSum_zero (P : ProjValMeasure X H) (f : ℕ → Set X)
    (hf : ∀ n, MeasurableSet (f n)) : partialSum P f hf 0 = 0 :=
  Finset.sum_empty

private theorem partialSum_succ (P : ProjValMeasure X H) (f : ℕ → Set X)
    (hf : ∀ n, MeasurableSet (f n)) (n : ℕ) :
    partialSum P f hf (n + 1) = partialSum P f hf n + P.proj (f n) (hf n) := by
  simp [partialSum]

private theorem partialSum_idem (P : ProjValMeasure X H) {f : ℕ → Set X}
    (hf : ∀ n, MeasurableSet (f n)) (hdisj : Pairwise (Disjoint on f)) (n : ℕ) :
    partialSum P f hf n * partialSum P f hf n = partialSum P f hf n := by
  induction n with
  | zero => simp [partialSum_zero]
  | succ n ih =>
    rw [partialSum_succ, mul_add, add_mul, add_mul]
    -- the cross terms vanish: the sets are pairwise disjoint
    have hzero : partialSum P f hf n * P.proj (f n) (hf n) = 0 := by
      rw [partialSum, Finset.sum_mul]
      apply Finset.sum_eq_zero
      intro k hk
      have hlt : k < n := by simpa using hk
      have hdis : f k ∩ f n = ∅ := by
        have hnd : Disjoint (f k) (f n) := by
          apply hdisj
          exact ne_of_lt hlt
        exact Disjoint.inter_eq hnd
      rw [P.proj_inter (f k) (f n) (hf k) (hf n),
        P.proj_congr hdis (MeasurableSet.inter (hf k) (hf n)) MeasurableSet.empty,
        P.proj_empty]
    have hzero' : P.proj (f n) (hf n) * partialSum P f hf n = 0 := by
      rw [partialSum, Finset.mul_sum]
      apply Finset.sum_eq_zero
      intro k hk
      have hlt : k < n := by simpa using hk
      have hdis : f n ∩ f k = ∅ := by
        have hnd : Disjoint (f n) (f k) := by
          apply hdisj
          exact by omega
        exact Disjoint.inter_eq hnd
      rw [P.proj_inter (f n) (f k) (hf n) (hf k),
        P.proj_congr hdis (MeasurableSet.inter (hf n) (hf k)) MeasurableSet.empty,
        P.proj_empty]
    -- the only surviving term is `P_n P_n`, which is `P_n` again:
    have hsq : P.proj (f n) (hf n) * P.proj (f n) (hf n) = P.proj (f n) (hf n) :=
      P.proj_idem (f n) (hf n)
    rw [hzero, hzero', add_zero, zero_add, ih, hsq]

private theorem partialSum_selfAdjoint (P : ProjValMeasure X H) {f : ℕ → Set X}
    (hf : ∀ n, MeasurableSet (f n)) (n : ℕ) :
    IsSelfAdjoint (partialSum P f hf n) := by
  induction n with
  | zero => simp [partialSum_zero, IsSelfAdjoint.zero]
  | succ n ih =>
    rw [partialSum_succ]
    exact IsSelfAdjoint.add ih
      (P.isSelfAdjoint_proj (f n) (hf n))

private theorem partialSum_mul_univ (P : ProjValMeasure X H) {f : ℕ → Set X}
    (hf : ∀ n, MeasurableSet (f n)) (n : ℕ) :
    partialSum P f hf n * P.proj (⋃ k, f k) (MeasurableSet.iUnion hf) =
      partialSum P f hf n := by
  induction n with
  | zero => simp [partialSum_zero, zero_mul]
  | succ n ih =>
    rw [partialSum_succ, add_mul]
    -- `P_n P_B = P(f_n ∩ B) = P_n` because `f_n ⊆ B`:
    have hterm : P.proj (f n) (hf n) * P.proj (⋃ k, f k) (MeasurableSet.iUnion hf) =
        P.proj (f n) (hf n) := by
      have hE : (f n) ∩ (⋃ k, f k) = f n := by
        ext x; simp only [Set.mem_inter_iff, Set.mem_iUnion]
        constructor
        · rintro ⟨h₁, h₂⟩; exact h₁
        · intro h₁; exact ⟨h₁, ⟨n, h₁⟩⟩
      rw [P.proj_inter (f n) (⋃ k, f k) (hf n) (MeasurableSet.iUnion hf),
        P.proj_congr hE (MeasurableSet.inter (hf n) (MeasurableSet.iUnion hf)) (hf n)]
    rw [ih, hterm]

private theorem univ_mul_partialSum (P : ProjValMeasure X H) {f : ℕ → Set X}
    (hf : ∀ n, MeasurableSet (f n)) (n : ℕ) :
    P.proj (⋃ k, f k) (MeasurableSet.iUnion hf) * partialSum P f hf n =
      partialSum P f hf n := by
  induction n with
  | zero => simp [partialSum_zero, mul_zero]
  | succ n ih =>
    rw [partialSum_succ, mul_add]
    have hterm : P.proj (⋃ k, f k) (MeasurableSet.iUnion hf) * P.proj (f n) (hf n) =
        P.proj (f n) (hf n) := by
      have hE : (⋃ k, f k) ∩ (f n) = f n := by
        ext x; simp only [Set.mem_inter_iff, Set.mem_iUnion]
        constructor
        · rintro ⟨h₁, h₂⟩
          -- the second conjunct is `x ∈ f n` (the first is `x ∈ ⋃ f`)
          exact h₂
        · intro h₁; exact ⟨⟨n, h₁⟩, h₁⟩
      rw [P.proj_inter (⋃ k, f k) (f n) (MeasurableSet.iUnion hf) (hf n),
        P.proj_congr hE (MeasurableSet.inter (MeasurableSet.iUnion hf) (hf n)) (hf n)]
    rw [ih, hterm]

/-
**Strong countable additivity, stated at the operator level.**  Let
`(f n)` be a pairwise-disjoint family of measurable sets and write
`B = ⋃ n, f n`; let `S n = ∑_{k < n} P(f k)`, `μ` the diagonal measure of
`ξ`, `U = μ B`, and `p n = ∑_{k < n} μ (f k)`.  Then:

* **Measure-theoretic input** (`hUeq`): countable additivity of the measure
  `μ` gives `U = ∑' k, μ (f k)` — the only place a property of `Measure X`
  is used; everything else is linear algebra.
* Each of the four diagonal inner products `⟪(S n) ξ, (S n) ξ⟫`,
  `⟪(S n) ξ, (P_B) ξ⟫`, `⟪(P_B) ξ, (S n) ξ⟫`, `⟪(P_B) ξ, (P_B) ξ⟫` equals the
  embedded real partial sum (or `U.toReal`), by the weld, self-adjointness,
  idempotence, and `P_B · (S n) = (S n) = (S n) · P_B`.
* Hence `‖(S n) ξ - (P_B) ξ‖² = U.toReal - (p n).toReal` — the mass of the
  part of `B` not yet covered (`hdist`).
* The `p n` converge to `U` along the finite sets (`ENNReal.tendsto_nat_tsum`),
  so the uncovered real mass `U.toReal - (p n).toReal` converges to `0`
  (`h0`); `Real.sqrt` is continuous at `0`, and `‖x‖ = Real.sqrt (‖x‖²)`,
  so the distance tends to `0` (`hnorm`); and a norm-convergent sequence in a
  normed space is convergent (`tendsto_zero_iff_norm_tendsto_zero`), leaving
  the constant `(P_B) ξ` behind.
-/
theorem tendsto_sum_proj_of_pairwise_disjoint {P : ProjValMeasure X H} {f : ℕ → Set X}
    (hf : ∀ n, MeasurableSet (f n)) (hdisj : Pairwise (Disjoint on f)) (ξ : H) :
    Tendsto (fun n => (∑ k < n, P.proj (f k) (hf k) : H →L[ℂ] H) ξ) Filter.atTop
        (𝓝 (P.proj (⋃ k, f k) (MeasurableSet.iUnion hf) ξ)) := by
  set μ := P.diag ξ
  set B : Set X := ⋃ k, f k
  set hB : MeasurableSet B := MeasurableSet.iUnion hf
  set P_B := P.proj B hB
  set S : ℕ → (H →L[ℂ] H) := fun n => partialSum P f hf n
  set U := μ B
  set p : ℕ → ENNReal := fun n => ∑ k ∈ Finset.range n, (μ (f k) : ℝ≥0∞)
  -- The diagonal measure is finite, so its values are never `⊤`:
  have hUfin : U ≠ ⊤ := measure_ne_top (μ := μ) (s := B)
  -- **The measure-theoretic input:** countable additivity of the measure `μ`
  -- gives `μ B` as the `tsum` of the disjoint diagonal values:
  have hUeq : U = (∑' k, (μ (f k) : ℝ≥0∞)) := by
    have h1 : μ (⋃ k, f k) = (∑' k, (μ (f k) : ℝ≥0∞)) :=
      measure_iUnion₀ (hdisj.aedisjoint) fun k => (hf k).nullMeasurableSet
    simpa [U, B] using h1
  -- The `n`-th diagonal partial sum is at most the mass of the union:
  have hUle (n : ℕ) : p n ≤ U := by
    rw [hUeq, ENNReal.tsum_eq_iSup_sum]
    exact le_iSup (fun (s : Finset ℕ) => (∑ k ∈ s, (μ (f k) : ℝ≥0∞))) (Finset.range n)
  -- (1) The four diagonal inner products.
  --
  -- Core: `⟪ξ, (S n) ξ⟫` is the real diagonal partial sum, by induction:
  have hdiagCore (n : ℕ) : (⟪ξ, (partialSum P f hf n) ξ⟫_ℂ) =
      (((p n).toReal) : ℂ) := by
    induction n with
    | zero =>
      simp [partialSum, p]
    | succ n ih =>
      have h1 : (⟪ξ, (partialSum P f hf (n + 1)) (ξ)⟫_ℂ) =
          (⟪ξ, ((partialSum P f hf n) (ξ) + ((P.proj (f n) (hf n)) (ξ)))⟫_ℂ) := by
        rw [partialSum_succ, add_apply]
      have h2 : (⟪ξ, ((partialSum P f hf n) (ξ) +
          ((P.proj (f n) (hf n)) (ξ)))⟫_ℂ) =
          (⟪ξ, (partialSum P f hf n) (ξ)⟫_ℂ) +
            (⟪ξ, (P.proj (f n) (hf n)) (ξ)⟫_ℂ) := by
        rw [inner_add_right]
      rw [h1, h2, ih, P.inner_proj (f n) (hf n) ξ]
      -- `p (n+1) = p n + μ (f n)` (the `ENNReal` partial-sum recursion):
      have hsum : (p (n + 1)) = (p n) + (μ (f n) : ℝ≥0∞) := by
        simp [p, Finset.sum_range_succ]
      -- `toReal` distributes over that finite sum:
      have hreal : ((p n).toReal) + (μ (f n)).toReal = ((p (n + 1)).toReal) := by
        have hadd : (((p n) + (μ (f n) : ℝ≥0∞)).toReal) =
            ((p n).toReal) + (μ (f n)).toReal :=
          ENNReal.toReal_add
            (show (p n) ≠ ⊤ from
              ENNReal.sum_ne_top.mpr
                (fun k _ => measure_ne_top (μ := μ) (s := f k)))
            (measure_ne_top (μ := μ) (s := f n))
        rw [hsum, ← hadd]
      -- the `ℂ`-valued goal is the `ℝ`-valued one, coerced:
      simpa using congrArg (fun x : ℝ => (x : ℂ)) hreal
  -- `⟪(S n) ξ, (S n) ξ⟫`: self-adjointness and idempotence put it in the
  -- core form:
  have hdiag (n : ℕ) : (⟪(S n) ξ, (S n) ξ⟫_ℂ) = (((p n).toReal) : ℂ) := by
    have h1 : (⟪(S n) ξ, (S n) ξ⟫_ℂ) = (⟪ξ, (S n) ((S n) ξ)⟫_ℂ) := by
      calc (⟪(S n) ξ, (S n) ξ⟫_ℂ)
          _ = (⟪(star (star (S n))) ξ, (S n) ξ⟫_ℂ) := by
            simp
          _ = (⟪ξ, ((S n)†) ((S n) ξ)⟫_ℂ) := by
            rw [ContinuousLinearMap.star_eq_adjoint (star (S n)),
                ContinuousLinearMap.star_eq_adjoint (S n),
                ContinuousLinearMap.adjoint_inner_left ((S n)†) ((S n) ξ) ξ]
          _ = (⟪ξ, (S n) ((S n) ξ)⟫_ℂ) := by
            rw [IsSelfAdjoint.adjoint_eq (partialSum_selfAdjoint P hf n)]
    rw [h1, show (S n) ((S n) ξ) = (S n) (ξ) by
      rw [← mul_apply_eq_comp, partialSum_idem P hf hdisj n]]
    simpa using hdiagCore n
  -- `⟪(S n) ξ, (P_B) ξ⟫` and `⟪(P_B) ξ, (S n) ξ⟫`: the partial sums commute
  -- with `P_B` in the strong sense `(S n) · (P_B) = (S n)` (and its mirror),
  -- so both reduce to the core form:
  have hcross (n : ℕ) : (⟪(S n) ξ, (P_B) ξ⟫_ℂ) = (((p n).toReal) : ℂ) := by
    have h1 : (⟪(S n) ξ, (P_B) ξ⟫_ℂ) = (⟪ξ, (S n) ((P_B) ξ)⟫_ℂ) := by
      calc (⟪(S n) ξ, (P_B) ξ⟫_ℂ)
          _ = (⟪(star (star (S n))) ξ, (P_B) ξ⟫_ℂ) := by
            simp
          _ = (⟪ξ, ((S n)†) ((P_B) ξ)⟫_ℂ) := by
            rw [ContinuousLinearMap.star_eq_adjoint (star (S n)),
                ContinuousLinearMap.star_eq_adjoint (S n),
                ContinuousLinearMap.adjoint_inner_left ((S n)†) ((P_B) ξ) ξ]
          _ = (⟪ξ, (S n) ((P_B) ξ)⟫_ℂ) := by
            rw [IsSelfAdjoint.adjoint_eq (partialSum_selfAdjoint P hf n)]
    rw [h1, show (S n) ((P_B) ξ) = (S n) (ξ) by
      rw [← mul_apply_eq_comp, partialSum_mul_univ P hf n]]
    simpa using hdiagCore n
  have hcross2 (n : ℕ) : (⟪(P_B) ξ, (S n) ξ⟫_ℂ) = (((p n).toReal) : ℂ) := by
    -- `⟪(P_B) ξ, (S n) ξ⟫ = ⟨(S n) ((P_B) ξ), ξ⟩` (`adjoint_inner_right` with
    -- `A := (S n)`, since `(S n)† = (S n)`):
    have h1 : (⟪(P_B) ξ, (S n) ξ⟫_ℂ) = (⟪(S n) ((P_B) ξ), ξ⟫_ℂ) := by
      have h1a : (⟪(P_B) ξ, (S n) ξ⟫_ℂ) =
          (⟪(P_B) ξ, (ContinuousLinearMap.adjoint (S n)) ξ⟫_ℂ) := by
        simp [S, IsSelfAdjoint.adjoint_eq (partialSum_selfAdjoint P hf n)]
      rw [h1a, ContinuousLinearMap.adjoint_inner_right (S n) ((P_B) ξ) ξ]
    rw [h1, show (S n) ((P_B) ξ) = (S n) (ξ) by
      rw [← mul_apply_eq_comp, partialSum_mul_univ P hf n]]
    -- `⟪(S n) ξ, ξ⟫ = ⟨ξ, (S n)† ξ⟩ = ⟨ξ, (S n) ξ⟩`:
    rw [show (⟪(S n) ξ, ξ⟫_ℂ) = (⟪ξ, (S n) ξ⟫_ℂ) by
      rw [← ContinuousLinearMap.adjoint_inner_right (S n) ξ ξ,
        IsSelfAdjoint.adjoint_eq (partialSum_selfAdjoint P hf n)]]
    simpa using hdiagCore n
  -- `⟪(P_B) ξ, (P_B) ξ⟫`: the same for `P_B` itself, with total mass `U`:
  have htotal : (⟪(P_B) ξ, (P_B) ξ⟫_ℂ) = ((U).toReal : ℂ) := by
    calc (⟪(P_B) ξ, (P_B) ξ⟫_ℂ)
        _ = (⟪(star (star (P_B))) ξ, (P_B) ξ⟫_ℂ) := by
          simp
        _ = (⟪ξ, ((P_B)†) ((P_B) ξ)⟫_ℂ) := by
          rw [ContinuousLinearMap.star_eq_adjoint (star (P_B)),
              ContinuousLinearMap.star_eq_adjoint (P_B),
              ContinuousLinearMap.adjoint_inner_left ((P_B)†) ((P_B) ξ) ξ]
        _ = (⟪ξ, (P_B) ((P_B) ξ)⟫_ℂ) := by
          rw [IsSelfAdjoint.adjoint_eq (P.isSelfAdjoint_proj B hB)]
        _ = (⟪ξ, (P_B) ξ⟫_ℂ) := by
          have hP2 : (P_B) ((P_B) ξ) = (P_B) (ξ) := by
            rw [← mul_apply_eq_comp, P.proj_idem B hB]
          simp [hP2]
        _ = (((U).toReal) : ℂ) := by
          simpa [P_B, μ, U] using P.inner_proj B hB ξ
  -- (2) The squared distance is the uncovered mass, in real form:
  --     `‖u - v‖² = re (⟪u, u⟫ - (⟨u, v⟩ + (⟨v, u⟩ - (⟨v, v⟩ : ℂ))))`,
  --     and all four inner products are the embedded reals above:
  have hdist (n : ℕ) : ‖(S n) ξ - (P_B) ξ‖ ^ 2 = (U - p n).toReal := by
    have hexp : ‖(S n) ξ - (P_B) ξ‖ ^ 2 =
        RCLike.re (⟪(S n) ξ - (P_B) ξ, (S n) ξ - (P_B) ξ⟫_ℂ) := by
      simpa using (inner_self_eq_norm_sq (𝕜 := ℂ) ((S n) ξ - (P_B) ξ)).symm
    rw [hexp, inner_sub_left, inner_sub_right, inner_sub_right,
      map_sub (f := RCLike.re (K := ℂ)), map_sub (f := RCLike.re (K := ℂ)),
      map_sub (f := RCLike.re (K := ℂ)),
      hdiag n, hcross n, hcross2 n, htotal]
    simp only [RCLike.re_to_complex, Complex.ofReal_re, sub_self, zero_sub, neg_sub]
    rw [ENNReal.toReal_sub_of_le (hUle n) hUfin]
  -- (3) The uncovered mass `U.toReal - (p n).toReal` tends to `0`:
  have hT : Tendsto (fun n : ℕ => (p n).toReal) Filter.atTop (𝓝 (U.toReal)) := by
    -- the `ENNReal`-valued partial sums converge to their tsum, which is `U`:
    have hTenn : Tendsto (fun n : ℕ => p n)
        Filter.atTop (𝓝 (∑' k, (μ (f k) : ℝ≥0∞))) := by
      simpa [p] using ENNReal.tendsto_nat_tsum (fun k => μ (f k))
    -- `toReal` is continuous at the finite point `U = ∑' k, μ (f k)`, and
    -- restricts the limit to the `ℕ`-indexed partial sums:
    rw [← Function.comp_def]
    simpa [hUeq] using
      (ENNReal.continuousAt_toReal (by
        rw [← hUeq]
        exact hUfin)).tendsto.comp hTenn
  have h0 : Tendsto (fun n : ℕ => (U - p n).toReal) Filter.atTop (𝓝 0) := by
    rw [tendsto_def]
    intro W hW
    -- `W` is a neighbourhood of `0`: take an `ε`-ball inside it:
    rcases Metric.mem_nhds_iff.mp hW with ⟨ε, hε, hWb⟩
    have hTball : (fun n : ℕ => (p n).toReal) ⁻¹' (Metric.ball (U.toReal) ε) ∈
        (Filter.atTop : Filter ℕ) := by
      rw [tendsto_def] at hT
      exact hT (Metric.ball (U.toReal) ε) (Metric.ball_mem_nhds (U.toReal) hε)
    rcases Filter.mem_atTop_sets.mp hTball with ⟨N, hN'⟩
    rw [Filter.mem_atTop_sets]
    use N
    intro n hn
    -- `hN'` says `|(p n).toReal - U.toReal| < ε`;
    -- since `(p n).toReal ≤ U.toReal`, that absolute value is exactly
    -- `U.toReal - (p n).toReal`:
    have habs : |((p n).toReal) - U.toReal| < ε := by
      simpa [Metric.mem_ball, Real.dist_eq] using hN' n hn
    have hle : (p n).toReal ≤ U.toReal := ENNReal.toReal_mono hUfin (hUle n)
    have habs2 : |((p n).toReal) - U.toReal| = U.toReal - (p n).toReal := by
      rw [abs_of_nonpos (sub_nonpos_of_le hle), neg_sub]
    have hval : (U - p n).toReal = U.toReal - (p n).toReal :=
        ENNReal.toReal_sub_of_le (hUle n) hUfin
    have hmem : (U - p n).toReal ∈ Metric.ball 0 ε := by
      rw [Metric.mem_ball, hval, Real.dist_eq, sub_zero,
        abs_of_nonneg (by linarith), ← habs2]
      exact habs
    exact hWb hmem
  -- (4) The norm tends to `0`:
  --     `‖x‖ = Real.sqrt (‖x‖²)` and `Real.sqrt` is continuous at `0`:
  have hnorm : Tendsto (fun n => ‖(S n) ξ - (P_B) ξ‖) Filter.atTop (𝓝 0) := by
    have hsq : (fun n : ℕ => ‖(S n) ξ - (P_B) ξ‖) =
        (fun n : ℕ => Real.sqrt ((U - p n).toReal)) := by
      funext n
      rw [(Real.sqrt_sq (norm_nonneg _)).symm, hdist n]
    rw [hsq, ← Function.comp_def, ← Real.sqrt_zero]
    exact (Continuous.tendsto Real.continuous_sqrt 0).comp h0
  -- (5) The norm-limit is the vector-limit; add back the constant `P_B ξ`:
  have hdiff : Tendsto (fun n : ℕ => (S n) ξ - (P_B) ξ) Filter.atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  have hadd : Tendsto (fun n : ℕ => ((S n) ξ - (P_B) ξ) + (P_B) ξ)
      Filter.atTop (𝓝 (0 + (P_B) ξ)) :=
    Tendsto.add hdiff (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (P_B) ξ) Filter.atTop (𝓝 ((P_B) ξ)))
  -- `(x - y) + y = x`, so the limit is `S n ξ` at the constant `P_B ξ`:
  have hfun : ∀ n : ℕ, ((S n) ξ - (P_B) ξ) + (P_B) ξ = (S n) ξ := by
    intro n
    simp
  have hcongr : Tendsto (fun n => (S n) ξ) Filter.atTop (𝓝 (0 + (P_B) ξ)) :=
    Tendsto.congr hfun hadd
  simpa [S, B, P_B, partialSum, zero_add] using hcongr

/-! ## Extensionality

A `ProjValMeasure` is determined by either its projection field or its
finite diagonal scalar measures. The identity `inner_proj` relates these
fields; finite measure values are recovered from their real embeddings. -/

/-- Two PVMs with the same data fields are equal; the remaining fields are
propositions. -/
lemma ext {P Q : ProjValMeasure X H} (hproj : P.proj = Q.proj)
    (hdiag : P.diag = Q.diag) : P = Q := by
  obtain ⟨p, d, _, _, _, _⟩ := P
  obtain ⟨q, e, _, _, _, _⟩ := Q
  obtain rfl : p = q := hproj
  obtain rfl : d = e := hdiag
  rfl

/-- Two projection-valued measures with the same diagonal scalar measures
are equal. -/
theorem ext_of_diag {P Q : ProjValMeasure X H}
    (h : ∀ ξ : H, P.diag ξ = Q.diag ξ) : P = Q := by
  refine ext ?_ (funext h)
  funext B hB
  refine ContinuousLinearMap.coe_injective ((ext_inner_map _ _).mp fun ξ => ?_)
  change ⟪P.proj B hB ξ, ξ⟫_ℂ = ⟪Q.proj B hB ξ, ξ⟫_ℂ
  rw [← inner_conj_symm (P.proj B hB ξ) ξ,
    ← inner_conj_symm (Q.proj B hB ξ) ξ,
    P.inner_proj, Q.inner_proj, h ξ]

/-- Two projection-valued measures agreeing on all measurable-set projections
are equal. -/
theorem ext_of_proj {P Q : ProjValMeasure X H}
    (h : ∀ (B : Set X) (hB : MeasurableSet B), P.proj B hB = Q.proj B hB) :
    P = Q := by
  refine ext_of_diag fun ξ => Measure.ext fun B hB => ?_
  have hr : (((P.diag ξ) B).toReal : ℂ) = (((Q.diag ξ) B).toReal : ℂ) := by
    rw [← P.inner_proj B hB ξ, ← Q.inner_proj B hB ξ, h B hB]
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top (μ := P.diag ξ) (s := B))
      (measure_ne_top (μ := Q.diag ξ) (s := B))).mp
    (by exact_mod_cast hr)

/-- Equality of projection-valued measures is equivalent to equality of all
diagonal scalar measures. -/
theorem ext_iff_diag {P Q : ProjValMeasure X H} :
    P = Q ↔ ∀ ξ : H, P.diag ξ = Q.diag ξ :=
  ⟨fun h ξ => by rw [h], ext_of_diag⟩

/-- Two projection-valued measures are equal exactly when they agree on every
measurable set. -/
theorem ext_iff_proj {P Q : ProjValMeasure X H} :
    P = Q ↔ ∀ (B : Set X) (hB : MeasurableSet B), P.proj B hB = Q.proj B hB :=
  ⟨fun h B hB => by rw [h], ext_of_proj⟩

end ProjValMeasure

end TauCeti
