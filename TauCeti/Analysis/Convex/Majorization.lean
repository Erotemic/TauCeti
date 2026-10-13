/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 Thinking, Claude Fable 5, Claude Opus 5
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Normed.Module.Seminorm.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Data.Fin.Tuple.Sort
public import TauCeti.Data.Fin.Append
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Weak majorization and the Hardy–Littlewood–Pólya transfer lemma

The combinatorial engine underlying every unitarily invariant norm inequality in this
development, isolated from the operator theory that consumes it.

A **T-transform** (Hardy–Littlewood–Pólya) is a convex combination of a vector
and a transposition of that vector. The operation `FiniteVector.transfer` changes two
coordinates by `-δ` and `+δ`; it realizes a Robin Hood/T-transform step under the
hypotheses `j ≠ l` and `0 ≤ δ ≤ q j - q l`. The transfer lemma
`FiniteVector.exists_isTTransform_of_not_forall_le` says that a single T-transform always
makes progress: given prefix-sum domination `z ≺w q` that is not yet coordinatewise
domination, some T-transform of `q` still dominates `z` in prefix sums while agreeing with
`z` in strictly more coordinates.  Iterating it is
`IsSymmetricConvex.mem_of_prefixSum_le`, the **transfer descent**.

## Main definitions

* `FiniteVector.prefixSum k x` — the sum of the first `k` coordinates of `x : Fin n → ℝ`.
* `FiniteVector.WeaklyMajorized x y` — weak majorization of vectors already presented in
  decreasing nonnegative order: every prefix sum of `x` is at most that of `y`.
* `FiniteVector.transfer q j l δ` — the elementary transfer of `δ` from coordinate `j` to
  coordinate `l`.
* `FiniteVector.IsTTransform y q` — `q` is a convex combination of `y` with a transposition
  of `y`.
* `FiniteVector.IsSymmetricConvex K` — `K` is convex, transposition-closed, and closed under
  flipping the sign of a single coordinate.  These are exactly the closure properties the
  descent consumes.
* `FiniteSymmetricGauge n` — a `Seminorm` on `Fin n → ℝ` that is invariant under
  permuting coordinates and under flipping a single coordinate's sign.

## Main results

* `FiniteVector.exists_isTTransform_of_not_forall_le` — **the transfer lemma**.
* `FiniteVector.IsSymmetricConvex.mem_of_prefixSum_le` — **the transfer descent**: a
  symmetric-convex set containing `y` contains every antitone nonnegative `z` whose prefix
  sums are dominated by those of `y`.
* `FiniteSymmetricGauge.le_of_prefixSum_le` and `FiniteSymmetricGauge.mono_weaklyMajorized` —
  the same statement for a gauge, obtained by applying the descent to the sublevel set
  `{x | Φ x ≤ Φ y}`, which `FiniteSymmetricGauge.isSymmetricConvex_sublevel` shows is
  symmetric-convex.

Nothing here needs a separation theorem, Birkhoff's theorem on doubly stochastic matrices, or
a majorization *completion*: total-sum equality is never assumed, and each descent step costs
one convexity application and one closure property.

## Source

Adapted from the [Davis--Kahan/DKPS formalization](https://github.com/AIQ-Kitware/aiq-dkps-formalization)
(Kitware, Inc.; Apache 2.0). The source developments include
`ForTauCeti.Analysis.Normed.FiniteLpGauge` and the unitarily invariant
seminorm majorization modules. Original authors: Jon Crall, GPT-5.6 Thinking,
Claude Fable 5, and Claude Opus 5.
-/

public section

namespace TauCeti

open scoped BigOperators

namespace FiniteVector

variable {n m : ℕ}

/-! ### Prefix sums -/

/-- Sum of the first `k` coordinates of a finite vector. For `k ≥ n` this is
its full sum. -/
def prefixSum (k : ℕ) (x : Fin n → ℝ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), x i

/-- The finite filtered-sum characterization of `prefixSum`. -/
theorem prefixSum_def (k : ℕ) (x : Fin n → ℝ) :
    prefixSum k x = ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), x i := by
  simp only [prefixSum]

/-- An empty prefix has sum zero, regardless of the vector. -/
@[simp] theorem prefixSum_zero_length (x : Fin n → ℝ) : prefixSum 0 x = 0 := by
  simp [prefixSum_def]

/-- Adding the next coordinate increases the prefix sum by that coordinate. -/
theorem prefixSum_succ (x : Fin n → ℝ) {k : ℕ} (hk : k < n) :
    prefixSum (k + 1) x = prefixSum k x + x ⟨k, hk⟩ := by
  classical
  have hfilter :
      Finset.univ.filter (fun i : Fin n => (i : ℕ) < k + 1) =
        insert ⟨k, hk⟩ (Finset.univ.filter (fun i : Fin n => (i : ℕ) < k)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hi
      have hle : (i : ℕ) ≤ k := Nat.lt_succ_iff.mp hi
      rcases lt_or_eq_of_le hle with hlt | heq
      · exact Or.inr hlt
      · exact Or.inl (Fin.ext heq)
    · rintro (h | h)
      · subst i
        exact Nat.lt_succ_self k
      · exact lt_trans h (Nat.lt_succ_self k)
  simp only [prefixSum_def, hfilter]
  rw [Finset.sum_insert]
  · ring
  · simp

/-- Prefix sums of the zero vector vanish. -/
@[simp] theorem prefixSum_zero (k : ℕ) :
    prefixSum k (0 : Fin n → ℝ) = 0 := by
  simp [prefixSum]

/-- Prefix sums are additive. -/
@[simp] theorem prefixSum_add (k : ℕ) (x y : Fin n → ℝ) :
    prefixSum k (x + y) = prefixSum k x + prefixSum k y := by
  simp [prefixSum, Finset.sum_add_distrib]

/-- Prefix sums are homogeneous. -/
@[simp] theorem prefixSum_smul (k : ℕ) (c : ℝ) (x : Fin n → ℝ) :
    prefixSum k (c • x) = c * prefixSum k x := by
  simp [prefixSum, Finset.mul_sum]

/-- Prefix sums stabilize after the vector length. -/
theorem prefixSum_eq_full_sum_of_le (x : Fin n → ℝ) {k : ℕ} (hk : n ≤ k) :
    prefixSum k x = ∑ i, x i := by
  unfold prefixSum
  have hfilter : Finset.univ.filter (fun i : Fin n => (i : ℕ) < k) =
      Finset.univ :=
    Finset.filter_true_of_mem fun i _ => lt_of_lt_of_le i.isLt hk
  rw [hfilter]

/-! ### Weak majorization -/

/-- Weak majorization for vectors already presented in decreasing,
nonnegative order. -/
structure WeaklyMajorized (x y : Fin n → ℝ) : Prop where
  left_antitone : Antitone x
  right_antitone : Antitone y
  left_nonneg : ∀ i, 0 ≤ x i
  right_nonneg : ∀ i, 0 ≤ y i
  prefix_le : ∀ k, prefixSum k x ≤ prefixSum k y

@[inherit_doc] local infix:50 " ≺w " => WeaklyMajorized

namespace WeaklyMajorized

/-- Weak majorization is reflexive on decreasing nonnegative vectors. -/
theorem refl {x : Fin n → ℝ} (hxanti : Antitone x) (hx0 : ∀ i, 0 ≤ x i) :
    x ≺w x :=
  ⟨hxanti, hxanti, hx0, hx0, fun _ => le_rfl⟩

/-- Weak majorization is transitive. -/
theorem trans {x y z : Fin n → ℝ} (hxy : x ≺w y) (hyz : y ≺w z) :
    x ≺w z :=
  ⟨hxy.left_antitone, hyz.right_antitone,
    hxy.left_nonneg, hyz.right_nonneg,
    fun k => (hxy.prefix_le k).trans (hyz.prefix_le k)⟩

/-- Coordinatewise domination implies weak majorization when both vectors are
already decreasing and nonnegative. -/
theorem of_pointwise {x y : Fin n → ℝ}
    (hxanti : Antitone x) (hyanti : Antitone y)
    (hx0 : ∀ i, 0 ≤ x i) (hy0 : ∀ i, 0 ≤ y i)
    (hxy : ∀ i, x i ≤ y i) : x ≺w y := by
  refine ⟨hxanti, hyanti, hx0, hy0, fun k => ?_⟩
  exact Finset.sum_le_sum fun i _ => hxy i

/-- Weak majorization is compatible with vector addition. -/
theorem add {x₁ x₂ y₁ y₂ : Fin n → ℝ}
    (h₁ : x₁ ≺w y₁) (h₂ : x₂ ≺w y₂) :
    x₁ + x₂ ≺w y₁ + y₂ := by
  refine ⟨?_, ?_, ?_, ?_, fun k => ?_⟩
  · intro i j hij
    exact add_le_add (h₁.left_antitone hij) (h₂.left_antitone hij)
  · intro i j hij
    exact add_le_add (h₁.right_antitone hij) (h₂.right_antitone hij)
  · intro i
    exact add_nonneg (h₁.left_nonneg i) (h₂.left_nonneg i)
  · intro i
    exact add_nonneg (h₁.right_nonneg i) (h₂.right_nonneg i)
  · rw [prefixSum_add, prefixSum_add]
    exact add_le_add (h₁.prefix_le k) (h₂.prefix_le k)

/-- Nonnegative scaling preserves weak majorization. -/
theorem nonneg_smul {x y : Fin n → ℝ} (h : x ≺w y)
    {c : ℝ} (hc : 0 ≤ c) : c • x ≺w c • y := by
  refine ⟨?_, ?_, ?_, ?_, fun k => ?_⟩
  · intro i j hij
    exact mul_le_mul_of_nonneg_left (h.left_antitone hij) hc
  · intro i j hij
    exact mul_le_mul_of_nonneg_left (h.right_antitone hij) hc
  · intro i
    exact mul_nonneg hc (h.left_nonneg i)
  · intro i
    exact mul_nonneg hc (h.right_nonneg i)
  · rw [prefixSum_smul, prefixSum_smul]
    exact mul_le_mul_of_nonneg_left (h.prefix_le k) hc

/-- The full-sum consequence of weak majorization. -/
theorem sum_le {x y : Fin n → ℝ} (h : x ≺w y) :
    ∑ i, x i ≤ ∑ i, y i := by
  have hfull := h.prefix_le n
  rw [prefixSum_eq_full_sum_of_le x le_rfl,
    prefixSum_eq_full_sum_of_le y le_rfl] at hfull
  exact hfull

end WeaklyMajorized

/-! ### Appending a zero tail -/

/-- Appending a zero tail (`Fin.append x (0 : Fin m → ℝ)`, the zero tuple of length `m`)
preserves every prefix sum. -/
theorem prefixSum_appendZeroTail (k : ℕ) (x : Fin n → ℝ) :
    prefixSum k (Fin.append x (0 : Fin m → ℝ)) = prefixSum k x := by
  unfold prefixSum
  rw [Finset.sum_filter, Fin.sum_univ_add, Finset.sum_filter]
  simp

/-- A decreasing nonnegative vector remains decreasing after appending a zero
tail. -/
theorem antitone_appendZeroTail {x : Fin n → ℝ}
    (hxanti : Antitone x) (hx0 : ∀ i, 0 ≤ x i) :
    Antitone (Fin.append x (0 : Fin m → ℝ)) := by
  intro i j hij
  have hijv : (i : ℕ) ≤ (j : ℕ) := Fin.le_def.mp hij
  simp only [Fin.append_zero_apply]
  -- the antitonicity goal is `pad j ≤ pad i`, so the outer split is on `j`
  split_ifs with hj hi
  · apply hxanti
    exact Fin.le_def.mpr hijv
  · -- `i` sits below `j < n`, so this branch is vacuous
    exact absurd hijv (by omega)
  · exact hx0 _
  · exact le_rfl

/-- Appending a zero tail preserves nonnegativity. -/
theorem appendZeroTail_nonneg {x : Fin n → ℝ} (hx0 : ∀ i, 0 ≤ x i) :
    ∀ i, 0 ≤ (Fin.append x (0 : Fin m → ℝ)) i := by
  intro i
  simp only [Fin.append_zero_apply]
  split_ifs
  · exact hx0 _
  · exact le_rfl

/-- Appending a common zero tail preserves weak majorization. -/
theorem WeaklyMajorized.appendZeroTail {x y : Fin n → ℝ}
    (h : WeaklyMajorized x y) :
    WeaklyMajorized (Fin.append x (0 : Fin m → ℝ)) (Fin.append y (0 : Fin m → ℝ)) := by
  exact ⟨antitone_appendZeroTail h.left_antitone h.left_nonneg,
    antitone_appendZeroTail h.right_antitone h.right_nonneg,
    appendZeroTail_nonneg h.left_nonneg,
    appendZeroTail_nonneg h.right_nonneg, fun k => by
      simpa only [prefixSum_appendZeroTail] using h.prefix_le k⟩

/-! ### T-transforms -/

/-- Update coordinates `j` and `l` by `-δ` and `+δ`, respectively.
Under `j ≠ l` and `0 ≤ δ ≤ q j - q l`, this is a Robin Hood/T-transform step.
For arbitrary indices and `δ`, no averaging or donor-order assumption is implied. -/
def transfer (q : Fin n → ℝ) (j l : Fin n) (δ : ℝ) : Fin n → ℝ :=
  Function.update (Function.update q j (q j - δ)) l (q l + δ)

/-- At the donor coordinate the transfer removes `δ`.  Needs `j ≠ l`, since a self-transfer would
have the receiving update overwrite the donating one. -/
theorem transfer_apply_left {q : Fin n → ℝ} {j l : Fin n} (hjl : j ≠ l) (δ : ℝ) :
    transfer q j l δ j = q j - δ := by
  rw [transfer, Function.update_of_ne hjl, Function.update_self]

/-- At the receiving coordinate the transfer adds `δ`. -/
theorem transfer_apply_right (q : Fin n → ℝ) (j l : Fin n) (δ : ℝ) :
    transfer q j l δ l = q l + δ := by
  rw [transfer, Function.update_self]

/-- A transfer leaves every coordinate other than the two it moves mass between unchanged. -/
theorem transfer_apply_of_ne {q : Fin n → ℝ} {i j l : Fin n} (hij : i ≠ j) (hil : i ≠ l)
    (δ : ℝ) : transfer q j l δ i = q i := by
  rw [transfer, Function.update_of_ne hil, Function.update_of_ne hij]

/-- A transfer of nothing is the identity. -/
@[simp] theorem transfer_zero (q : Fin n → ℝ) (j l : Fin n) : transfer q j l 0 = q := by
  simp [transfer]

/-- The prefix sums of a transfer: the moved mass leaves the prefix once it passes `j` and
returns once it passes `l`.  In particular a transfer preserves every prefix sum that
contains both coordinates or neither. -/
theorem prefixSum_transfer {q : Fin n → ℝ} {j l : Fin n} (hjl : j ≠ l) (δ : ℝ) (k : ℕ) :
    prefixSum k (transfer q j l δ) =
      prefixSum k q - (if (j : ℕ) < k then δ else 0) + (if (l : ℕ) < k then δ else 0) := by
  classical
  have hsplit : transfer q j l δ =
      q + ((fun i => if i = j then -δ else 0) + fun i => if i = l then δ else 0) := by
    funext i
    simp only [Pi.add_apply]
    rcases eq_or_ne i j with rfl | hij
    · rw [transfer_apply_left hjl, ite_eq_left rfl, ite_eq_right hjl]
      ring
    rcases eq_or_ne i l with rfl | hil
    · rw [transfer_apply_right, ite_eq_right hij, ite_eq_left rfl]
      ring
    · rw [transfer_apply_of_ne hij hil, ite_eq_right hij, ite_eq_right hil]
      ring
  have hj : prefixSum k (fun i : Fin n => if i = j then -δ else 0) =
      if (j : ℕ) < k then -δ else 0 := by
    simp [prefixSum]
  have hl : prefixSum k (fun i : Fin n => if i = l then δ else 0) =
      if (l : ℕ) < k then δ else 0 := by
    simp [prefixSum]
  rw [hsplit, prefixSum_add, prefixSum_add, hj, hl]
  split_ifs <;> ring

/-- `q` is a **T-transform** of `y`: a convex combination of `y` with one of its
transpositions.  This is the elementary move of Hardy–Littlewood–Pólya majorization theory;
`isTTransform_transfer` exhibits `transfer` as one. -/
def IsTTransform (y q : Fin n → ℝ) : Prop :=
  ∃ (j l : Fin n) (c : ℝ), 0 ≤ c ∧ c ≤ 1 ∧ q = (1 - c) • y + c • (y ∘ Equiv.swap j l)

/-- **The elementary transfer is a T-transform.**  Moving `δ ≥ 0` from `j` to `l` without
overshooting (`δ ≤ q j - q l`) is averaging `q` with its `(j l)`-transposition. -/
theorem isTTransform_transfer {q : Fin n → ℝ} {j l : Fin n} (hjl : j ≠ l) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ q j - q l) : IsTTransform q (transfer q j l δ) := by
  rcases eq_or_lt_of_le (le_trans hδ0 hδ) with hzero | hpos
  · -- No room to move: `δ = 0` and the transfer is the identity.
    have : δ = 0 := le_antisymm (hδ.trans hzero.symm.le) hδ0
    subst this
    refine ⟨j, l, 0, le_rfl, zero_le_one, ?_⟩
    simp
  · set c : ℝ := δ / (q j - q l) with hc
    have hcmul : c * (q j - q l) = δ := div_mul_cancel₀ δ (ne_of_gt hpos)
    refine ⟨j, l, c, div_nonneg hδ0 hpos.le, (div_le_one hpos).mpr hδ, ?_⟩
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply]
    rcases eq_or_ne i j with rfl | hij
    · rw [transfer_apply_left hjl, Equiv.swap_apply_left]
      linear_combination hcmul
    rcases eq_or_ne i l with rfl | hil
    · rw [transfer_apply_right, Equiv.swap_apply_right]
      linear_combination -hcmul
    · rw [transfer_apply_of_ne hij hil, Equiv.swap_apply_of_ne_of_ne hij hil]
      ring

/-! ### The transfer lemma -/

/-- **Hardy–Littlewood–Pólya transfer lemma.** If a nonnegative tuple `q` has
prefix sums dominating those of an antitone nonnegative tuple `z`, but fails
to dominate `z` coordinatewise, a single T-transform produces a nonnegative
tuple with the same prefix domination and strictly fewer disagreements with `z`. -/
theorem exists_isTTransform_of_not_forall_le {z q : Fin n → ℝ}
    (hz : Antitone z) (hz0 : ∀ i, 0 ≤ z i) (hq0 : ∀ i, 0 ≤ q i)
    (hpre : ∀ k, prefixSum k z ≤ prefixSum k q) (hnot : ¬ ∀ i, z i ≤ q i) :
    ∃ q', IsTTransform q q' ∧ (∀ i, 0 ≤ q' i) ∧
      (∀ k, prefixSum k z ≤ prefixSum k q') ∧
      (Finset.univ.filter fun i => z i ≠ q' i).card <
        (Finset.univ.filter fun i => z i ≠ q i).card := by
  classical
  push Not at hnot
  -- `l`: the least index where `q` drops below `z`.
  have hSne : (Finset.univ.filter fun i : Fin n => q i < z i).Nonempty :=
    hnot.imp fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
  set l := (Finset.univ.filter fun i : Fin n => q i < z i).min' hSne with hldef
  have hlS : q l < z l :=
    (Finset.mem_filter.mp (Finset.min'_mem _ hSne)).2
  have hlmin : ∀ i, i < l → z i ≤ q i := by
    intro i hil
    by_contra hzq
    push Not at hzq
    exact absurd
      (Finset.min'_le _ i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzq⟩))
      (not_le.mpr hil)
  -- Prefix domination at `l + 1` produces `j < l` with `z j < q j`.
  have hexj : ∃ j, j < l ∧ z j < q j := by
    by_contra hcon
    push Not at hcon
    have heq : ∀ i, i < l → z i = q i := fun i hi => le_antisymm (hlmin i hi) (hcon i hi)
    have hp := hpre ((l : ℕ) + 1)
    have hset : (Finset.univ.filter fun i : Fin n => (i : ℕ) < (l : ℕ) + 1)
        = insert l (Finset.univ.filter fun i : Fin n => (i : ℕ) < (l : ℕ)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · intro hi
        rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hi) with heq' | hlt
        · exact Or.inl (Fin.ext heq')
        · exact Or.inr hlt
      · rintro (rfl | hi) <;> omega
    have hlnot : l ∉ Finset.univ.filter fun i : Fin n => (i : ℕ) < (l : ℕ) := by simp
    rw [prefixSum, prefixSum, hset, Finset.sum_insert hlnot,
      Finset.sum_insert hlnot] at hp
    have hsum_eq :
        ∑ i ∈ Finset.univ.filter fun i : Fin n => (i : ℕ) < (l : ℕ), z i
          = ∑ i ∈ Finset.univ.filter fun i : Fin n => (i : ℕ) < (l : ℕ), q i :=
      Finset.sum_congr rfl fun i hi => heq i (Fin.lt_def.mpr (Finset.mem_filter.mp hi).2)
    rw [hsum_eq] at hp
    linarith
  obtain ⟨j, hjl, hzj⟩ := hexj
  have hjl_ne : j ≠ l := ne_of_lt hjl
  -- The transform: move `δ` from coordinate `j` down to coordinate `l`.
  set δ : ℝ := min (q j - z j) (z l - q l) with hδdef
  have hδpos : 0 < δ := lt_min (by linarith) (by linarith)
  have hδ₁ : δ ≤ q j - z j := min_le_left _ _
  have hδ₂ : δ ≤ z l - q l := min_le_right _ _
  have hδ₃ : δ ≤ q j - q l := by linarith [hz hjl.le]
  refine ⟨transfer q j l δ, isTTransform_transfer hjl_ne hδpos.le hδ₃, ?_, ?_, ?_⟩
  · -- (i) nonnegativity survives: coordinate `j` stops at `z j ≥ 0`.
    intro i
    rcases eq_or_ne i j with rfl | hij
    · rw [transfer_apply_left hjl_ne]
      linarith [hz0 i]
    rcases eq_or_ne i l with rfl | hil
    · rw [transfer_apply_right]
      linarith [hq0 l]
    · rw [transfer_apply_of_ne hij hil]
      exact hq0 i
  · -- (ii) prefix domination survives.
    intro k
    rw [prefixSum_transfer hjl_ne]
    rcases lt_or_ge (j : ℕ) k with hjk | hjk
    · rcases lt_or_ge (l : ℕ) k with hlk | hlk
      · -- Both coordinates lie in the prefix: the transform is sum-preserving there.
        rw [ite_eq_left hjk, ite_eq_left hlk]
        linarith [hpre k]
      · -- Only `j` lies in the prefix, so the prefix of `q` loses exactly `δ`.  But the
        -- prefix gap was already at least `q j - z j ≥ δ`, since `q` dominates `z`
        -- coordinatewise below `l`.
        rw [ite_eq_left hjk, ite_eq_right (by omega : ¬ (l : ℕ) < k)]
        have hjmem : j ∈ Finset.univ.filter fun i : Fin n => (i : ℕ) < k :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjk⟩
        have hterm : q j - z j ≤
            ∑ i ∈ Finset.univ.filter fun i : Fin n => (i : ℕ) < k, (q i - z i) := by
          refine Finset.single_le_sum (f := fun i => q i - z i) (fun i hi => ?_) hjmem
          have hivk : (i : ℕ) < k := (Finset.mem_filter.mp hi).2
          linarith [hlmin i (Fin.lt_def.mpr (by omega : (i : ℕ) < (l : ℕ)))]
        rw [Finset.sum_sub_distrib] at hterm
        simp only [prefixSum]
        linarith
    · -- Neither coordinate lies in the prefix: the sums are unchanged.
      rw [ite_eq_right (by omega), ite_eq_right (by omega : ¬ (l : ℕ) < k)]
      linarith [hpre k]
  · -- (iii) the transform kills at least one disagreement and creates none.
    refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset ?_).mpr ?_)
    · intro i hi
      obtain ⟨-, hine⟩ := Finset.mem_filter.mp hi
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun heq => ?_⟩
      have hij : i ≠ j := by rintro rfl; exact absurd heq hzj.ne
      have hil : i ≠ l := by rintro rfl; exact absurd heq hlS.ne'
      exact hine (by rw [transfer_apply_of_ne hij hil]; exact heq)
    · rcases min_choice (q j - z j) (z l - q l) with hmin | hmin
      · refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzj.ne⟩, ?_⟩
        have : transfer q j l δ j = z j := by
          rw [transfer_apply_left hjl_ne, hδdef, hmin]; ring
        simp [this]
      · refine ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlS.ne'⟩, ?_⟩
        have : transfer q j l δ l = z l := by
          rw [transfer_apply_right, hδdef, hmin]; ring
        simp [this]

/-! ### Symmetric-convex sets and the transfer descent -/

/-- A set of finite real vectors is **symmetric-convex** when it is convex, closed under
coordinate transpositions, and closed under flipping the sign of a single coordinate.

These are exactly the properties the transfer descent consumes, and exactly the properties a
sublevel set of a symmetric gauge has (`FiniteSymmetricGauge.isSymmetricConvex_sublevel`). -/
structure IsSymmetricConvex (K : Set (Fin n → ℝ)) : Prop where
  convex : Convex ℝ K
  swap_mem : ∀ y ∈ K, ∀ j l : Fin n, y ∘ Equiv.swap j l ∈ K
  neg_single_mem : ∀ y ∈ K, ∀ j : Fin n, Function.update y j (-(y j)) ∈ K

namespace IsSymmetricConvex

variable {K : Set (Fin n → ℝ)} (hK : IsSymmetricConvex K)
include hK

/-- A symmetric-convex set is closed under T-transforms. -/
theorem mem_of_isTTransform {y q : Fin n → ℝ} (hy : y ∈ K) (h : IsTTransform y q) : q ∈ K := by
  obtain ⟨j, l, c, hc0, hc1, rfl⟩ := h
  exact hK.convex hy (hK.swap_mem y hy j l) (by linarith) hc0 (by ring)

/-- Replacing a nonnegative coordinate by a number of no greater absolute
value preserves membership in a symmetric-convex set. -/
private theorem update_mem_of_nonneg {q : Fin n → ℝ} (hq : q ∈ K) (j : Fin n)
    {t : ℝ} (ht : |t| ≤ q j) :
    Function.update q j t ∈ K := by
  have hqj : 0 ≤ q j := le_trans (abs_nonneg t) ht
  rcases hqj.eq_or_lt with hzero | hpos
  · -- `q j = 0` forces `t = 0`: the update is trivial.
    have ht0 : t = 0 := abs_eq_zero.mp (le_antisymm (by rw [← hzero] at ht; exact ht)
      (abs_nonneg t))
    have hupd : Function.update q j t = q := by
      funext i
      rcases eq_or_ne i j with rfl | hij
      · rw [Function.update_self, ht0, ← hzero]
      · rw [Function.update_of_ne hij]
    rwa [hupd]
  · obtain ⟨ht₁, ht₂⟩ := abs_le.mp ht
    have hden : 0 < 2 * q j := by linarith
    set c₁ : ℝ := (q j + t) / (2 * q j) with hc₁
    set c₂ : ℝ := (q j - t) / (2 * q j) with hc₂
    have hc₁0 : 0 ≤ c₁ := div_nonneg (by linarith) hden.le
    have hc₂0 : 0 ≤ c₂ := div_nonneg (by linarith) hden.le
    have hsum : c₁ + c₂ = 1 := by rw [hc₁, hc₂]; field_simp; ring
    have hdecomp : Function.update q j t = c₁ • q + c₂ • Function.update q j (-(q j)) := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rcases eq_or_ne i j with rfl | hij
      · rw [Function.update_self, Function.update_self, hc₁, hc₂]
        field_simp
        ring
      · rw [Function.update_of_ne hij, Function.update_of_ne hij, ← add_mul, hsum, one_mul]
    rw [hdecomp]
    exact hK.convex hq (hK.neg_single_mem q hq j) hc₁0 hc₂0 hsum

/-- Replacing a coordinate of a vector in a symmetric-convex set by a
number of no greater absolute value preserves membership. -/
theorem update_mem {q : Fin n → ℝ} (hq : q ∈ K) (j : Fin n) {t : ℝ}
    (ht : |t| ≤ |q j|) : Function.update q j t ∈ K := by
  by_cases hqj : 0 ≤ q j
  · exact hK.update_mem_of_nonneg hq j (by simpa only [abs_of_nonneg hqj] using ht)
  · have hneg : q j < 0 := lt_of_not_ge hqj
    have hflip := hK.neg_single_mem q hq j
    have htflip : |t| ≤ (Function.update q j (-(q j))) j := by
      simpa only [Function.update_self, abs_of_neg hneg] using ht
    have h := hK.update_mem_of_nonneg hflip j htflip
    have heq : Function.update (Function.update q j (-(q j))) j t =
        Function.update q j t := by
      funext i
      by_cases hij : i = j
      · subst i
        simp
      · simp only [Function.update_of_ne hij]
    rwa [heq] at h

/-- **Absolute coordinatewise descent.** A symmetric-convex set containing
`q` also contains every tuple `z` satisfying `|z i| ≤ |q i|` at every index. -/
theorem mem_of_forall_abs_le {z q : Fin n → ℝ} (hzq : ∀ i, |z i| ≤ |q i|)
    (hq : q ∈ K) : z ∈ K := by
  classical
  -- Induct on the number of coordinates where `z` and `q` disagree.
  suffices H : ∀ d (q : Fin n → ℝ), (Finset.univ.filter fun i => z i ≠ q i).card ≤ d →
      (∀ i, |z i| ≤ |q i|) → q ∈ K → z ∈ K from H _ q le_rfl hzq hq
  intro d
  induction d with
  | zero =>
    intro q hcard _ hqK
    have hemp : (Finset.univ.filter fun i => z i ≠ q i) = ∅ :=
      Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
    have hzq' : z = q := funext fun i => by
      by_contra hne
      exact Finset.filter_eq_empty_iff.mp hemp (Finset.mem_univ i) hne
    rwa [hzq']
  | succ d ih =>
    intro q hcard hzq hqK
    by_cases heq : z = q
    · rwa [heq]
    obtain ⟨j, hj⟩ : (Finset.univ.filter fun i => z i ≠ q i).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hemp
      refine heq (funext fun i => ?_)
      by_contra hne
      exact Finset.filter_eq_empty_iff.mp hemp (Finset.mem_univ i) hne
    refine ih (Function.update q j (z j)) ?_ ?_
      (hK.update_mem hqK j (hzq j))
    · have hsub : (Finset.univ.filter fun i => z i ≠ Function.update q j (z j) i)
          ⊆ (Finset.univ.filter fun i => z i ≠ q i).erase j := by
        intro i hi
        obtain ⟨-, hine⟩ := Finset.mem_filter.mp hi
        have hij : i ≠ j := by
          rintro rfl
          exact hine (by rw [Function.update_self])
        refine Finset.mem_erase.mpr ⟨hij, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
        rwa [Function.update_of_ne hij] at hine
      have h1 := Finset.card_le_card hsub
      have h2 := Finset.card_erase_of_mem hj
      omega
    · intro i
      rcases eq_or_ne i j with rfl | hij
      · rw [Function.update_self]
      · rw [Function.update_of_ne hij]
        exact hzq i

/-- **Hardy–Littlewood–Pólya transfer descent.** For an antitone nonnegative
`z` and nonnegative `y`, domination of every prefix sum of `z` by the
corresponding sum of `y` implies that every symmetric-convex set containing
`y` also contains `z`. Total-sum equality is not required. -/
theorem mem_of_prefixSum_le {z y : Fin n → ℝ} (hz : Antitone z) (hz0 : ∀ i, 0 ≤ z i)
    (hy0 : ∀ i, 0 ≤ y i) (hpre : ∀ k, prefixSum k z ≤ prefixSum k y) (hy : y ∈ K) : z ∈ K := by
  classical
  suffices H : ∀ d (q : Fin n → ℝ), (Finset.univ.filter fun i => z i ≠ q i).card ≤ d →
      (∀ i, 0 ≤ q i) → (∀ k, prefixSum k z ≤ prefixSum k q) → q ∈ K → z ∈ K from
    H _ y le_rfl hy0 hpre hy
  intro d
  induction d with
  | zero =>
    intro q hcard _ _ hqK
    have hemp : (Finset.univ.filter fun i => z i ≠ q i) = ∅ :=
      Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
    have hzq : z = q := funext fun i => by
      by_contra hne
      exact Finset.filter_eq_empty_iff.mp hemp (Finset.mem_univ i) hne
    rwa [hzq]
  | succ d ih =>
    intro q hcard hq0 hqpre hqK
    by_cases hall : ∀ i, z i ≤ q i
    · exact hK.mem_of_forall_abs_le (fun i => by
        simpa only [abs_of_nonneg (hz0 i), abs_of_nonneg (hq0 i)] using hall i) hqK
    obtain ⟨q', htr, hq'0, hq'pre, hcard'⟩ :=
      exists_isTTransform_of_not_forall_le hz hz0 hq0 hqpre hall
    exact ih q' (by omega) hq'0 hq'pre (hK.mem_of_isTTransform hqK htr)

/-- The transfer descent, phrased with `WeaklyMajorized`. -/
theorem mem_of_weaklyMajorized {z y : Fin n → ℝ} (h : WeaklyMajorized z y) (hy : y ∈ K) :
    z ∈ K :=
  hK.mem_of_prefixSum_le h.left_antitone h.left_nonneg h.right_nonneg h.prefix_le hy

end IsSymmetricConvex

end FiniteVector

/-! ### Finite symmetric gauges -/

/-- Algebraic interface for a finite symmetric gauge: a `Seminorm` on the finite
real vectors that is invariant under permuting coordinates and under flipping
the sign of a single coordinate.  These are precisely the properties used by
the T-transform proof of weak-majorization monotonicity. -/
structure FiniteSymmetricGauge (n : ℕ) extends Seminorm ℝ (Fin n → ℝ) where
  /-- Invariance under permuting coordinates -- the *symmetric* half of the name. -/
  perm' : ∀ x (π : Equiv.Perm (Fin n)), toFun (x ∘ π) = toFun x
  /-- Invariance under flipping the sign of a single coordinate; with `perm'` this
  gives invariance under all signed permutations, which is what makes the
  sublevel sets symmetric-convex. -/
  neg_single' : ∀ x j, toFun (Function.update x j (-(x j))) = toFun x
namespace FiniteSymmetricGauge

variable {n : ℕ}

/-- Apply a finite symmetric gauge directly to a vector, writing `Φ x` for
`Φ.toSeminorm x`. -/
instance : CoeFun (FiniteSymmetricGauge n) fun _ => (Fin n → ℝ) → ℝ :=
  ⟨fun Φ x => Φ.toSeminorm x⟩

variable (Φ : FiniteSymmetricGauge n)

/-- A finite symmetric gauge is invariant under permuting coordinates -- the *symmetric* half of
the name. -/
theorem perm (x : Fin n → ℝ) (π : Equiv.Perm (Fin n)) :
    Φ (x ∘ π) = Φ x :=
  Φ.perm' x π

/-- A finite symmetric gauge is invariant under flipping the sign of a single coordinate.  With
`perm` this gives invariance under all signed permutations, which is what makes the sublevel sets
symmetric-convex. -/
theorem neg_single (x : Fin n → ℝ) (j : Fin n) :
    Φ (Function.update x j (-(x j))) = Φ x :=
  Φ.neg_single' x j

/-- Every sublevel set of a finite symmetric gauge is convex, invariant under
coordinate transpositions, and invariant under single-coordinate sign flips. -/
theorem isSymmetricConvex_sublevel (r : ℝ) :
    FiniteVector.IsSymmetricConvex {x : Fin n → ℝ | Φ x ≤ r} where
  convex := by
    simpa using (Φ.toSeminorm.convexOn).convex_le r
  swap_mem := fun y hy j l => by
    have : Φ (y ∘ Equiv.swap j l) ≤ r := by rw [Φ.perm]; exact hy
    exact this
  neg_single_mem := fun y hy j => by
    have : Φ (Function.update y j (-(y j))) ≤ r := by rw [Φ.neg_single]; exact hy
    exact this

/-- Changing a single coordinate to any value of no larger modulus cannot
increase a finite symmetric gauge. -/
theorem update_le {y : Fin n → ℝ} {j : Fin n} {t : ℝ}
    (ht : |t| ≤ |y j|) :
    Φ (Function.update y j t) ≤ Φ y := by
  have hy : y ∈ {x : Fin n → ℝ | Φ x ≤ Φ y} := by exact le_refl (Φ y)
  exact (Φ.isSymmetricConvex_sublevel (Φ y)).update_mem hy j ht

/-- **Absolute coordinatewise monotonicity.** If `|x i| ≤ |y i|` at every index,
then `Φ x ≤ Φ y`, regardless of the signs of their coordinates. -/
theorem mono {x y : Fin n → ℝ} (hxy : ∀ i, |x i| ≤ |y i|) : Φ x ≤ Φ y := by
  have hy : y ∈ {v : Fin n → ℝ | Φ v ≤ Φ y} := by exact le_refl (Φ y)
  exact (Φ.isSymmetricConvex_sublevel (Φ y)).mem_of_forall_abs_le hxy hy

/-- A finite symmetric gauge preserves weak prefix-sum domination for
antitone nonnegative left vectors and nonnegative right vectors. -/
theorem le_of_prefixSum_le {z y : Fin n → ℝ} (hz_anti : Antitone z) (hz0 : ∀ i, 0 ≤ z i)
    (hy0 : ∀ i, 0 ≤ y i)
    (hpre : ∀ k : ℕ,
      ∑ i ∈ Finset.univ.filter fun i : Fin n => (i : ℕ) < k, z i
        ≤ ∑ i ∈ Finset.univ.filter fun i : Fin n => (i : ℕ) < k, y i) :
    Φ z ≤ Φ y := by
  have hy : y ∈ {v : Fin n → ℝ | Φ v ≤ Φ y} := by exact le_refl (Φ y)
  exact (Φ.isSymmetricConvex_sublevel (Φ y)).mem_of_prefixSum_le hz_anti hz0 hy0 hpre hy

/-- Every finite symmetric gauge is monotone under weak majorization. -/
theorem mono_weaklyMajorized {x y : Fin n → ℝ}
    (h : FiniteVector.WeaklyMajorized x y) : Φ x ≤ Φ y := by
  have hy : y ∈ {v : Fin n → ℝ | Φ v ≤ Φ y} := by exact le_refl (Φ y)
  exact (Φ.isSymmetricConvex_sublevel (Φ y)).mem_of_weaklyMajorized h hy

/-! ### Antitone rearrangement

`Tuple.sort` produces a *monotone* rearrangement.  Several results downstream --
realizing a sequence as the approximation numbers of a diagonal operator, and
the block-sum statement that the sequence of a block-diagonal sum is the
decreasing rearrangement of the union -- need the *antitone* one instead.

Composing the sorting permutation with `Fin.rev` supplies it, and a symmetric
gauge cannot tell the difference, since permutation invariance is one of its
axioms.
-/

/-- The permutation putting a tuple into antitone order: sort, then reverse. -/
noncomputable def antitoneSortPerm {n : ℕ} (f : Fin n → ℝ) : Equiv.Perm (Fin n) :=
  Fin.revPerm.trans (Tuple.sort f)

/-- Sorting a tuple and reversing the sorted order gives an antitone
rearrangement of its coordinates. -/
theorem antitone_comp_antitoneSortPerm {n : ℕ} (f : Fin n → ℝ) :
    Antitone (f ∘ antitoneSortPerm f) := by
  intro i j hij
  have hrev : (j : Fin n).rev ≤ (i : Fin n).rev := Fin.rev_le_rev.mpr hij
  simpa only [Function.comp_apply, antitoneSortPerm, Equiv.trans_apply,
    Fin.revPerm_apply] using (Tuple.monotone_sort f hrev)

/-- A finite symmetric gauge does not see the rearrangement. -/
theorem apply_antitoneSortPerm {n : ℕ}
    (Φ : FiniteSymmetricGauge n) (f : Fin n → ℝ) :
    Φ (f ∘ antitoneSortPerm f) = Φ f :=
  Φ.perm f (antitoneSortPerm f)

end FiniteSymmetricGauge

end TauCeti
