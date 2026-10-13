/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import Mathlib.Analysis.InnerProductSpace.Orthonormal
public import TauCeti.Analysis.InnerProductSpace.LpIndexCongr
public import Mathlib.Analysis.Normed.Lp.LpEquiv
public import Mathlib.Topology.Bases

/-!
# Separability bounds the size of an orthonormal set

Two facts, in increasing specificity.

* `TauCeti.countable_of_pairwise_dist_le`: a uniformly separated set in a separable
  pseudometric space is countable.
* `TauCeti.countable_of_orthonormal`: an orthonormal set in a separable inner
  product space is countable, because distinct orthonormal vectors are `√2` apart.

The second is the step Mathlib does not have, and it is the one a Hilbert-space classification
at separable scope needs first: it is what turns "the space is separable" into "the Hilbert
basis is indexed by a countable set", after which two infinite-dimensional separable Hilbert
spaces can be compared through `HilbertBasis.repr`.

The main classification result says that two complete, separable, infinite-dimensional
inner-product spaces over the same `RCLike` field are linearly isometric.
The classification follows by reindexing their `ℓ²` representations through an
equivalence of countably infinite Hilbert-basis index types.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* The results are general separable-Hilbert-space infrastructure, depending on
  Mathlib and `TauCeti.Analysis.InnerProductSpace.LpIndexCongr`.
* Spectra influence: **none**.
-/

namespace TauCeti

/-- **A uniformly separated set in a separable pseudometric space is countable.**

The balls of radius `δ / 2` about distinct points are disjoint, nonempty, and open;
separability bounds the size of any such family. -/
public theorem countable_of_pairwise_dist_le {M : Type*} [PseudoMetricSpace M]
    [TopologicalSpace.SeparableSpace M] {s : Set M} {δ : ℝ} (hδ : 0 < δ)
    (h : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → δ ≤ dist x y) : s.Countable := by
  refine Set.PairwiseDisjoint.countable_of_isOpen
    (a := s) (s := fun x : M => Metric.ball x (δ / 2)) ?_ ?_ ?_
  · intro x hx y hy hxy
    exact Metric.ball_disjoint_ball (by linarith [h x hx y hy hxy])
  · intro x hx
    exact Metric.isOpen_ball
  · intro x hx
    exact Metric.nonempty_ball.2 (half_pos hδ)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **Distinct members of an orthonormal set are `√2` apart.** -/
public theorem dist_eq_sqrt_two_of_orthonormal {s : Set E}
    (h : Orthonormal 𝕜 ((↑) : s → E)) {x y : E} (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y) :
    dist x y = Real.sqrt 2 := by
  have hne : (⟨x, hx⟩ : s) ≠ ⟨y, hy⟩ := by
    simpa [Subtype.ext_iff] using hxy
  have hinner : (inner 𝕜 x y : 𝕜) = 0 := h.2 hne
  have hnx : ‖x‖ = 1 := h.1 ⟨x, hx⟩
  have hny : ‖y‖ = 1 := h.1 ⟨y, hy⟩
  have hsq : ‖x - y‖ ^ 2 = 2 := by
    rw [@norm_sub_sq 𝕜, hinner, hnx, hny]
    norm_num
  have hnn : 0 ≤ ‖x - y‖ := norm_nonneg _
  rw [dist_eq_norm]
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2, hsq, hnn]

/-- **An orthonormal set in a separable inner product space is countable.**

Distinct orthonormal vectors are `√2 ≥ 1` apart, so the set is uniformly separated and
`TauCeti.countable_of_pairwise_dist_le` applies.  Mathlib proves that every Hilbert space has a
Hilbert basis but says nothing about its size; this is the missing step that makes "separable"
into "countably indexed". -/
public theorem countable_of_orthonormal
    [TopologicalSpace.SeparableSpace E] {s : Set E}
    (h : Orthonormal 𝕜 ((↑) : s → E)) : s.Countable := by
  refine countable_of_pairwise_dist_le (δ := 1) one_pos ?_
  intro x hx y hy hxy
  rw [dist_eq_sqrt_two_of_orthonormal h hx hy hxy]
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]

/-! ## Separable Hilbert spaces are classified by the size of a Hilbert basis

Mathlib proves that every Hilbert space has a Hilbert basis (`exists_hilbertBasis`) but says
nothing about how large it is.  With `countable_of_orthonormal` the separable case is settled:
the index set is countable, so two separable Hilbert spaces whose bases are both countably
infinite are isometric, by `TauCeti.nonempty_linearIsometryEquiv_of_hilbertBasis` through the
`ℓ²` reindexing.

The classification proceeds by identifying each space with its `ℓ²` model and
reindexing those models through an equivalence of countably infinite sets. -/

section Classification

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- The index type of a Hilbert basis of a separable inner-product space is countable.

The basis is an orthonormal family, so its range is a countable orthonormal set;
linearly independent basis vectors have distinct indices. -/
public theorem countable_of_hilbertBasis [TopologicalSpace.SeparableSpace E]
    {ι : Type*} (b : HilbertBasis ι 𝕜 E) : Countable ι := by
  classical
  have hcount : (Set.range (b : ι → E)).Countable :=
    countable_of_orthonormal b.orthonormal.toSubtypeRange
  exact (Equiv.ofInjective (b : ι → E)
    b.orthonormal.linearIndependent.injective).countable_iff.mpr hcount.to_subtype

/-- **A separable Hilbert space has a countably indexed Hilbert basis.**

`exists_hilbertBasis` supplies the basis and `countable_of_hilbertBasis` bounds its index set. -/
public theorem exists_countable_hilbertBasis [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E] :
    ∃ (w : Set E) (_b : HilbertBasis w 𝕜 E), w.Countable := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis 𝕜 E
  exact ⟨w, b, Set.countable_coe_iff.mpr (countable_of_hilbertBasis b)⟩

/-- **Two Hilbert spaces with countably infinite Hilbert bases are isometric.**

Two countably infinite index types are equinumerous, and the `ℓ²` reindexing carries one space
onto the other.  Separability enters through `exists_countable_hilbertBasis`, which is what
supplies `Countable` on the index; it is not needed again here. -/
public theorem nonempty_linearIsometryEquiv_of_countable_infinite_hilbertBasis
    {ι ι' : Type*} [Countable ι] [Infinite ι] [Countable ι'] [Infinite ι']
    (b : HilbertBasis ι 𝕜 E) (b' : HilbertBasis ι' 𝕜 F) :
    Nonempty (E ≃ₗᵢ[𝕜] F) :=
  nonempty_linearIsometryEquiv_of_hilbertBasis b b' nonempty_equiv_of_countable.some

/-- **A finitely indexed Hilbert basis makes the space finite-dimensional.**

Through `lpPiLpₗᵢ`, the `ℓ²` model over a finite index is `PiLp 2` over that index, which is
finite-dimensional. -/
public theorem finiteDimensional_of_finite_hilbertBasis {ι : Type*} [Finite ι]
    (b : HilbertBasis ι 𝕜 E) : FiniteDimensional 𝕜 E := by
  have : Fintype ι := Fintype.ofFinite ι
  exact (b.repr.trans (lpPiLpₗᵢ (fun _ : ι => 𝕜) 𝕜)).toLinearEquiv.symm.finiteDimensional

/-- **Any two infinite-dimensional separable Hilbert spaces over the same field are
isometrically isomorphic.**

Every Hilbert basis is countable by separability and must be infinite by the
infinite-dimensionality hypothesis. Thus the two bases have equivalent index types,
and their `ℓ²` representations induce a linear isometric equivalence. -/
public theorem nonempty_linearIsometryEquiv_of_separable_of_infiniteDimensional
    [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
    [CompleteSpace F] [TopologicalSpace.SeparableSpace F]
    (hE : ¬ FiniteDimensional 𝕜 E) (hF : ¬ FiniteDimensional 𝕜 F) :
    Nonempty (E ≃ₗᵢ[𝕜] F) := by
  classical
  obtain ⟨w, b, _⟩ := exists_hilbertBasis 𝕜 E
  obtain ⟨w', b', _⟩ := exists_hilbertBasis 𝕜 F
  have hw : w.Infinite := by
    by_contra hfin
    rw [Set.not_infinite] at hfin
    have : Finite w := hfin
    exact hE (finiteDimensional_of_finite_hilbertBasis b)
  have hw' : w'.Infinite := by
    by_contra hfin
    rw [Set.not_infinite] at hfin
    have : Finite w' := hfin
    exact hF (finiteDimensional_of_finite_hilbertBasis b')
  have hcw : Countable w := countable_of_hilbertBasis b
  have hcw' : Countable w' := countable_of_hilbertBasis b'
  have hiw : Infinite w := hw.to_subtype
  have hiw' : Infinite w' := hw'.to_subtype
  exact @nonempty_linearIsometryEquiv_of_countable_infinite_hilbertBasis
    𝕜 _ E _ _ F _ _ w w' hcw hiw hcw' hiw' b b'

end Classification

end TauCeti
