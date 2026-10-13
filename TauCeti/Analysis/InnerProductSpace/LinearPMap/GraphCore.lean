/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall
-/
module

public import Mathlib.Topology.Algebra.Module.LinearPMap

/-!
# Sequential closed-graph criterion for partial linear maps

Mathlib's `LinearPMap.HasCore` is the canonical abstraction for graph cores:
`A.HasCore S` means that restricting `A` to `S` and taking its closure
recovers `A`. No second graph-core predicate is needed.

This module records the sequential closed-graph elimination lemma used in
unbounded-operator arguments. If domain vectors converge in the ambient space
and their images converge as well, closedness of the graph identifies the
limit as a vector in the domain and determines its image.

## Provenance

Adapted from the graph-limit argument in the Apache-2.0 DKPS formalization
(`DavisKahan/Sources/DavisKahan1970/SineTheta/CommonCore.lean`, Kitware, Inc.),
formerly phrased for the project's bundled closed-operator representation.
-/

public section

namespace LinearPMap

open Filter Topology

variable {R E F : Type*} [CommRing R]
variable [AddCommGroup E] [AddCommGroup F] [Module R E] [Module R F]
variable [TopologicalSpace E] [TopologicalSpace F]

/-- A closed partial linear map contains the ambient limit of any convergent
sequence of domain vectors whose operator images also converge. The operator
value at the limit is the limit of the images. -/
theorem IsClosed.mem_domain_of_tendsto
    {A : E →ₗ.[R] F} (hA : A.IsClosed)
    {u : ℕ → E} {x : E} {y : F} (hu : ∀ n, u n ∈ A.domain)
    (hlim : Tendsto u atTop (𝓝 x))
    (hAlim : Tendsto (fun n => A ⟨u n, hu n⟩) atTop (𝓝 y)) :
    ∃ h : x ∈ A.domain, A ⟨x, h⟩ = y := by
  have hmem : ∀ n, (u n, A ⟨u n, hu n⟩) ∈ (A.graph : Set (E × F)) :=
    fun n => A.mem_graph ⟨u n, hu n⟩
  have hpair : Tendsto (fun n => (u n, A ⟨u n, hu n⟩)) atTop (𝓝 (x, y)) :=
    hlim.prodMk_nhds hAlim
  have hlimmem : (x, y) ∈ (A.graph : Set (E × F)) :=
    hA.mem_of_tendsto hpair (Eventually.of_forall hmem)
  obtain ⟨v, hv1, hv2⟩ := (LinearPMap.mem_graph_iff A).1 hlimmem
  dsimp only at hv1 hv2
  have hxmem : x ∈ A.domain := hv1 ▸ v.property
  refine ⟨hxmem, ?_⟩
  have hveq : (⟨x, hxmem⟩ : A.domain) = v := Subtype.ext hv1.symm
  rw [hveq, hv2]

end LinearPMap
