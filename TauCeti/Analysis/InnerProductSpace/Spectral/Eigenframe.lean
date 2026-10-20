/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import TauCeti.Analysis.InnerProductSpace.PointSpectrum
public import TauCeti.Analysis.InnerProductSpace.Spectrum

/-!
# Eigenfamilies and corresponding eigenblocks

An eigenfamily records orthonormal eigenvectors and their real eigenvalues without choosing an
entire eigenbasis. An ordered eigenframe associates the vectors with specified indices in the
sorted eigenvalue list of a finite-dimensional symmetric operator. Two such frames give
corresponding eigenblocks when they use the same ordered index embedding.

The frame formulation allows the selected vectors to vary inside repeated eigenspaces; the
canonical eigenvector basis gives one instance of the interface.

## References

* Y. Yu, T. Wang, R. J. Samworth, *A useful variant of the Davis--Kahan theorem for
  statisticians*, Biometrika **102** (2015), 315--323.
* Kitware DKPS formalization,
  `ForTauCeti/Analysis/InnerProductSpace/Spectral/EigenFrame.lean`.
-/

public section

open Module (finrank)
open scoped InnerProductSpace

namespace TauCeti

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- An orthonormal family of eigenvectors of `T` with specified real eigenvalues. -/
structure IsEigenfamily {ι : Type*} (T : E →ₗ[𝕜] E) (c : ι → ℝ)
    (y : ι → E) : Prop where
  /-- The eigenvectors form an orthonormal family. -/
  orthonormal : Orthonormal 𝕜 y
  /-- The eigenvalue equation for each vector in the family. -/
  apply_eq : ∀ i, T (y i) = (c i : 𝕜) • y i

namespace IsEigenfamily

variable {ι : Type*} {T : E →ₗ[𝕜] E} {c : ι → ℝ} {y : ι → E}

/-- Membership in the eigenspace at the family's recorded eigenvalue. -/
theorem mem_eigenspace (h : IsEigenfamily T c y) (i : ι) :
    y i ∈ Module.End.eigenspace T (c i : 𝕜) :=
  Module.End.mem_eigenspace_iff.mpr (h.apply_eq i)

/-- Every member of an orthonormal eigenfamily is a nonzero eigenvector. -/
theorem hasEigenvector (h : IsEigenfamily T c y) (i : ι) :
    Module.End.HasEigenvector T (c i : 𝕜) (y i) :=
  ⟨h.mem_eigenspace i, h.orthonormal.ne_zero i⟩

/-- The span of an eigenfamily is preserved by its operator. -/
theorem map_span_le (h : IsEigenfamily T c y) :
    Submodule.map T (Submodule.span 𝕜 (Set.range y)) ≤
      Submodule.span 𝕜 (Set.range y) := by
  rw [Submodule.map_span_le]
  rintro _ ⟨i, rfl⟩
  rw [h.apply_eq i]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- An eigenfamily's span is closed under application of its operator. -/
theorem apply_mem_span_of_mem_span (h : IsEigenfamily T c y) {x : E}
    (hx : x ∈ Submodule.span 𝕜 (Set.range y)) :
    T x ∈ Submodule.span 𝕜 (Set.range y) :=
  h.map_span_le (Submodule.mem_map_of_mem hx)

/-- The dimension of the span of a finite orthonormal eigenfamily equals its cardinality. -/
theorem finrank_span [Fintype ι] (h : IsEigenfamily T c y) :
    finrank 𝕜 (Submodule.span 𝕜 (Set.range y)) = Fintype.card ι :=
  finrank_span_eq_card h.orthonormal.linearIndependent

/-- An eigenfamily's span carries no real point-spectrum values beyond its recorded eigenvalues. -/
theorem restrictedPointSpectrum_span_subset (h : IsEigenfamily T c y) :
    Module.End.restrictedPointSpectrum T (Submodule.span 𝕜 (Set.range y)) ⊆
      Set.range c := by
  have hspan : Submodule.span 𝕜 (Set.range y) ≤
      Module.End.pointSpectralSubspace T (Set.range c) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    exact Module.End.eigenspace_le_pointSpectralSubspace (A := T)
      (show c i ∈ Set.range c from ⟨i, rfl⟩) (h.mem_eigenspace i)
  intro μ hμ
  obtain ⟨x, hx, hx0, hTx⟩ := Module.End.mem_restrictedPointSpectrum_iff.mp
    (Module.End.restrictedPointSpectrum_mono hspan hμ)
  exact (Module.End.pointSpectrumIn_iff.mp
    (Module.End.pointSpectrumIn_pointSpectralSubspace T (Set.range c))) x hx hx0 μ hTx

/-- A recorded eigenvalue belongs to the point spectrum restricted to the family's span. -/
theorem eigenvalue_mem_restrictedPointSpectrum (h : IsEigenfamily T c y) (i : ι) :
    c i ∈ Module.End.restrictedPointSpectrum T (Submodule.span 𝕜 (Set.range y)) :=
  Module.End.mem_restrictedPointSpectrum (Submodule.subset_span ⟨i, rfl⟩)
    (h.orthonormal.ne_zero i) (h.apply_eq i)

/-- The restricted real point spectrum on an eigenfamily's span is exactly the recorded set. -/
theorem restrictedPointSpectrum_span_eq (h : IsEigenfamily T c y) :
    Module.End.restrictedPointSpectrum T (Submodule.span 𝕜 (Set.range y)) =
      Set.range c := by
  apply Set.Subset.antisymm h.restrictedPointSpectrum_span_subset
  rintro _ ⟨i, rfl⟩
  exact h.eigenvalue_mem_restrictedPointSpectrum i

end IsEigenfamily

variable [FiniteDimensional 𝕜 E] {n d : ℕ} {T S : E →ₗ[𝕜] E}

/-- An orthonormal eigenframe whose eigenvalues are taken at given sorted-spectrum indices. -/
def IsOrderedEigenframe (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n)
    (e : Fin d ↪ Fin n) (w : Fin d → E) : Prop :=
  IsEigenfamily T (fun i => hT.eigenvalues hn (e i)) w

/-- An ordered eigenframe is an eigenfamily with the corresponding eigenvalue list. -/
theorem isOrderedEigenframe_iff {hT : T.IsSymmetric} {hn : finrank 𝕜 E = n}
    {e : Fin d ↪ Fin n} {w : Fin d → E} :
    IsOrderedEigenframe hT hn e w ↔
      IsEigenfamily T (fun i => hT.eigenvalues hn (e i)) w :=
  Iff.rfl

/-- An ordered eigenframe spans a subspace of dimension equal to its number of indices. -/
theorem IsOrderedEigenframe.finrank_span {hT : T.IsSymmetric}
    {hn : finrank 𝕜 E = n} {e : Fin d ↪ Fin n} {w : Fin d → E}
    (h : IsOrderedEigenframe hT hn e w) :
    finrank 𝕜 (Submodule.span 𝕜 (Set.range w)) = d := by
  simpa only [Fintype.card_fin] using (isOrderedEigenframe_iff.mp h).finrank_span

/-- Two spectral blocks correspond when they are spanned by ordered eigenframes selected at
identical eigenvalue indices of their respective symmetric operators. -/
def CorrespondingEigenblocks (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (hn : finrank 𝕜 E = n) (e : Fin d ↪ Fin n)
    (U V : Submodule 𝕜 E) : Prop :=
  ∃ w u : Fin d → E,
    IsOrderedEigenframe hT hn e w ∧ IsOrderedEigenframe hS hn e u ∧
      U = Submodule.span 𝕜 (Set.range w) ∧ V = Submodule.span 𝕜 (Set.range u)

/-- A pair of blocks corresponds exactly when it has ordered-eigenframe witnesses for both
operators and the blocks are their spans. -/
theorem correspondingEigenblocks_iff {hT : T.IsSymmetric} {hS : S.IsSymmetric}
    {hn : finrank 𝕜 E = n} {e : Fin d ↪ Fin n} {U V : Submodule 𝕜 E} :
    CorrespondingEigenblocks hT hS hn e U V ↔
      ∃ w u : Fin d → E,
        IsOrderedEigenframe hT hn e w ∧ IsOrderedEigenframe hS hn e u ∧
          U = Submodule.span 𝕜 (Set.range w) ∧
            V = Submodule.span 𝕜 (Set.range u) :=
  Iff.rfl

/-- Correspondence of eigenblocks is symmetric in the two operators. -/
theorem CorrespondingEigenblocks.symm {hT : T.IsSymmetric} {hS : S.IsSymmetric}
    {hn : finrank 𝕜 E = n} {e : Fin d ↪ Fin n} {U V : Submodule 𝕜 E}
    (h : CorrespondingEigenblocks hT hS hn e U V) :
    CorrespondingEigenblocks hS hT hn e V U := by
  obtain ⟨w, u, hw, hu, hU, hV⟩ := correspondingEigenblocks_iff.mp h
  exact correspondingEigenblocks_iff.mpr ⟨u, w, hu, hw, hV, hU⟩

/-- The first block of a pair of corresponding eigenblocks has dimension `d`. -/
theorem CorrespondingEigenblocks.finrank_left {hT : T.IsSymmetric} {hS : S.IsSymmetric}
    {hn : finrank 𝕜 E = n} {e : Fin d ↪ Fin n} {U V : Submodule 𝕜 E}
    (h : CorrespondingEigenblocks hT hS hn e U V) : finrank 𝕜 U = d := by
  obtain ⟨w, u, hw, hu, rfl, rfl⟩ := correspondingEigenblocks_iff.mp h
  exact hw.finrank_span

/-- The second block of a pair of corresponding eigenblocks has dimension `d`. -/
theorem CorrespondingEigenblocks.finrank_right {hT : T.IsSymmetric} {hS : S.IsSymmetric}
    {hn : finrank 𝕜 E = n} {e : Fin d ↪ Fin n} {U V : Submodule 𝕜 E}
    (h : CorrespondingEigenblocks hT hS hn e U V) : finrank 𝕜 V = d := by
  obtain ⟨w, u, hw, hu, rfl, rfl⟩ := correspondingEigenblocks_iff.mp h
  exact hu.finrank_span

/-- The first corresponding block is invariant under the first operator. -/
theorem CorrespondingEigenblocks.map_left_le {hT : T.IsSymmetric} {hS : S.IsSymmetric}
    {hn : finrank 𝕜 E = n} {e : Fin d ↪ Fin n} {U V : Submodule 𝕜 E}
    (h : CorrespondingEigenblocks hT hS hn e U V) : Submodule.map T U ≤ U := by
  obtain ⟨w, u, hw, hu, rfl, rfl⟩ := correspondingEigenblocks_iff.mp h
  exact (isOrderedEigenframe_iff.mp hw).map_span_le

/-- The second corresponding block is invariant under the second operator. -/
theorem CorrespondingEigenblocks.map_right_le {hT : T.IsSymmetric} {hS : S.IsSymmetric}
    {hn : finrank 𝕜 E = n} {e : Fin d ↪ Fin n} {U V : Submodule 𝕜 E}
    (h : CorrespondingEigenblocks hT hS hn e U V) : Submodule.map S V ≤ V := by
  obtain ⟨w, u, hw, hu, rfl, rfl⟩ := correspondingEigenblocks_iff.mp h
  exact (isOrderedEigenframe_iff.mp hu).map_span_le

/-- Applying the first operator to a vector in its corresponding block stays in that block. -/
theorem CorrespondingEigenblocks.apply_mem_left {hT : T.IsSymmetric} {hS : S.IsSymmetric}
    {hn : finrank 𝕜 E = n} {e : Fin d ↪ Fin n} {U V : Submodule 𝕜 E}
    (h : CorrespondingEigenblocks hT hS hn e U V) {x : E} (hx : x ∈ U) :
    T x ∈ U :=
  h.map_left_le (Submodule.mem_map_of_mem hx)

/-- Applying the second operator to a vector in its corresponding block stays in that block. -/
theorem CorrespondingEigenblocks.apply_mem_right {hT : T.IsSymmetric} {hS : S.IsSymmetric}
    {hn : finrank 𝕜 E = n} {e : Fin d ↪ Fin n} {U V : Submodule 𝕜 E}
    (h : CorrespondingEigenblocks hT hS hn e U V) {x : E} (hx : x ∈ V) :
    S x ∈ V :=
  h.map_right_le (Submodule.mem_map_of_mem hx)

/-- The first block's restricted point spectrum is exactly its selected eigenvalues. -/
theorem CorrespondingEigenblocks.restrictedPointSpectrum_left_eq
    {hT : T.IsSymmetric} {hS : S.IsSymmetric}
    {hn : finrank 𝕜 E = n} {e : Fin d ↪ Fin n} {U V : Submodule 𝕜 E}
    (h : CorrespondingEigenblocks hT hS hn e U V) :
    Module.End.restrictedPointSpectrum T U =
      Set.range (fun i : Fin d => hT.eigenvalues hn (e i)) := by
  obtain ⟨w, u, hw, hu, rfl, rfl⟩ := correspondingEigenblocks_iff.mp h
  exact (isOrderedEigenframe_iff.mp hw).restrictedPointSpectrum_span_eq

/-- The second block's restricted point spectrum is exactly its selected eigenvalues. -/
theorem CorrespondingEigenblocks.restrictedPointSpectrum_right_eq
    {hT : T.IsSymmetric} {hS : S.IsSymmetric}
    {hn : finrank 𝕜 E = n} {e : Fin d ↪ Fin n} {U V : Submodule 𝕜 E}
    (h : CorrespondingEigenblocks hT hS hn e U V) :
    Module.End.restrictedPointSpectrum S V =
      Set.range (fun i : Fin d => hS.eigenvalues hn (e i)) := by
  obtain ⟨w, u, hw, hu, rfl, rfl⟩ := correspondingEigenblocks_iff.mp h
  exact (isOrderedEigenframe_iff.mp hu).restrictedPointSpectrum_span_eq

/-- The first block carries only eigenvalues assigned to the selected indices of `T`. -/
theorem CorrespondingEigenblocks.restrictedPointSpectrum_left_subset
    {hT : T.IsSymmetric} {hS : S.IsSymmetric}
    {hn : finrank 𝕜 E = n} {e : Fin d ↪ Fin n} {U V : Submodule 𝕜 E}
    (h : CorrespondingEigenblocks hT hS hn e U V) :
    Module.End.restrictedPointSpectrum T U ⊆
      Set.range (fun i : Fin d => hT.eigenvalues hn (e i)) := by
  intro μ hμ
  simpa only [h.restrictedPointSpectrum_left_eq] using hμ

/-- The second block carries only eigenvalues assigned to the selected indices of `S`. -/
theorem CorrespondingEigenblocks.restrictedPointSpectrum_right_subset
    {hT : T.IsSymmetric} {hS : S.IsSymmetric}
    {hn : finrank 𝕜 E = n} {e : Fin d ↪ Fin n} {U V : Submodule 𝕜 E}
    (h : CorrespondingEigenblocks hT hS hn e U V) :
    Module.End.restrictedPointSpectrum S V ⊆
      Set.range (fun i : Fin d => hS.eigenvalues hn (e i)) := by
  intro μ hμ
  simpa only [h.restrictedPointSpectrum_right_eq] using hμ

end TauCeti

/-! ### Canonical eigenframe constructors -/

namespace LinearMap.IsSymmetric

open TauCeti

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E] {n d : ℕ} {T S : E →ₗ[𝕜] E}

/-- Selecting an indexed subfamily of the canonical eigenbasis gives an ordered eigenframe. -/
theorem isOrderedEigenframe_eigenvectorBasis (hT : T.IsSymmetric)
    (hn : finrank 𝕜 E = n) (e : Fin d ↪ Fin n) :
    IsOrderedEigenframe hT hn e (fun i => hT.eigenvectorBasis hn (e i)) :=
  isOrderedEigenframe_iff.mpr
    { orthonormal := (hT.eigenvectorBasis hn).orthonormal.comp _ e.injective
      apply_eq := fun i => hT.apply_eigenvectorBasis hn (e i) }

/-- The canonical eigenvector spans at the same indices form corresponding eigenblocks. -/
theorem correspondingEigenblocks_eigenvectorBasis (hT : T.IsSymmetric)
    (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n) (e : Fin d ↪ Fin n) :
    CorrespondingEigenblocks hT hS hn e
      (hT.eigenvectorSpan hn (Set.range e))
      (hS.eigenvectorSpan hn (Set.range e)) := by
  refine correspondingEigenblocks_iff.mpr
    ⟨_, _, isOrderedEigenframe_eigenvectorBasis hT hn e,
      isOrderedEigenframe_eigenvectorBasis hS hn e, ?_, ?_⟩
  · exact (span_eigenvectorBasis_comp_embedding hT hn e).symm
  · exact (span_eigenvectorBasis_comp_embedding hS hn e).symm

end LinearMap.IsSymmetric
