/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import TauCeti.Analysis.InnerProductSpace.PointSpectrum
public import Mathlib.Analysis.InnerProductSpace.Spectrum

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
structure IsEigenFamily {ι : Type*} (T : E →ₗ[𝕜] E) (c : ι → ℝ)
    (y : ι → E) : Prop where
  /-- The eigenvectors form an orthonormal family. -/
  orthonormal : Orthonormal 𝕜 y
  /-- The eigenvalue equation for each vector in the family. -/
  apply_eq : ∀ i, T (y i) = (c i : 𝕜) • y i

namespace IsEigenFamily

variable {ι : Type*} {T : E →ₗ[𝕜] E} {c : ι → ℝ} {y : ι → E}

/-- The span of an eigenfamily is invariant under its operator. -/
theorem isInvariant_span (h : IsEigenFamily T c y) :
    ∀ x ∈ Submodule.span 𝕜 (Set.range y),
      T x ∈ Submodule.span 𝕜 (Set.range y) := by
  intro x hx
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨i, rfl⟩
    rw [h.apply_eq i]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [map_zero]
    exact Submodule.zero_mem _
  · intro a b _ _ ha hb
    rw [map_add]
    exact Submodule.add_mem _ ha hb
  · intro a b _ hb
    rw [map_smul]
    exact Submodule.smul_mem _ _ hb

/-- A recorded eigenvalue belongs to the point spectrum restricted to the family's span. -/
theorem eigenvalue_mem_restrictedPointSpectrum (h : IsEigenFamily T c y) (i : ι) :
    c i ∈ Module.End.restrictedPointSpectrum T (Submodule.span 𝕜 (Set.range y)) :=
  Module.End.mem_restrictedPointSpectrum (Submodule.subset_span ⟨i, rfl⟩)
    (h.orthonormal.ne_zero i) (h.apply_eq i)

end IsEigenFamily

variable [FiniteDimensional 𝕜 E] {n d : ℕ} {T S : E →ₗ[𝕜] E}

/-- An orthonormal eigenframe whose eigenvalues are taken at given sorted-spectrum indices. -/
def IsOrderedEigenframe (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n)
    (e : Fin d ↪ Fin n) (w : Fin d → E) : Prop :=
  IsEigenFamily T (fun i => hT.eigenvalues hn (e i)) w

/-- An ordered eigenframe is an eigenfamily with the corresponding eigenvalue list. -/
theorem isOrderedEigenframe_iff {hT : T.IsSymmetric} {hn : finrank 𝕜 E = n}
    {e : Fin d ↪ Fin n} {w : Fin d → E} :
    IsOrderedEigenframe hT hn e w ↔
      IsEigenFamily T (fun i => hT.eigenvalues hn (e i)) w :=
  Iff.rfl

/-- Selecting an indexed subfamily of the canonical eigenbasis gives an ordered eigenframe. -/
theorem isOrderedEigenframe_eigenvectorBasis (hT : T.IsSymmetric)
    (hn : finrank 𝕜 E = n) (e : Fin d ↪ Fin n) :
    IsOrderedEigenframe hT hn e (fun i => hT.eigenvectorBasis hn (e i)) :=
  isOrderedEigenframe_iff.mpr
    { orthonormal := (hT.eigenvectorBasis hn).orthonormal.comp _ e.injective
      apply_eq := fun i => hT.apply_eigenvectorBasis hn (e i) }

/-- Two spectral blocks correspond when they are spanned by ordered eigenframes selected at
identical eigenvalue indices of their respective symmetric operators. -/
def CorrespondingEigenblocks (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (hn : finrank 𝕜 E = n) (e : Fin d ↪ Fin n)
    (U V : Submodule 𝕜 E) : Prop :=
  ∃ w u : Fin d → E,
    IsOrderedEigenframe hT hn e w ∧ IsOrderedEigenframe hS hn e u ∧
      U = Submodule.span 𝕜 (Set.range w) ∧ V = Submodule.span 𝕜 (Set.range u)

/-- The blocks selected from the canonical eigenbases of two symmetric operators correspond. -/
theorem correspondingEigenblocks_eigenvectorBasis (hT : T.IsSymmetric)
    (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n) (e : Fin d ↪ Fin n) :
    CorrespondingEigenblocks hT hS hn e
      (Submodule.span 𝕜 (Set.range fun i => hT.eigenvectorBasis hn (e i)))
      (Submodule.span 𝕜 (Set.range fun i => hS.eigenvectorBasis hn (e i))) := by
  exact ⟨_, _, isOrderedEigenframe_eigenvectorBasis hT hn e,
    isOrderedEigenframe_eigenvectorBasis hS hn e, rfl, rfl⟩

/-- Correspondence of eigenblocks is symmetric in the two operators. -/
theorem CorrespondingEigenblocks.symm {hT : T.IsSymmetric} {hS : S.IsSymmetric}
    {hn : finrank 𝕜 E = n} {e : Fin d ↪ Fin n} {U V : Submodule 𝕜 E}
    (h : CorrespondingEigenblocks hT hS hn e U V) :
    CorrespondingEigenblocks hS hT hn e V U := by
  obtain ⟨w, u, hw, hu, hU, hV⟩ := h
  exact ⟨u, w, hu, hw, hV, hU⟩

end TauCeti
