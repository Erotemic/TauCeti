/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5, Claude Opus 4.8, Claude Opus 5
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearIsometry.FromBasis
public import TauCeti.Analysis.InnerProductSpace.Gram.QuadraticForm
public import TauCeti.Analysis.InnerProductSpace.Gram.Eigenvalue
public import TauCeti.Analysis.InnerProductSpace.Gram.Adjoint
public import TauCeti.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Finite-dimensional real near-isometries

If a linear endomorphism of a finite-dimensional real inner product space distorts squared norms by
at most `δ < 1`, it has a symmetric Gram square root `S` and factors as `M = W ∘ S`, where `W` is
a linear isometry equivalence. The factorization gives the sharp pointwise estimate
`‖M x - W x‖ ≤ δ * ‖x‖`. A continuous-linear-map variant takes an operator-norm Gram bound.

The underlying basis-isometry result is stated for general `RCLike` inner product spaces in
`LinearIsometry.FromBasis`. The quadratic-form, eigenvalue, and operator-norm bounds are imported
from reusable modules under `Gram/`.

## References and provenance

* N. J. Higham, *Functions of Matrices: Theory and Computation*, Ch. 8.
* Adapted from the Apache-2.0 DKPS formalization (Kitware, Inc.).
-/

public section

namespace TauCeti

open scoped RealInnerProductSpace InnerProductSpace
open Module (finrank)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section Diagonal

variable {d : ℕ}

/-- The operator that scales the `k`-th vector of an orthonormal basis by `c k`. -/
private noncomputable def diagonal (b : OrthonormalBasis (Fin d) ℝ E) (c : Fin d → ℝ) :
    E →ₗ[ℝ] E :=
  b.toBasis.constr ℝ fun j => c j • b j

private theorem diagonal_basis (b : OrthonormalBasis (Fin d) ℝ E) (c : Fin d → ℝ)
    (k : Fin d) :
    diagonal b c (b k) = c k • b k := by
  have := b.toBasis.constr_basis ℝ (fun j => c j • b j) k
  rwa [OrthonormalBasis.coe_toBasis] at this

/-- **Diagonals compose pointwise.**  `diagonal b f ∘ₗ diagonal b g` is the
diagonal of the pointwise product. -/
private theorem diagonal_comp_diagonal (b : OrthonormalBasis (Fin d) ℝ E)
    (f g : Fin d → ℝ) :
    diagonal b f ∘ₗ diagonal b g = diagonal b (fun k => f k * g k) := by
  refine b.toBasis.ext fun k => ?_
  simp only [OrthonormalBasis.coe_toBasis, LinearMap.comp_apply, diagonal_basis, map_smul,
    smul_smul, mul_comm]

/-- **A diagonal minus the identity is diagonal**, with factors `c k - 1`. -/
private theorem diagonal_sub_id (b : OrthonormalBasis (Fin d) ℝ E) (c : Fin d → ℝ) :
    diagonal b c - LinearMap.id = diagonal b fun k => c k - 1 := by
  refine b.toBasis.ext fun k => ?_
  simp only [OrthonormalBasis.coe_toBasis, LinearMap.sub_apply, LinearMap.id_apply,
    diagonal_basis, sub_smul, one_smul]

/-- A diagonal operator acts on basis coordinates by scalar multiplication. -/
private theorem repr_diagonal (b : OrthonormalBasis (Fin d) ℝ E) (c : Fin d → ℝ) (x : E)
    (k : Fin d) : b.repr (diagonal b c x) k = c k * b.repr x k := by
  have hx : diagonal b c x = ∑ j : Fin d, b.repr x j • (c j • b j) := by
    conv_lhs => rw [← b.sum_repr x, map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_smul, diagonal_basis]
  rw [b.repr_apply_apply, hx, inner_sum, Finset.sum_eq_single k]
  · rw [real_inner_smul_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
      b.orthonormal.norm_eq_one k, b.repr_apply_apply]
    ring
  · intro j _ hjk
    rw [real_inner_smul_right, real_inner_smul_right, b.inner_eq_zero hjk.symm]
    ring
  · intro hk; exact absurd (Finset.mem_univ k) hk

private theorem isSymmetric_diagonal (b : OrthonormalBasis (Fin d) ℝ E) (c : Fin d → ℝ) :
    (diagonal b c).IsSymmetric := by
  have key :
      ∀ u v : E, ⟪diagonal b c u, v⟫_ℝ =
        ∑ k : Fin d, c k * b.repr u k * b.repr v k := by
    intro u v
    conv_lhs => rw [← b.sum_repr v]
    rw [inner_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [real_inner_smul_right, real_inner_comm, ← b.repr_apply_apply, repr_diagonal]
    ring
  intro x y
  rw [key, real_inner_comm, key]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- A diagonal operator whose scaling factors are bounded by `δ` has operator norm at most
`δ`, by Parseval. -/
private theorem norm_diagonal_apply_le (b : OrthonormalBasis (Fin d) ℝ E) (c : Fin d → ℝ)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hc : ∀ k, |c k| ≤ δ) (x : E) :
    ‖diagonal b c x‖ ≤ δ * ‖x‖ := by
  have hpars : ∀ y : E, ∑ k : Fin d, b.repr y k ^ 2 = ‖y‖ ^ 2 := by
    intro y
    rw [← b.sum_sq_inner_right y]
    exact Finset.sum_congr rfl fun k _ => by rw [b.repr_apply_apply]
  have hbnd : ‖diagonal b c x‖ ^ 2 ≤ δ ^ 2 * ‖x‖ ^ 2 := by
    rw [← hpars (diagonal b c x), ← hpars x, Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [repr_diagonal, mul_pow]
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    have := hc k
    nlinarith [abs_nonneg (c k), abs_le.mp (hc k), sq_abs (c k)]
  nlinarith [hbnd, norm_nonneg (diagonal b c x), mul_nonneg hδ0 (norm_nonneg x),
    sq_nonneg (‖diagonal b c x‖ - δ * ‖x‖)]

/-- A diagonal operator whose scaling factors are all within `δ` of `1` moves no vector by
more than `δ`.

This is the operator form of the scalar estimate that makes the near-isometry constant sharp:
`diagonal b c - 1` is again diagonal, with factors `c k - 1`. -/
private theorem norm_diagonal_apply_sub_self_le (b : OrthonormalBasis (Fin d) ℝ E)
    (c : Fin d → ℝ) {δ : ℝ} (hδ0 : 0 ≤ δ) (hc : ∀ k, |c k - 1| ≤ δ) (x : E) :
    ‖diagonal b c x - x‖ ≤ δ * ‖x‖ := by
  have hsub := diagonal_sub_id b c
  have hx : diagonal b c x - x = diagonal b (fun k => c k - 1) x := by
    have := congrArg (fun T : E →ₗ[ℝ] E => T x) hsub
    simpa using this
  rw [hx]
  exact norm_diagonal_apply_le b _ hδ0 hc x

end Diagonal

end TauCeti

open scoped RealInnerProductSpace InnerProductSpace
open Module (finrank)
open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

namespace LinearMap

/-- The images of a Gram eigenbasis under `M` are pairwise orthogonal, with squared
norms given by the eigenvalues. -/
private theorem inner_map_eigenvectorBasis {M : E →ₗ[ℝ] E} {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ E) (μ : Fin d → ℝ)
    (hunit : ∀ k, ⟪b k, b k⟫_ℝ = 1)
    (hGbasis : ∀ k, (M.adjoint * M) (b k) = μ k • b k) (j k : Fin d) :
    ⟪M (b j), M (b k)⟫_ℝ = if j = k then μ j else 0 := by
  have hadj : ⟪M (b j), M (b k)⟫_ℝ = ⟪(M.adjoint * M) (b j), b k⟫_ℝ := by
    rw [Module.End.mul_apply, LinearMap.adjoint_inner_left]
  rw [hadj, hGbasis j, real_inner_smul_left]
  by_cases hjk : j = k
  · subst hjk; rw [hunit j, ite_eq_left rfl, mul_one]
  · rw [b.inner_eq_zero hjk, ite_eq_right hjk, mul_zero]

/-- Rescaling the eigenbasis images by `(√ μ k)⁻¹` turns the Gram matrix of `M` into the
identity: a map sending `b k` to `(√ μ k)⁻¹ • M (b k)` preserves the inner products *between
basis vectors*.

With `inner_map_eq_of_inner_basis` this is the whole reason `W = M ∘ S⁻¹` is an isometry in
`exists_linearIsometryEquiv_comp_polarFactor`. -/
private theorem inner_basis_of_smul_inv_sqrt {M W : E →ₗ[ℝ] E} {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ E) {μ : Fin d → ℝ} (hμpos : ∀ k, 0 < μ k)
    (hunit : ∀ k, ⟪b k, b k⟫_ℝ = 1)
    (hGbasis : ∀ k, (M.adjoint * M) (b k) = μ k • b k)
    (hWbasis : ∀ k, W (b k) = (Real.sqrt (μ k))⁻¹ • M (b k)) (j k : Fin d) :
    ⟪W (b j), W (b k)⟫_ℝ = ⟪b j, b k⟫_ℝ := by
  rw [hWbasis, hWbasis, real_inner_smul_left, real_inner_smul_right,
    inner_map_eigenvectorBasis b μ hunit hGbasis]
  by_cases hjk : j = k
  · subst hjk
    rw [ite_eq_left rfl, hunit j]
    have hsj : 0 < Real.sqrt (μ j) := Real.sqrt_pos.mpr (hμpos j)
    have hsqj : Real.sqrt (μ j) * Real.sqrt (μ j) = μ j :=
      Real.mul_self_sqrt (le_of_lt (hμpos j))
    field_simp
    exact (Real.sq_sqrt (le_of_lt (hμpos j))).symm
  · rw [ite_eq_right hjk, b.inner_eq_zero hjk, mul_zero, mul_zero]

/-- A real near-isometry admits an orthonormal Gram eigenbasis with positive eigenvalues
whose deviations from one are bounded by the quadratic-form error. -/
private theorem exists_orthonormalBasis_gram (M : E →ₗ[ℝ] E) {δ : ℝ} (hδ : δ < 1)
    (hM : ∀ x : E, |⟪M x, M x⟫_ℝ - ⟪x, x⟫_ℝ| ≤ δ * ⟪x, x⟫_ℝ)
    {d : ℕ} (hd : finrank ℝ E = d) :
    ∃ (b : OrthonormalBasis (Fin d) ℝ E) (μ : Fin d → ℝ),
      (∀ k, ⟪b k, b k⟫_ℝ = 1) ∧ (∀ k, (M.adjoint * M) (b k) = μ k • b k) ∧
        (∀ k, |μ k - 1| ≤ δ) ∧ ∀ k, 0 < μ k := by
  have hGsymm : (M.adjoint * M).IsSymmetric := LinearMap.isSymmetric_adjoint_mul_self M
  set b := hGsymm.eigenvectorBasis hd with hb
  set μ := hGsymm.eigenvalues hd with hμ
  have hunit : ∀ k : Fin d, ⟪b k, b k⟫_ℝ = 1 := fun k => by
    rw [real_inner_self_eq_norm_sq, b.orthonormal.norm_eq_one k]; ring
  have hGbasis : ∀ k : Fin d, (M.adjoint * M) (b k) = μ k • b k := by
    intro k
    rw [hb, hGsymm.apply_eigenvectorBasis, ← hb, ← hμ]
    simp
  have hμbound : ∀ k : Fin d, |μ k - 1| ≤ δ := fun k =>
    abs_eigenvalue_sub_one_le hM (hunit k) (hGbasis k)
  refine ⟨b, μ, hunit, hGbasis, hμbound, fun k => ?_⟩
  have hk := hμbound k
  rw [abs_le] at hk
  linarith

/-- A real finite-dimensional near-isometry factors through a symmetric square root of its
Gram operator, with a sharp pointwise estimate for the square root. -/
theorem exists_linearIsometryEquiv_comp_polarFactor (M : E →ₗ[ℝ] E) {δ : ℝ} (hδ : δ < 1)
    (hM : ∀ x : E, |⟪M x, M x⟫_ℝ - ⟪x, x⟫_ℝ| ≤ δ * ⟪x, x⟫_ℝ) :
    ∃ (W : E ≃ₗᵢ[ℝ] E) (S : E →ₗ[ℝ] E),
      (∀ x : E, M x = W (S x)) ∧ S.IsSymmetric ∧ S ∘ₗ S = M.adjoint ∘ₗ M ∧
        ∀ x : E, ‖S x - x‖ ≤ δ * ‖x‖ := by
  -- Degenerate case: if `E` is a subsingleton every vector is `0`.
  rcases subsingleton_or_nontrivial E with hsub | hnt
  · refine ⟨LinearIsometryEquiv.refl ℝ E, LinearMap.id, fun x => ?_, fun x y => ?_,
      LinearMap.ext fun x => ?_, fun x => ?_⟩ <;>
      simp [Subsingleton.elim x (0 : E)]
  -- Main case: `E` is nontrivial.  Derive `δ ≥ 0` from a nonzero vector.
  have hδ0 : 0 ≤ δ := nonneg_of_quadraticFormBound hM
  obtain ⟨d, hd⟩ : ∃ d, finrank ℝ E = d := ⟨_, rfl⟩
  -- Sorted eigen-data of the Gram operator `Mᵀ M`, with every eigenvalue within `δ` of `1`.
  obtain ⟨b, μ, hunit, hGbasis, hμbound, hμpos⟩ := exists_orthonormalBasis_gram M hδ hM hd
  have hsqrtpos : ∀ k : Fin d, 0 < Real.sqrt (μ k) := fun k => Real.sqrt_pos.mpr (hμpos k)
  -- The modulus `S = G^(1/2)` and its inverse `R = G^(-1/2)`, diagonal in the eigenbasis.
  set S : E →ₗ[ℝ] E := diagonal b (fun k => Real.sqrt (μ k)) with hS
  set R : E →ₗ[ℝ] E := diagonal b (fun k => (Real.sqrt (μ k))⁻¹) with hR
  have hRS : ∀ x : E, R (S x) = x := by
    have : R ∘ₗ S = LinearMap.id := by
      rw [hS, hR, diagonal_comp_diagonal]
      refine b.toBasis.ext fun k => ?_
      rw [OrthonormalBasis.coe_toBasis, LinearMap.id_apply, diagonal_basis,
        inv_mul_cancel₀ (ne_of_gt (hsqrtpos k)), one_smul]
    intro x
    exact congrArg (fun T : E →ₗ[ℝ] E => T x) this
  -- `S` is a square root of the Gram operator.
  have hSS : S ∘ₗ S = M.adjoint ∘ₗ M := by
    rw [hS, diagonal_comp_diagonal]
    refine b.toBasis.ext fun k => ?_
    rw [OrthonormalBasis.coe_toBasis, diagonal_basis,
      Real.mul_self_sqrt (le_of_lt (hμpos k))]
    exact (hGbasis k).symm
  -- The candidate isometry `W₀ = M ∘ R`, which is orthonormal on the eigenbasis.
  set W₀ : E →ₗ[ℝ] E := M ∘ₗ R with hW
  have hWbasis : ∀ k : Fin d, W₀ (b k) = (Real.sqrt (μ k))⁻¹ • M (b k) := fun k => by
    rw [hW, LinearMap.comp_apply, hR, diagonal_basis, map_smul]
  have hWortho := inner_basis_of_smul_inv_sqrt b hμpos hunit hGbasis hWbasis
  -- `S` moves no vector by more than `δ`, since `|√(μ k) - 1| ≤ |μ k - 1| ≤ δ`.
  have hSest : ∀ x : E, ‖S x - x‖ ≤ δ * ‖x‖ := by
    intro x
    rw [hS]
    exact norm_diagonal_apply_sub_self_le b _ hδ0
      (fun k => (Real.abs_sqrt_sub_one_le_abs_sub_one).trans (hμbound k)) x
  -- Bundle `W₀` as a linear isometry equivalence and read off the factorization.
  obtain ⟨U, hU⟩ := LinearMap.exists_linearIsometryEquiv_of_inner_map
    (b.inner_map_eq_of_inner_basis hWortho)
  refine ⟨U, S, fun x => ?_, hS ▸ isSymmetric_diagonal b _, hSS, hSest⟩
  rw [hU, hW, LinearMap.comp_apply, hRS]

/-- **The sharp near-isometry estimate.**  If the quadratic form of a linear map `M` on a
finite-dimensional real inner product space is uniformly `δ`-close to the identity quadratic
form (with `δ < 1`), then `M` lies within `δ` — not `2 * δ` — of a genuine linear isometry
equivalence.

This is immediate from `exists_linearIsometryEquiv_comp_polarFactor`: `M x - W x` is the image
under the isometry `W` of `S x - x`. -/
theorem exists_linearIsometryEquiv_norm_sub_apply_le (M : E →ₗ[ℝ] E) {δ : ℝ} (hδ : δ < 1)
    (hM : ∀ x : E, |⟪M x, M x⟫_ℝ - ⟪x, x⟫_ℝ| ≤ δ * ⟪x, x⟫_ℝ) :
    ∃ W : E ≃ₗᵢ[ℝ] E, ∀ x : E, ‖M x - W x‖ ≤ δ * ‖x‖ := by
  obtain ⟨W, S, hMS, -, -, hSest⟩ := exists_linearIsometryEquiv_comp_polarFactor M hδ hM
  refine ⟨W, fun x => ?_⟩
  rw [hMS x, ← map_sub, W.norm_map]
  exact hSest x

end LinearMap

namespace ContinuousLinearMap

/-- A bounded real endomorphism with a small Gram defect is close to a linear isometry
equivalence, with the sharp coefficient `δ`. -/
theorem exists_linearIsometryEquiv_norm_sub_apply_le (M : E →L[ℝ] E) {δ : ℝ} (hδ : δ < 1)
    (hM : ‖ContinuousLinearMap.adjoint M * M - 1‖ ≤ δ) :
    ∃ W : E ≃ₗᵢ[ℝ] E, ∀ x : E, ‖M x - W x‖ ≤ δ * ‖x‖ := by
  obtain ⟨W, hW⟩ :=
    LinearMap.exists_linearIsometryEquiv_norm_sub_apply_le (M : E →ₗ[ℝ] E) hδ
    (abs_inner_sub_le_of_norm_adjoint_mul_self_sub_one_le M hM)
  exact ⟨W, fun x => by simpa using hW x⟩

end ContinuousLinearMap

end
