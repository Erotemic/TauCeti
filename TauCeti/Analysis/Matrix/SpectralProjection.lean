/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AIQ-Kitware DKPS contributors, GPT-6
-/
module

public import TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Measurable
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

/-!
# Fixed-threshold spectral projectors of Hermitian matrices

The characteristic function of the closed upper ray `[c, ∞)` acts by the
finite-dimensional matrix functional calculus as the orthogonal projection
onto the eigenspaces with eigenvalues at least `c`. At the threshold itself,
the associated eigenvectors are retained.

The characteristic function is discontinuous, so these projectors are generally
not continuous in the matrix. Nevertheless they are Borel measurable. Continuous
ramps approach the characteristic function pointwise, and diagonalization in a
finite eigenbasis turns this into convergence of their matrix functional calculi.
The argument does not select eigenvectors measurably or assume a spectral gap.

## Roadmap

* **MSS-B11**: construct and characterize the closed-threshold projector.
* **MSS-B12**: prove the projector is measurable on finite Hermitian matrices.
* **MSS-B13**: obtain measurability for a random Hermitian matrix.

**MSS-B14**, threshold-count stability, is already proved in
`TauCeti.Analysis.Matrix.Eigenvalues`, as
`Matrix.IsHermitian.card_eigenvalues₀_ge_eq_of_norm_sub_lt`.
The generic continuity and measurability results covering **MSS-B09–B10** are
already available in Mathlib and TauCeti and are not reimplemented here.

## Provenance

Adapted from `ForTauCeti/Analysis/Matrix/SpectralProjection.lean` and the
finite-spectrum convergence proof in
`ForTauCeti/Analysis/Matrix/SpectralFunctionMeasurable.lean` in the
[AIQ-Kitware DKPS formalization](https://github.com/AIQ-Kitware/aiq-dkps-formalization)
(Apache-2.0). The CFC measurability step now uses the general theorem already
present in `TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Measurable`.
-/

public section

open MeasureTheory Filter Set
open scoped Topology Matrix Matrix.Norms.L2Operator

namespace TauCeti.Matrix

variable {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]

/-! ### Projector and its spectral action -/

/-- **MSS-B11.** The orthogonal spectral projector onto the sum of the
eigenspaces of `A` whose eigenvalues belong to the closed ray `[c, ∞)`. -/
noncomputable def spectralProjectionIci (c : ℝ) (A : Matrix ι ι 𝕜)
    (_hA : A.IsHermitian) : Matrix ι ι 𝕜 :=
  cfc (Set.indicator (Set.Ici c) (1 : ℝ → ℝ)) A

/-- Upper-threshold spectral projections are Hermitian. -/
theorem isHermitian_spectralProjectionIci (c : ℝ)
    {A : Matrix ι ι 𝕜} (hA : A.IsHermitian) :
    (spectralProjectionIci c A hA).IsHermitian := by
  exact (cfc_predicate (Set.indicator (Set.Ici c) (1 : ℝ → ℝ)) A).isHermitian

/-- Upper-threshold spectral projections are idempotent. Together with
Hermitian symmetry, this characterizes an orthogonal projection. -/
theorem isIdempotentElem_spectralProjectionIci (c : ℝ)
    {A : Matrix ι ι 𝕜} (hA : A.IsHermitian) :
    IsIdempotentElem (spectralProjectionIci c A hA) := by
  classical
  let f := Set.indicator (Set.Ici c) (1 : ℝ → ℝ)
  let D : Matrix ι ι 𝕜 :=
    Matrix.diagonal (fun i => (f (hA.eigenvalues i) : 𝕜))
  have hd : D * D = D := by
    simp only [D, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases hi : c ≤ hA.eigenvalues i <;> simp [f, hi]
  have h := congrArg (Unitary.conjStarAlgAut 𝕜 _ hA.eigenvectorUnitary) hd
  change spectralProjectionIci c A hA * spectralProjectionIci c A hA =
      spectralProjectionIci c A hA
  simpa only [map_mul, spectralProjectionIci, hA.cfc_eq, Matrix.IsHermitian.cfc,
    Function.comp_def, D, f] using h

/-- The projector is conjugate to the diagonal matrix whose diagonal entry is
one precisely at eigenvalues greater than or equal to the threshold. -/
theorem spectralProjectionIci_eq_conj_diagonal (c : ℝ)
    {A : Matrix ι ι 𝕜} (hA : A.IsHermitian) :
    spectralProjectionIci c A hA =
      Unitary.conjStarAlgAut 𝕜 _ hA.eigenvectorUnitary
        (Matrix.diagonal (fun i => if c ≤ hA.eigenvalues i then 1 else 0)) := by
  rw [spectralProjectionIci, hA.cfc_eq, Matrix.IsHermitian.cfc]
  congr 1
  ext i j
  simp [Set.indicator, Function.comp_def]

/-- In the eigenvector basis, the projector retains exactly the columns with
eigenvalues in `[c, ∞)`. -/
theorem spectralProjectionIci_mul_eigenvectorUnitary (c : ℝ)
    {A : Matrix ι ι 𝕜} (hA : A.IsHermitian) :
    spectralProjectionIci c A hA * (hA.eigenvectorUnitary : Matrix ι ι 𝕜) =
      (hA.eigenvectorUnitary : Matrix ι ι 𝕜) *
        Matrix.diagonal (fun i => if c ≤ hA.eigenvalues i then 1 else 0) := by
  rw [spectralProjectionIci_eq_conj_diagonal, Unitary.conjStarAlgAut_apply]
  simp only [mul_assoc, Unitary.coe_star_mul_self, mul_one]

/-- Eigenvector columns exactly at the threshold are retained, since the
threshold ray is closed. -/
theorem spectralProjectionIci_mulVec_of_eigenvalue_eq (c : ℝ)
    {A : Matrix ι ι 𝕜} (hA : A.IsHermitian) (i : ι)
    (hi : hA.eigenvalues i = c) :
    (spectralProjectionIci c A hA) *ᵥ
        (fun j => (hA.eigenvectorUnitary : Matrix ι ι 𝕜) j i) =
      (fun j => (hA.eigenvectorUnitary : Matrix ι ι 𝕜) j i) := by
  funext j
  have h := congrArg (fun M : Matrix ι ι 𝕜 => M j i)
    (spectralProjectionIci_mul_eigenvectorUnitary c hA)
  rw [Matrix.mul_diagonal] at h
  simp only [hi, le_refl, ite_true, mul_one] at h
  simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply] using h

/-! ### Measurability via continuous ramp approximation -/

/-- A continuous ramp which equals one on `[c, ∞)` and approaches zero
at every fixed point strictly below `c`. -/
private def thresholdRamp (c : ℝ) (m : ℕ) (x : ℝ) : ℝ :=
  max 0 (min 1 (1 + ((m : ℝ) + 1) * (x - c)))

private theorem continuous_thresholdRamp (c : ℝ) (m : ℕ) :
    Continuous (thresholdRamp c m) := by
  unfold thresholdRamp
  fun_prop

private theorem thresholdRamp_eventually_eq (c x : ℝ) :
    ∀ᶠ m : ℕ in atTop,
      thresholdRamp c m x = (Set.indicator (Set.Ici c) (1 : ℝ → ℝ)) x := by
  by_cases hx : c ≤ x
  · apply Filter.Eventually.of_forall
    intro m
    have hprod : 0 ≤ ((m : ℝ) + 1) * (x - c) := by positivity
    have hmin : min 1 (1 + ((m : ℝ) + 1) * (x - c)) = 1 :=
      min_eq_left (by linarith)
    simp [thresholdRamp, hx, hmin]
  · have hpos : 0 < c - x := sub_pos.mpr (lt_of_not_ge hx)
    obtain ⟨N, hN⟩ := exists_nat_ge (1 / (c - x))
    have hN' : 1 ≤ (N : ℝ) * (c - x) := (div_le_iff₀ hpos).mp hN
    filter_upwards [eventually_ge_atTop N] with m hm
    have hm' : (N : ℝ) ≤ m := by exact_mod_cast hm
    have hprod : 1 ≤ ((m : ℝ) + 1) * (c - x) :=
      hN'.trans (mul_le_mul_of_nonneg_right (by linarith) hpos.le)
    have hneg : 1 + ((m : ℝ) + 1) * (x - c) ≤ 0 := by nlinarith
    have hmin : min 1 (1 + ((m : ℝ) + 1) * (x - c)) =
        1 + ((m : ℝ) + 1) * (x - c) := min_eq_right (by linarith)
    have hmax : max 0 (1 + ((m : ℝ) + 1) * (x - c)) = 0 := max_eq_left hneg
    simp [thresholdRamp, hx, hmin, hmax]

/-- At a fixed Hermitian matrix of finite size, convergence of scalar
functions at its eigenvalues implies convergence of their CFC matrices. -/
private theorem tendsto_cfc_of_pointwise {β : Type*} {l : Filter β}
    {F : β → ℝ → ℝ} {f : ℝ → ℝ}
    {A : Matrix ι ι 𝕜} (hA : A.IsHermitian)
    (hF : ∀ x ∈ spectrum ℝ A, Tendsto (fun i => F i x) l (𝓝 (f x))) :
    Tendsto (fun i => cfc (F i) A) l (𝓝 (cfc f A)) := by
  have hvalues : Tendsto (fun i j => F i (hA.eigenvalues j)) l
      (𝓝 (fun j => f (hA.eigenvalues j))) :=
    tendsto_pi_nhds.mpr fun j => hF _ (hA.eigenvalues_mem_spectrum_real j)
  have hdiag : Continuous (fun v : ι → ℝ =>
      Matrix.diagonal (fun j => (v j : 𝕜))) := by
    fun_prop
  have ht := hdiag.continuousAt.tendsto.comp hvalues
  simpa only [hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
    Function.comp_def] using (tendsto_const_nhds.mul ht).mul tendsto_const_nhds

/- The general CFC measurability theorem requires a real normed-algebra
structure compatible with the canonical L2 operator norm. This is only a
local adapter, not a new global choice of matrix norm. -/
noncomputable local instance instRealNormedAlgebraMatrix :
    NormedAlgebra ℝ (Matrix ι ι 𝕜) :=
  { (inferInstance : Algebra ℝ (Matrix ι ι 𝕜)) with
    norm_smul_le := fun r x => by
      have hx : r • x = (r : 𝕜) • x := by
        ext i j
        simp [RCLike.real_smul_eq_coe_smul (K := 𝕜)]
      rw [hx, norm_smul, RCLike.norm_ofReal, Real.norm_eq_abs] }

/- Matrices are definitionally double function spaces. The product
pseudo-metrizability is needed for the measurable-limit theorem. -/
noncomputable local instance instPseudoMetrizableSpaceMatrix {κ : Type*} [Finite κ] :
    TopologicalSpace.PseudoMetrizableSpace (Matrix κ κ 𝕜) := by
  let : Fintype κ := Fintype.ofFinite κ
  exact inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (κ → κ → 𝕜))

/-- **MSS-B12.** The threshold projector is Borel measurable on Hermitian
finite matrices, including when an eigenvalue lies exactly at the cut. -/
theorem measurable_spectralProjectionIci (c : ℝ) :
    Measurable fun A : {A : Matrix ι ι 𝕜 // A.IsHermitian} =>
      spectralProjectionIci c A.1 A.2 := by
  have hm (m : ℕ) : Measurable
      (fun A : {A : Matrix ι ι 𝕜 // A.IsHermitian} =>
        cfc (thresholdRamp c m) (A : Matrix ι ι 𝕜)) := by
    exact TauCeti.measurable_cfc_of_predicate
      (𝕜 := ℝ) (p := IsSelfAdjoint)
      (a := fun A : {A : Matrix ι ι 𝕜 // A.IsHermitian} =>
        (A : Matrix ι ι 𝕜))
      (f := thresholdRamp c m) (s := Set.univ)
      measurable_subtype_coe (fun A => A.2.isSelfAdjoint)
      (continuous_thresholdRamp c m).continuousOn (by simp)
  apply measurable_of_tendsto_metrizable' atTop hm
  -- The limit theorem asks for convergence in the product topology on functions.
  -- Check convergence separately at each Hermitian input matrix.
  apply tendsto_pi_nhds.mpr
  rintro ⟨A, hA⟩
  change Tendsto (fun m : ℕ => cfc (thresholdRamp c m) A) atTop
    (𝓝 (cfc (Set.indicator (Set.Ici c) (1 : ℝ → ℝ)) A))
  apply tendsto_cfc_of_pointwise hA
  intro x _
  exact tendsto_const_nhds.congr'
    (Filter.EventuallyEq.symm (thresholdRamp_eventually_eq c x))

/-- **MSS-B13.** A measurable family of Hermitian matrices has a measurable
closed-threshold spectral projector, without any eigenvalue-gap assumption. -/
theorem measurable_spectralProjectionIci_of_hermitian {Ω : Type*}
    [MeasurableSpace Ω] (c : ℝ)
    {Bm : Ω → Matrix ι ι 𝕜} (hBmeas : Measurable Bm)
    (hherm : ∀ w, (Bm w).IsHermitian) :
    Measurable fun w => spectralProjectionIci c (Bm w) (hherm w) :=
  (measurable_spectralProjectionIci c).comp (hBmeas.subtype_mk (h := hherm))

end TauCeti.Matrix
