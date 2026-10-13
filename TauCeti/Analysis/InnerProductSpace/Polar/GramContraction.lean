/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Contractions from Gram identities and domination

Let `T : E →L[𝕜] F` and let `A : E →L[𝕜] E` be self-adjoint.
The construction `gramContraction T A` extends the rule `A x ↦ T x`
from the range of `A` to its closure and vanishes on the orthogonal
complement. Under the **Gram identity** `A² = T†T`, this extension
is isometric on the initial space, has norm at most one, and satisfies
`W A = T` and `W† T = A`.

Under the weaker **Gram domination** `T†T ≤ A²`, the same construction
is contractive, but need not be isometric, and only `W A = T` is asserted.
The canonical polar-factor interpretation requires a *positive* square
root `A = |T|`; self-adjointness alone does not identify `A` with `|T|`.

Based on the Apache-2.0 DKPS formalization (Kitware, Inc.).
-/

public section

namespace ContinuousLinearMap

open scoped InnerProductSpace

universe u v

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-! ### The isometry identity -/

/-- **A self-adjoint Gram square root has the same norms as the operator.**

`‖A x‖² = ⟪A x, A x⟫ = ⟪x, A² x⟫ = ⟪x, T⋆T x⟫ = ⟪T x, T x⟫ = ‖T x‖²`.  This is
the only consequence of the Gram identity that the whole construction uses. -/
theorem norm_apply_eq_of_gram_eq {T : E →L[𝕜] F} {A : E →L[𝕜] E}
    (hA : IsSelfAdjoint A) (hgram : A ∘L A = adjoint T ∘L T) (x : E) :
    ‖A x‖ = ‖T x‖ := by
  have hAadj : adjoint A = A := by
    rw [← ContinuousLinearMap.star_eq_adjoint]; exact hA.star_eq
  have hinner : ⟪A x, A x⟫_𝕜 = ⟪T x, T x⟫_𝕜 := by
    calc ⟪A x, A x⟫_𝕜 = ⟪x, adjoint A (A x)⟫_𝕜 := (adjoint_inner_right A x (A x)).symm
      _ = ⟪x, (A ∘L A) x⟫_𝕜 := by rw [hAadj, ContinuousLinearMap.comp_apply]
      _ = ⟪x, (adjoint T ∘L T) x⟫_𝕜 := by rw [hgram]
      _ = ⟪x, adjoint T (T x)⟫_𝕜 := by rw [ContinuousLinearMap.comp_apply]
      _ = ⟪T x, T x⟫_𝕜 := adjoint_inner_right T x (T x)
  have hsq : ‖A x‖ * ‖A x‖ = ‖T x‖ * ‖T x‖ := by
    have h := congrArg RCLike.re hinner
    rwa [inner_self_eq_norm_mul_norm, inner_self_eq_norm_mul_norm] at h
  exact (mul_self_inj (norm_nonneg _) (norm_nonneg _)).mp hsq

/-! ### The initial space -/

/-- The closure of the range of `A`, the support of the Gram extension. -/
noncomputable def rangeTopologicalClosure (A : E →L[𝕜] E) : Submodule 𝕜 E :=
  (LinearMap.range A.toLinearMap).topologicalClosure

omit [CompleteSpace E] in
/-- Every value of `A` lies in the initial space. -/
theorem apply_mem_rangeTopologicalClosure (A : E →L[𝕜] E) (x : E) :
    A x ∈ A.rangeTopologicalClosure :=
  Submodule.le_topologicalClosure _ ⟨x, rfl⟩

/-- The initial space is complete, being a topological closure inside a complete
space.  This is what lets the isometry be extended to it by continuity. -/
instance instCompleteSpaceRangeTopologicalClosure (A : E →L[𝕜] E) :
    CompleteSpace A.rangeTopologicalClosure :=
  Submodule.topologicalClosure.completeSpace _

/-- `A`, corestricted to the initial space, where it has dense range. -/
noncomputable def corestrictRangeClosure (A : E →L[𝕜] E) :
    E →ₗ[𝕜] A.rangeTopologicalClosure :=
  LinearMap.codRestrict A.rangeTopologicalClosure A.toLinearMap
    A.apply_mem_rangeTopologicalClosure

omit [CompleteSpace E] in
/-- The corestriction has the same values as `A`; only its codomain changes. -/
@[simp]
theorem coe_corestrictRangeClosure_apply (A : E →L[𝕜] E) (x : E) :
    (A.corestrictRangeClosure x : E) = A x := (rfl)

omit [CompleteSpace E] in
/-- The corestriction has **dense** range: the initial space is defined as that
closure.  This is the hypothesis `LinearMap.extendOfNorm` needs. -/
theorem denseRange_corestrictRangeClosure (A : E →L[𝕜] E) :
    DenseRange A.corestrictRangeClosure := by
  rw [DenseRange, Subtype.dense_iff]
  have hsub : (LinearMap.range A.toLinearMap : Set E)
      ⊆ (Subtype.val '' Set.range A.corestrictRangeClosure) := by
    rintro _ ⟨x, rfl⟩
    exact ⟨A.corestrictRangeClosure x, ⟨x, rfl⟩, rfl⟩
  calc (A.rangeTopologicalClosure : Set E)
      = closure (LinearMap.range A.toLinearMap : Set E) :=
        Submodule.topologicalClosure_coe _
    _ ⊆ closure (Subtype.val '' Set.range A.corestrictRangeClosure) := closure_mono hsub

/-! ### The contraction -/

/-- The extension of `A x ↦ T x` to the closure of the range of `A`.
Its norm bounds and isometry property require the corresponding Gram hypotheses. -/
noncomputable def gramContractionOnRangeClosure (T : E →L[𝕜] F) (A : E →L[𝕜] E) :
    A.rangeTopologicalClosure →L[𝕜] F :=
  T.toLinearMap.extendOfNorm A.corestrictRangeClosure

/-- The Gram extension is `W₀ ∘ P`, with `P` the orthogonal projection
onto the closure of `range A`. Contractivity follows from Gram domination;
isometry on the initial space requires Gram equality. -/
noncomputable def gramContraction (T : E →L[𝕜] F) (A : E →L[𝕜] E) : E →L[𝕜] F :=
  T.gramContractionOnRangeClosure A ∘L A.rangeTopologicalClosure.orthogonalProjectionOnto

/-- The Gram extension vanishes on the orthogonal complement of the closed range of `A`. -/
theorem gramContraction_apply_eq_zero_of_mem_orthogonal
    (T : E →L[𝕜] F) (A : E →L[𝕜] E) (x : E)
    (hx : x ∈ A.rangeTopologicalClosureᗮ) : T.gramContraction A x = 0 := by
  rw [gramContraction, ContinuousLinearMap.comp_apply,
    Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr hx]
  simp

section GramHyp

variable {T : E →L[𝕜] F} {A : E →L[𝕜] E}
  (hA : IsSelfAdjoint A) (hgram : A ∘L A = adjoint T ∘L T)

include hA hgram

/-- The bound that makes the extension possible; it is in fact an equality. -/
theorem norm_apply_le_norm_corestrictRangeClosure (x : E) :
    ‖T.toLinearMap x‖ ≤ 1 * ‖A.corestrictRangeClosure x‖ := by
  rw [one_mul]
  exact le_of_eq (norm_apply_eq_of_gram_eq hA hgram x).symm

/-- The extension undoes `A` on its range: `W₀ (A x) = T x`. -/
theorem gramContractionOnRangeClosure_corestrictRangeClosure (x : E) :
    T.gramContractionOnRangeClosure A (A.corestrictRangeClosure x) = T x :=
  LinearMap.extendOfNorm_eq A.denseRange_corestrictRangeClosure
    ⟨1, norm_apply_le_norm_corestrictRangeClosure hA hgram⟩ x

/-- Under Gram equality, the extension preserves norms on the entire closed range of `A`. -/
theorem norm_gramContractionOnRangeClosure (z : A.rangeTopologicalClosure) :
    ‖T.gramContractionOnRangeClosure A z‖ = ‖z‖ := by
  have heq : Set.EqOn
      (fun w : A.rangeTopologicalClosure => ‖T.gramContractionOnRangeClosure A w‖)
      (fun w : A.rangeTopologicalClosure => ‖w‖)
      (Set.range A.corestrictRangeClosure) := by
    rintro _ ⟨x, rfl⟩
    rw [gramContractionOnRangeClosure_corestrictRangeClosure hA hgram]
    exact (norm_apply_eq_of_gram_eq hA hgram x).symm
  exact congrFun (Continuous.ext_on A.denseRange_corestrictRangeClosure
    (by fun_prop) (by fun_prop) heq) z

/-- Under Gram equality, `gramContraction T A` is isometric on the closed range of `A`. -/
theorem norm_gramContraction_apply_of_mem_rangeTopologicalClosure (x : E)
    (hx : x ∈ A.rangeTopologicalClosure) :
    ‖T.gramContraction A x‖ = ‖x‖ := by
  have hproj : A.rangeTopologicalClosure.orthogonalProjectionOnto x = ⟨x, hx⟩ := by
    apply Subtype.ext
    simpa using Submodule.starProjection_eq_self_iff.mpr hx
  rw [gramContraction, ContinuousLinearMap.comp_apply, hproj,
    norm_gramContractionOnRangeClosure hA hgram]
  rfl

/-- **The factorisation**: `W A = T`, pointwise. -/
theorem gramContraction_apply_apply (x : E) :
    T.gramContraction A (A x) = T x := by
  have hproj : A.rangeTopologicalClosure.orthogonalProjectionOnto (A x)
      = A.corestrictRangeClosure x := by
    apply Subtype.ext
    simpa using
      Submodule.starProjection_eq_self_iff.mpr (A.apply_mem_rangeTopologicalClosure x)
  rw [gramContraction, ContinuousLinearMap.comp_apply, hproj,
    gramContractionOnRangeClosure_corestrictRangeClosure hA hgram]

/-- **The factorisation**: `W ∘L A = T`. -/
theorem gramContraction_comp_right : T.gramContraction A ∘L A = T := by
  ext x
  exact gramContraction_apply_apply hA hgram x

/-- **The contraction bound**: `‖W‖ ≤ 1`.  Both factors are contractions — the
extension because the map it extends is isometric, the projection because it is
orthogonal. -/
theorem norm_gramContraction_le_one : ‖T.gramContraction A‖ ≤ 1 := by
  have haux : ‖T.gramContractionOnRangeClosure A‖ ≤ 1 :=
    LinearMap.opNorm_extendOfNorm_le A.denseRange_corestrictRangeClosure zero_le_one
      (norm_apply_le_norm_corestrictRangeClosure hA hgram)
  have hproj : ‖A.rangeTopologicalClosure.orthogonalProjectionOnto‖ ≤ 1 :=
    Submodule.orthogonalProjectionOnto_norm_le _
  calc ‖T.gramContraction A‖
      ≤ ‖T.gramContractionOnRangeClosure A‖ *
        ‖A.rangeTopologicalClosure.orthogonalProjectionOnto‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 1 := mul_le_mul haux hproj (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- The inner-product identity behind `W⋆ T = A`, stated on the initial space so
that it can be proved on the dense range of `A` and transported by continuity. -/
theorem inner_gramContractionOnRangeClosure (x : E) (z : A.rangeTopologicalClosure) :
    ⟪T x, T.gramContractionOnRangeClosure A z⟫_𝕜 = ⟪A x, (z : E)⟫_𝕜 := by
  have hAadj : adjoint A = A := by
    rw [← ContinuousLinearMap.star_eq_adjoint]; exact hA.star_eq
  have heq : Set.EqOn
      (fun w : A.rangeTopologicalClosure => ⟪T x, T.gramContractionOnRangeClosure A w⟫_𝕜)
      (fun w : A.rangeTopologicalClosure => ⟪A x, (w : E)⟫_𝕜)
      (Set.range A.corestrictRangeClosure) := by
    rintro _ ⟨w, rfl⟩
    simp only [gramContractionOnRangeClosure_corestrictRangeClosure hA hgram,
      coe_corestrictRangeClosure_apply]
    calc ⟪T x, T w⟫_𝕜 = ⟪x, adjoint T (T w)⟫_𝕜 := (adjoint_inner_right T x (T w)).symm
      _ = ⟪x, (adjoint T ∘L T) w⟫_𝕜 := by rw [ContinuousLinearMap.comp_apply]
      _ = ⟪x, (A ∘L A) w⟫_𝕜 := by rw [hgram]
      _ = ⟪x, A (A w)⟫_𝕜 := by rw [ContinuousLinearMap.comp_apply]
      _ = ⟪x, adjoint A (A w)⟫_𝕜 := by rw [hAadj]
      _ = ⟪A x, A w⟫_𝕜 := adjoint_inner_right A x (A w)
  exact congrFun (Continuous.ext_on A.denseRange_corestrictRangeClosure
    (by fun_prop) (by fun_prop) heq) z

/-- **The reverse factorisation**: `W⋆ ∘L T = A`.

On the initial space this is the Gram identity read backwards; off it, both
sides vanish, `W` because it is zero there and `A` because its values lie in the
initial space. -/
theorem adjoint_gramContraction_comp_left :
    adjoint (T.gramContraction A) ∘L T = A := by
  ext x
  refine ext_inner_right 𝕜 fun y => ?_
  calc ⟪(adjoint (T.gramContraction A) ∘L T) x, y⟫_𝕜
      = ⟪T x, T.gramContraction A y⟫_𝕜 := by
        rw [ContinuousLinearMap.comp_apply, adjoint_inner_left]
    _ = ⟪T x, T.gramContractionOnRangeClosure A
          (A.rangeTopologicalClosure.orthogonalProjectionOnto y)⟫_𝕜 := by
        rw [gramContraction, ContinuousLinearMap.comp_apply]
    _ = ⟪A x, A.rangeTopologicalClosure.starProjection y⟫_𝕜 :=
        inner_gramContractionOnRangeClosure hA hgram x _
    _ = ⟪A.rangeTopologicalClosure.starProjection (A x), y⟫_𝕜 :=
        (Submodule.inner_starProjection_left_eq_right _ _ _).symm
    _ = ⟪A x, y⟫_𝕜 := by
        rw [Submodule.starProjection_eq_self_iff.mpr
          (A.apply_mem_rangeTopologicalClosure x)]

/-- The Gram extension is the unique bounded factor satisfying `WA = T` and
vanishing on the orthogonal complement of the closed range of `A`. -/
theorem eq_gramContraction_of_comp_right_and_orthogonal_eq_zero
    (W : E →L[𝕜] F) (hWA : W ∘L A = T)
    (hzero : ∀ x ∈ A.rangeTopologicalClosureᗮ, W x = 0) :
    W = T.gramContraction A := by
  have hon : ∀ z : A.rangeTopologicalClosure,
      W (z : E) = T.gramContraction A z := by
    have heq : Set.EqOn
        (fun z : A.rangeTopologicalClosure => W (z : E))
        (fun z : A.rangeTopologicalClosure => T.gramContraction A (z : E))
        (Set.range A.corestrictRangeClosure) := by
      rintro _ ⟨x, rfl⟩
      have hw := congrArg (fun K : E →L[𝕜] F => K x) hWA
      simpa only [ContinuousLinearMap.comp_apply, coe_corestrictRangeClosure_apply]
        using hw.trans (gramContraction_apply_apply hA hgram x).symm
    intro z
    exact congrFun (Continuous.ext_on A.denseRange_corestrictRangeClosure
      (by fun_prop) (by fun_prop) heq) z
  ext x
  set P := A.rangeTopologicalClosure.starProjection x with hP
  have hx : x - P ∈ A.rangeTopologicalClosureᗮ := by
    rw [hP]
    exact Submodule.sub_starProjection_mem_orthogonal x
  have hPx : P ∈ A.rangeTopologicalClosure := Submodule.starProjection_apply_mem _ _
  have hGzero : T.gramContraction A (x - P) = 0 :=
    gramContraction_apply_eq_zero_of_mem_orthogonal T A (x - P) hx
  calc
    W x = W P + W (x - P) := by rw [map_sub]; abel
    _ = W P := by rw [hzero _ hx, add_zero]
    _ = T.gramContraction A P := hon ⟨P, hPx⟩
    _ = T.gramContraction A P + T.gramContraction A (x - P) := by rw [hGzero, add_zero]
    _ = T.gramContraction A x := by rw [← map_add]; congr 1 <;> abel

/-- **A Gram factorisation produces a two-sided contractive equivalence.**

This is the packaged form: `T` and its self-adjoint Gram square root `A` are
contractive multiples of one another.  It is what a symmetric-norm-ideal
argument needs — an ideal gauge bounds `‖W‖ · gauge · ‖V‖`, so two-sided
domination by contractions forces the gauges of `T` and `A` to agree. -/
theorem exists_contraction_of_gram_eq :
    ∃ W : E →L[𝕜] F, ‖W‖ ≤ 1 ∧ ‖adjoint W‖ ≤ 1 ∧ W ∘L A = T ∧ adjoint W ∘L T = A :=
  ⟨T.gramContraction A, norm_gramContraction_le_one hA hgram,
    (LinearIsometryEquiv.norm_map _ _).trans_le (norm_gramContraction_le_one hA hgram),
    gramContraction_comp_right hA hgram, adjoint_gramContraction_comp_left hA hgram⟩

end GramHyp

/-! ### The one-sided version

Only `T⋆T ≤ A²` is assumed.  Every declaration here is the corresponding one
from the section above with the norm *equality* replaced by the norm
*inequality*; the underlying construction is reused verbatim. -/

section GramLeHyp

variable {T : E →L[𝕜] F} {A : E →L[𝕜] E}
  (hA : IsSelfAdjoint A) (hle : adjoint T ∘L T ≤ A ∘L A)

include hA hle

/-- **Gram domination bounds norms pointwise.**

`‖T x‖² = re ⟪T⋆T x, x⟫ ≤ re ⟪A² x, x⟫ = ‖A x‖²`, the middle step being exactly
positivity of `A² - T⋆T` applied at `x`.  This is the only consequence of the
hypothesis that the construction uses, which is why weakening the Gram identity
to an inequality costs nothing but the reverse factorisation. -/
theorem norm_apply_le_of_gram_le (x : E) : ‖T x‖ ≤ ‖A x‖ := by
  have hAadj : adjoint A = A := by
    rw [← ContinuousLinearMap.star_eq_adjoint]; exact hA.star_eq
  have hpos : (A ∘L A - adjoint T ∘L T).IsPositive :=
    ContinuousLinearMap.le_def.mp hle
  have hAA : ⟪x, A (A x)⟫_𝕜 = ⟪A x, A x⟫_𝕜 := by
    have h := adjoint_inner_right A x (A x)
    rwa [hAadj] at h
  have hTT : ⟪x, adjoint T (T x)⟫_𝕜 = ⟪T x, T x⟫_𝕜 := adjoint_inner_right T x (T x)
  have hsplit : ⟪x, (A ∘L A - adjoint T ∘L T) x⟫_𝕜 =
      ⟪A x, A x⟫_𝕜 - ⟪T x, T x⟫_𝕜 := by
    rw [_root_.sub_apply, inner_sub_right,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hAA, hTT]
  have hnn := hpos.re_inner_nonneg_right x
  rw [hsplit, map_sub, inner_self_eq_norm_mul_norm,
    inner_self_eq_norm_mul_norm] at hnn
  exact nonneg_le_nonneg_of_sq_le_sq (norm_nonneg _) (by linarith)

/-- The bound that makes the extension possible, under domination only. -/
theorem norm_apply_le_norm_corestrictRangeClosure_of_gram_le (x : E) :
    ‖T.toLinearMap x‖ ≤ 1 * ‖A.corestrictRangeClosure x‖ := by
  rw [one_mul]
  exact norm_apply_le_of_gram_le hA hle x

/-- The extension undoes `A` on its range: `W₀ (A x) = T x`. -/
theorem gramContractionOnRangeClosure_corestrictRangeClosure_of_gram_le (x : E) :
    T.gramContractionOnRangeClosure A (A.corestrictRangeClosure x) = T x :=
  LinearMap.extendOfNorm_eq A.denseRange_corestrictRangeClosure
    ⟨1, norm_apply_le_norm_corestrictRangeClosure_of_gram_le hA hle⟩ x

/-- **The factorisation**: `W A = T`, pointwise. -/
theorem gramContraction_apply_apply_of_gram_le (x : E) :
    T.gramContraction A (A x) = T x := by
  have hproj : A.rangeTopologicalClosure.orthogonalProjectionOnto (A x)
      = A.corestrictRangeClosure x := by
    apply Subtype.ext
    simpa using
      Submodule.starProjection_eq_self_iff.mpr (A.apply_mem_rangeTopologicalClosure x)
  rw [gramContraction, ContinuousLinearMap.comp_apply, hproj,
    gramContractionOnRangeClosure_corestrictRangeClosure_of_gram_le hA hle]

/-- **The factorisation**: `W ∘L A = T`. -/
theorem gramContraction_comp_right_of_gram_le : T.gramContraction A ∘L A = T := by
  ext x
  exact gramContraction_apply_apply_of_gram_le hA hle x

/-- **The contraction bound**: `‖W‖ ≤ 1`. -/
theorem norm_gramContraction_le_one_of_gram_le : ‖T.gramContraction A‖ ≤ 1 := by
  have haux : ‖T.gramContractionOnRangeClosure A‖ ≤ 1 :=
    LinearMap.opNorm_extendOfNorm_le A.denseRange_corestrictRangeClosure zero_le_one
      (norm_apply_le_norm_corestrictRangeClosure_of_gram_le hA hle)
  have hproj : ‖A.rangeTopologicalClosure.orthogonalProjectionOnto‖ ≤ 1 :=
    Submodule.orthogonalProjectionOnto_norm_le _
  calc ‖T.gramContraction A‖
      ≤ ‖T.gramContractionOnRangeClosure A‖ *
        ‖A.rangeTopologicalClosure.orthogonalProjectionOnto‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 1 := mul_le_mul haux hproj (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- **Gram domination produces a contractive factorisation.**

If `T⋆T ≤ A²` with `A` self-adjoint, then `T` factors through `A` by a
contraction.  This is the specialised Douglas factorisation: no functional
calculus, no square roots and no product space, because `A` is supplied as a
hypothesis rather than constructed.

It is deliberately **one-sided**.  The reverse identity `W⋆ ∘L T = A` of
`exists_contraction_of_gram_eq` is false under domination alone — `T = 0` with
`A ≠ 0` satisfies the hypothesis and forces `W⋆ T = 0 ≠ A`. -/
theorem exists_contraction_of_gram_le :
    ∃ W : E →L[𝕜] F, ‖W‖ ≤ 1 ∧ W ∘L A = T :=
  ⟨T.gramContraction A, norm_gramContraction_le_one_of_gram_le hA hle,
    gramContraction_comp_right_of_gram_le hA hle⟩

end GramLeHyp

end ContinuousLinearMap
