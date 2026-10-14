/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.Dimension.Basic

/-!
# Scalar-field transport along an isomorphism of `RCLike` fields

For an isomorphism `e : RCLikeIso 𝕜 𝕂`, `ScalarTransport e E` has the same
underlying additive group as `E`, with the `𝕂`-action defined by
`c • x = e.symm c • x`. When `E` is normed, this preserves its topology and
norm; when `E` has an inner product, the inner product is transported using `e`.

The algebraic layer transports submodules, ranks, and partial linear maps.
The normed layer transports bounded operators and their operator norms.
The Hilbert layer transports orthogonality, orthogonal projections, and adjoints.
In particular, changing between isomorphic `RCLike` fields does not change
operator rank, domain membership, or adjoint and self-adjointness properties.

Unlike restriction of complex scalars to real scalars, this construction
renames *all* scalars and does not change module rank.

## Source

Developed for the Davis--Kahan/DKPS formalization
(https://github.com/AIQ-Kitware/aiq-dkps-formalization; Kitware, Inc.;
Apache 2.0), by Jon Crall and Claude Opus 5. The source development
is in `ForTauCeti/`.
-/

public section

open scoped InnerProductSpace

universe u w v v'

namespace TauCeti
/-- An isomorphism of `RCLike` fields fixing the reals and `I`. -/
structure RCLikeIso (𝕜 : Type u) (𝕂 : Type w) [RCLike 𝕜] [RCLike 𝕂] where
  /-- The underlying ring isomorphism. -/
  toRingEquiv : 𝕜 ≃+* 𝕂
  map_ofReal : ∀ r : ℝ, toRingEquiv (r : 𝕜) = (r : 𝕂)
  map_I : toRingEquiv (RCLike.I : 𝕜) = RCLike.I

namespace RCLikeIso

variable {𝕜 : Type u} {𝕂 : Type w} [RCLike 𝕜] [RCLike 𝕂]

/-- The isomorphism acts as a function. -/
instance : CoeFun (RCLikeIso 𝕜 𝕂) (fun _ => 𝕜 → 𝕂) := ⟨fun e => e.toRingEquiv⟩

/-- Reverse an isomorphism of `RCLike` fields. -/
def symm (e : RCLikeIso 𝕜 𝕂) : RCLikeIso 𝕂 𝕜 where
  toRingEquiv := e.toRingEquiv.symm
  map_ofReal r := by
    apply e.toRingEquiv.injective
    simp only [RingEquiv.apply_symm_apply, e.map_ofReal]
  map_I := by
    apply e.toRingEquiv.injective
    simp only [RingEquiv.apply_symm_apply, e.map_I]

/-- The inverse `RCLikeIso` acts by the inverse underlying ring equivalence. -/
@[simp] theorem symm_apply (e : RCLikeIso 𝕜 𝕂) (c : 𝕂) :
    e.symm c = e.toRingEquiv.symm c := (rfl)

/-- When `I = 0` the field is `ℝ`. -/
noncomputable def real (h : (RCLike.I : 𝕜) = 0) : RCLikeIso 𝕜 ℝ where
  toRingEquiv := RCLike.realRingEquiv h
  map_ofReal r := by simp
  map_I := by simp [h]

/-- When `im I = 1` the field is `ℂ`. -/
noncomputable def complex (h : RCLike.im (RCLike.I : 𝕜) = 1) : RCLikeIso 𝕜 ℂ where
  toRingEquiv := RCLike.complexRingEquiv h
  map_ofReal r := by simp
  map_I := by simp [h]

/-- The canonical real-field specialization maps a scalar to its real part. -/
@[simp] theorem real_apply (h : (RCLike.I : 𝕜) = 0) (x : 𝕜) :
    real h x = RCLike.re x := (rfl)

/-- The canonical complex-field specialization maps real and imaginary parts to `ℂ`. -/
@[simp] theorem complex_apply (h : RCLike.im (RCLike.I : 𝕜) = 1) (x : 𝕜) :
    complex h x = (RCLike.re x : ℂ) + (RCLike.im x : ℂ) * RCLike.I := (rfl)

/-- The isomorphism is determined by its action on the real and imaginary parts. -/
theorem apply_eq (e : RCLikeIso 𝕜 𝕂) (x : 𝕜) :
    e x = (RCLike.re x : 𝕂) + (RCLike.im x : 𝕂) * RCLike.I := by
  conv_lhs => rw [← RCLike.re_add_im x]
  rw [map_add, map_mul, e.map_ofReal, e.map_ofReal, e.map_I]

/-- Two `RCLike` isomorphisms are equal if they agree on every scalar. -/
@[ext] theorem ext {e f : RCLikeIso 𝕜 𝕂} (h : ∀ x, e x = f x) : e = f := by
  cases e with
  | mk φ hφ hI =>
    cases f with
    | mk ψ hψ hJ =>
      have heq : φ = ψ := RingEquiv.ext h
      cases heq
      rfl

/-- There is at most one `RCLike`-isomorphism between any two `RCLike` fields. -/
instance : Subsingleton (RCLikeIso 𝕜 𝕂) :=
  ⟨fun e f => ext fun x => (e.apply_eq x).trans (f.apply_eq x).symm⟩

/-- The underlying function is Mathlib's canonical `RCLike.map`. -/
@[simp] theorem coe_eq_map (e : RCLikeIso 𝕜 𝕂) :
    (e : 𝕜 → 𝕂) = (RCLike.map 𝕜 𝕂 : 𝕜 → 𝕂) := by
  funext x
  exact e.apply_eq x

/-- Reversing an `RCLike` isomorphism twice recovers the original. -/
@[simp] theorem symm_symm (e : RCLikeIso 𝕜 𝕂) : e.symm.symm = e :=
  Subsingleton.elim _ _

/-- The isomorphism preserves real parts. -/
@[simp] theorem re_map (e : RCLikeIso 𝕜 𝕂) (x : 𝕜) : RCLike.re (e x) = RCLike.re x := by
  rw [apply_eq]; simp

/-- `I` vanishes on one side exactly when it vanishes on the other. -/
theorem im_I_map (e : RCLikeIso 𝕜 𝕂) :
    RCLike.im (RCLike.I : 𝕂) = RCLike.im (RCLike.I : 𝕜) := by
  rcases RCLike.I_eq_zero_or_im_I_eq_one (K := 𝕜) with h | h
  · have : (RCLike.I : 𝕂) = 0 := by rw [← e.map_I, h, map_zero]
    simp [this, h]
  · have hI : (RCLike.I : 𝕜) ≠ 0 := by
      intro hz
      simp [hz] at h
    have hI' : (RCLike.I : 𝕂) ≠ 0 := by
      intro hz
      apply hI
      apply e.toRingEquiv.injective
      simpa only [e.map_I, map_zero] using hz
    rcases RCLike.I_eq_zero_or_im_I_eq_one (K := 𝕂) with h' | h'
    · exact absurd h' hI'
    · rw [h, h']

/-- The isomorphism preserves imaginary parts. -/
@[simp] theorem im_map (e : RCLikeIso 𝕜 𝕂) (x : 𝕜) : RCLike.im (e x) = RCLike.im x := by
  rw [apply_eq]; simp [e.im_I_map]

/-- The isomorphism preserves norms. -/
@[simp] theorem norm_map (e : RCLikeIso 𝕜 𝕂) (x : 𝕜) : ‖e x‖ = ‖x‖ := by
  have h1 : ‖e x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [RCLike.norm_sq_eq_def, RCLike.norm_sq_eq_def, e.re_map, e.im_map]
  nlinarith [norm_nonneg (e x), norm_nonneg x, h1]

/-- The isomorphism commutes with conjugation. -/
@[simp] theorem map_conj (e : RCLikeIso 𝕜 𝕂) (x : 𝕜) :
    e (starRingEnd 𝕜 x) = starRingEnd 𝕂 (e x) := by
  rw [apply_eq, apply_eq]; simp [RCLike.conj_re, RCLike.conj_im]

/-- The inverse isomorphism preserves norms. -/
@[simp] theorem norm_symm_map (e : RCLikeIso 𝕜 𝕂) (c : 𝕂) :
    ‖e.symm c‖ = ‖c‖ :=
  e.symm.norm_map c

/-- The isomorphism is an isometry. -/
theorem isometry (e : RCLikeIso 𝕜 𝕂) : Isometry (e : 𝕜 → 𝕂) :=
  AddMonoidHomClass.isometry_of_norm (e.toRingEquiv : 𝕜 →+* 𝕂) e.norm_map

/-- The inverse underlying ring equivalence preserves norms. -/
@[simp] theorem norm_toRingEquiv_symm_map (e : RCLikeIso 𝕜 𝕂) (c : 𝕂) :
    ‖e.toRingEquiv.symm c‖ = ‖c‖ := by
  simpa only [symm_apply] using e.norm_symm_map c

/-- The field isomorphism is a homeomorphism. -/
noncomputable def homeomorph (e : RCLikeIso 𝕜 𝕂) : 𝕜 ≃ₜ 𝕂 where
  toEquiv := e.toRingEquiv.toEquiv
  continuous_toFun := e.isometry.continuous
  continuous_invFun := by
    refine (AddMonoidHomClass.isometry_of_norm
      (e.toRingEquiv.symm : 𝕂 →+* 𝕜) fun c => ?_).continuous
    exact e.norm_toRingEquiv_symm_map c

/-- The homeomorphism is the isomorphism. -/
@[simp] theorem coe_homeomorph (e : RCLikeIso 𝕜 𝕂) : (e.homeomorph : 𝕜 → 𝕂) = e := by
  dsimp only [homeomorph]
  rfl

/-- The inverse homeomorphism is the inverse isomorphism. -/
@[simp] theorem homeomorph_symm_apply (e : RCLikeIso 𝕜 𝕂) (c : 𝕂) :
    (e.homeomorph.symm : 𝕂 → 𝕜) c = e.symm c := by
  dsimp only [homeomorph, RCLikeIso.symm, Homeomorph.symm, Equiv.symm]
  rfl

end RCLikeIso

/-- The type `E` with its scalars transported across `e : RCLikeIso 𝕜 𝕂`.

This is definitionally the same type as `E`, but equipped with a `𝕂`-module
structure by restriction along `e.symm`. -/
@[expose]
def ScalarTransport {𝕜 : Type u} {𝕂 : Type w} [RCLike 𝕜] [RCLike 𝕂]
    (_e : RCLikeIso 𝕜 𝕂) (E : Type v) : Type v := E

namespace ScalarTransport

variable {𝕜 : Type u} {𝕂 : Type w} [RCLike 𝕜] [RCLike 𝕂] {e : RCLikeIso 𝕜 𝕂}
variable {E : Type v} {F : Type v'}

/-- The underlying identity map, into the transported type. -/
@[expose]
def of (x : E) : ScalarTransport e E := x

/-- The underlying identity map, out of the transported type. -/
@[expose]
def out (x : ScalarTransport e E) : E := x

/-- `out` followed by `of` is the identity. -/
@[simp] theorem of_out (x : ScalarTransport e E) : of (e := e) (out x) = x := rfl

/-- `of` followed by `out` is the identity. -/
@[simp] theorem out_of (x : E) : out (of (e := e) x) = x := rfl

/-! ## Algebraic scalar transport -/

section Algebraic

variable [AddCommMonoid E] [Module 𝕜 E]
variable [AddCommMonoid F] [Module 𝕜 F]

/-- Transport leaves the additive monoid unchanged. -/
instance : AddCommMonoid (ScalarTransport e E) := inferInstanceAs (AddCommMonoid E)

/-- Scalars act by applying the inverse field isomorphism. -/
instance : Module 𝕂 (ScalarTransport e E) :=
  Module.compHom E (e.toRingEquiv.symm : 𝕂 →+* 𝕜)

/-- Transported scalar multiplication in terms of the original action. -/
theorem smul_def (c : 𝕂) (x : ScalarTransport e E) :
    c • x = of (e := e) ((e.toRingEquiv.symm c) • out x) := rfl

/-- Reading transported scalar multiplication back gives the original action. -/
@[simp] theorem out_smul (c : 𝕂) (x : ScalarTransport e E) :
    out (c • x) = (e.toRingEquiv.symm c) • out x := rfl

omit [Module 𝕜 E] in
/-- The identity transport map respects addition. -/
@[simp] theorem of_add (x y : E) :
    of (e := e) (x + y) = of (e := e) x + of (e := e) y := rfl

omit [Module 𝕜 E] in
/-- Reading out respects addition. -/
@[simp] theorem out_add (x y : ScalarTransport e E) :
    out (x + y) = out x + out y := rfl

/-- The identity transport map intertwines the two scalar actions. -/
@[simp] theorem of_smul (c : 𝕜) (x : E) :
    of (e := e) (c • x) = e c • of (e := e) x := by
  simp only [smul_def, e.toRingEquiv.symm_apply_apply, out_of]

/-- A real scalar has the same action before and after transport. -/
@[simp] theorem ofReal_smul_of (r : ℝ) (x : E) :
    ((r : 𝕂)) • of (e := e) x = of (e := e) ((r : 𝕜) • x) := by
  have hreal := e.symm.map_ofReal r
  simp only [RCLikeIso.symm_apply] at hreal
  rw [smul_def, hreal, out_of]

/-! ### Submodules -/

/-- A `𝕜`-subspace of `E`, as a `𝕂`-subspace of the transport, with the same carrier. -/
def submodule (S : Submodule 𝕜 E) : Submodule 𝕂 (ScalarTransport e E) where
  carrier := {x | out x ∈ S}
  add_mem' := S.add_mem
  zero_mem' := S.zero_mem
  smul_mem' _ _ hx := S.smul_mem _ hx

/-- Membership in a transported subspace is membership in the original. -/
@[simp] theorem mem_submodule {S : Submodule 𝕜 E} {x : ScalarTransport e E} :
    x ∈ submodule (e := e) S ↔ out x ∈ S := Iff.rfl

/-- Read a transported subspace back over the original field. -/
def submoduleSymm (S : Submodule 𝕂 (ScalarTransport e E)) : Submodule 𝕜 E where
  carrier := {x | of (e := e) x ∈ S}
  add_mem' := S.add_mem
  zero_mem' := S.zero_mem
  smul_mem' c x hx := by
    have : (e c) • (of (e := e) x) ∈ S := S.smul_mem _ hx
    rwa [smul_def, e.toRingEquiv.symm_apply_apply] at this

/-- Membership in a subspace read back is membership in the original. -/
@[simp] theorem mem_submoduleSymm {S : Submodule 𝕂 (ScalarTransport e E)} {x : E} :
    x ∈ submoduleSymm S ↔ of (e := e) x ∈ S := Iff.rfl

/-- The submodule transports are mutually inverse. -/
@[simp] theorem submoduleSymm_submodule (S : Submodule 𝕜 E) :
    submoduleSymm (submodule (e := e) S) = S := by
  ext x
  simp only [mem_submoduleSymm, mem_submodule, out_of]

/-- The submodule transports are mutually inverse. -/
@[simp] theorem submodule_submoduleSymm (S : Submodule 𝕂 (ScalarTransport e E)) :
    submodule (e := e) (submoduleSymm S) = S := by
  ext x
  simp only [mem_submodule, mem_submoduleSymm, of_out]

/-- Scalar transport induces an order isomorphism of submodule lattices. -/
def submoduleOrderIso : Submodule 𝕜 E ≃o Submodule 𝕂 (ScalarTransport e E) where
  toFun := submodule
  invFun := submoduleSymm
  left_inv := submoduleSymm_submodule
  right_inv := submodule_submoduleSymm
  map_rel_iff' := by
    intro S T
    -- Expose the order-isomorphism's two carrier maps explicitly before
    -- converting transported submodule membership back to the original type.
    change (submodule (e := e) S ≤ submodule (e := e) T) ↔ (S ≤ T)
    constructor
    · intro h x hx
      have hx' : of (e := e) (x : E) ∈ submodule (e := e) S :=
        (mem_submodule (e := e)).mpr (by simpa only [out_of] using hx)
      have hy := (mem_submodule (e := e)).mp (h hx')
      simpa only [out_of] using hy
    · intro h x hx
      exact (mem_submodule (e := e)).mpr (h ((mem_submodule (e := e)).mp hx))

/-- Transporting a submodule preserves inclusion. -/
theorem submodule_mono {S T : Submodule 𝕜 E} (hST : S ≤ T) :
    submodule (e := e) S ≤ submodule (e := e) T :=
  (submoduleOrderIso (e := e)).monotone hST

/-- The transport commutes with intersection of subspaces. -/
@[simp] theorem submodule_inf (S T : Submodule 𝕜 E) :
    submodule (e := e) (S ⊓ T) =
      submodule (e := e) S ⊓ submodule (e := e) T :=
  (submoduleOrderIso (e := e)).map_inf S T

/-- Scalar transport commutes with sums of subspaces. -/
@[simp] theorem submodule_sup (S T : Submodule 𝕜 E) :
    submodule (e := e) (S ⊔ T) =
      submodule (e := e) S ⊔ submodule (e := e) T :=
  (submoduleOrderIso (e := e)).map_sup S T

/-- Scalar transport sends the zero submodule to the zero submodule. -/
@[simp] theorem submodule_bot :
    submodule (e := e) (⊥ : Submodule 𝕜 E) = ⊥ :=
  (submoduleOrderIso (e := e)).map_bot

/-- Scalar transport sends the full submodule to the full submodule. -/
@[simp] theorem submodule_top :
    submodule (e := e) (⊤ : Submodule 𝕜 E) = ⊤ :=
  (submoduleOrderIso (e := e)).map_top


/-! ### Additive equivalence and rank -/

/-- The additive identity `E ≃+ ScalarTransport e E`. -/
def addEquiv : E ≃+ ScalarTransport e E where
  toFun := of
  invFun := out
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

omit [Module 𝕜 E] in
/-- Applying the additive transport is the `of` embedding. -/
@[simp] theorem addEquiv_apply (x : E) : addEquiv (e := e) x = of (e := e) x := by
  dsimp only [addEquiv]
  rfl

omit [Module 𝕜 E] in
/-- The inverse additive transport reads the vector back out. -/
@[simp] theorem addEquiv_symm_apply (x : ScalarTransport e E) :
    (addEquiv (e := e)).symm x = out (e := e) x := by
  dsimp only [addEquiv, AddEquiv.symm]
  rfl

/-- The additive identity intertwines the two scalar actions through `e`. -/
theorem addEquiv_smul (r : 𝕜) (x : E) :
    addEquiv (e := e) (r • x) = e r • addEquiv (e := e) x := by
  simpa only [addEquiv_apply] using (of_smul (e := e) r x)

-- A semilinear equivalence needs explicit inverse-pair instances for the
-- specific ring homomorphisms underlying the scalar-field isomorphism.
local instance : RingHomInvPair (e.toRingEquiv : 𝕜 →+* 𝕂)
    (e.toRingEquiv.symm : 𝕂 →+* 𝕜) :=
  RingHomInvPair.of_ringEquiv e.toRingEquiv

local instance : RingHomInvPair (e.toRingEquiv.symm : 𝕂 →+* 𝕜)
    (e.toRingEquiv : 𝕜 →+* 𝕂) :=
  RingHomInvPair.of_ringEquiv e.toRingEquiv.symm

/-- Scalar transport is semilinear for the underlying `RCLike` field isomorphism. -/
def semilinearEquiv : E ≃ₛₗ[(e.toRingEquiv : 𝕜 →+* 𝕂)] ScalarTransport e E where
  toFun := of
  invFun := out
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c x := of_smul (e := e) c x

/-- Restriction of the scalar-transport equivalence to a submodule. -/
def submoduleSemilinearEquiv (S : Submodule 𝕜 E) :
    S ≃ₛₗ[(e.toRingEquiv : 𝕜 →+* 𝕂)] submodule (e := e) S where
  toFun x := ⟨of (e := e) (x : E), by simpa only [mem_submodule, out_of] using x.2⟩
  invFun x := ⟨out (e := e) (x : ScalarTransport e E),
    by simpa only [mem_submodule] using x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c x := by
    apply Subtype.ext
    exact of_smul (e := e) c (x : E)

/-- Rank is unchanged by the transport: the scalar action is the same up to `e`. -/
theorem rank_eq (S : Submodule 𝕜 E) :
    Module.rank 𝕜 S = Module.rank 𝕂 (submodule (e := e) S) :=
  rank_eq_of_equiv_equiv (R := 𝕜) (R' := 𝕂) (M := S) (M₁ := submodule (e := e) S)
    (fun r => e r)
    (submoduleSemilinearEquiv S).toAddEquiv
    e.toRingEquiv.bijective
    (fun r m => (submoduleSemilinearEquiv S).map_smulₛₗ r m)


end Algebraic

/-! ### Partial linear maps -/

section PartialMaps

-- A partial linear map uses additive groups, unlike the submodule and rank
-- transport above, which works with arbitrary additive commutative monoids.
variable [AddCommGroup E] [Module 𝕜 E]
variable [AddCommGroup F] [Module 𝕜 F]

/-- The transported type inherits additive inverses without changing vectors. -/
instance : AddCommGroup (ScalarTransport e E) :=
  inferInstanceAs (AddCommGroup E)

/-- A point of the transported domain, read back in `A.domain`. -/
private def domainOut (A : E →ₗ.[𝕜] F) (x : submodule (e := e) A.domain) : A.domain :=
  ⟨out (x : ScalarTransport e E), x.2⟩

/-- Reading the transported-domain point back to the ambient vector. -/
private theorem domainOut_coe (A : E →ₗ.[𝕜] F) (x : submodule (e := e) A.domain) :
    (domainOut (e := e) A x : E) = out (e := e) (x : ScalarTransport e E) := by
  dsimp only [domainOut]

/-- A `𝕜`-linear partial map, as a `𝕂`-linear one on the transports:
the same domain and the same function. -/
def pmap (A : E →ₗ.[𝕜] F) : ScalarTransport e E →ₗ.[𝕂] ScalarTransport e F where
  domain := submodule (e := e) A.domain
  toFun :=
    { toFun := fun x => of (e := e) (A (domainOut (e := e) A x))
      map_add' := fun x y => congrArg (of (e := e)) (A.map_add _ _)
      map_smul' := fun c x => by
        -- The domain subtype is transported by the same scalar action as E.
        have hd : domainOut (e := e) A (c • x) =
            (e.toRingEquiv.symm c) • domainOut (e := e) A x := rfl
        -- The subtype's transported scalar action must be read through
        -- `domainOut` before the original map's scalar law can be used.
        change of (e := e) (A (domainOut (e := e) A (c • x))) =
          c • of (e := e) (A (domainOut (e := e) A x))
        rw [hd, A.map_smul, smul_def, out_of] }

/-- The transported partial map has the transported domain. -/
@[simp] theorem pmap_domain (A : E →ₗ.[𝕜] F) :
    (pmap (e := e) A).domain = submodule (e := e) A.domain := by
  dsimp only [pmap]

/-- Read a vector in the transported partial-map domain as a member of the original
partial-map domain. The underlying ambient vector is unchanged. -/
def pmapDomainOut (A : E →ₗ.[𝕜] F) (x : (pmap (e := e) A).domain) : A.domain :=
  ⟨out (x : ScalarTransport e E), by
    have hx : (x : ScalarTransport e E) ∈ submodule (e := e) A.domain := by
      rw [← pmap_domain]
      exact x.property
    exact (mem_submodule).mp hx⟩

/-- Reading a transported-domain point back preserves its ambient vector. -/
@[simp] theorem pmapDomainOut_coe (A : E →ₗ.[𝕜] F)
    (x : (pmap (e := e) A).domain) :
    (pmapDomainOut (e := e) A x : E) = out (e := e) (x : ScalarTransport e E) := by
  dsimp only [pmapDomainOut]

/-- The transported partial map has the original function. -/
@[simp] theorem pmap_apply (A : E →ₗ.[𝕜] F) (x : (pmap (e := e) A).domain) :
    pmap (e := e) A x = of (e := e) (A (pmapDomainOut (e := e) A x)) := by
  unfold pmap pmapDomainOut
  rfl

/-- The transport of partial maps is injective. -/
theorem pmap_injective : Function.Injective (pmap (e := e) (E := E) (F := F)) := by
  intro A B h
  have hdom : A.domain = B.domain := by
    have h0 := congrArg LinearPMap.domain h
    have := congrArg (submoduleSymm (e := e)) h0
    rwa [pmap_domain, pmap_domain, submoduleSymm_submodule, submoduleSymm_submodule] at this
  refine LinearPMap.ext hdom fun x hA hB => ?_
  have := LinearPMap.ext_iff.mp h
  obtain ⟨_, hval⟩ := this
  exact hval (x := of (e := e) x) (hf := hA) (hg := hB)


end PartialMaps

/-! ## Normed scalar transport -/

section Normed

variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The norm and topology are unchanged. -/
instance : NormedAddCommGroup (ScalarTransport e E) :=
  inferInstanceAs (NormedAddCommGroup E)

/-- The transported scalar action is compatible with the original norm. -/
noncomputable instance : NormedSpace 𝕂 (ScalarTransport e E) where
  norm_smul_le c x := by
    -- `ScalarTransport` is definitionally E, while the scalar action is
    -- defined by `Module.compHom`; this is the construction boundary.
    change ‖(e.toRingEquiv.symm c) • (out x)‖ ≤ ‖c‖ * ‖x‖
    rw [norm_smul, e.norm_toRingEquiv_symm_map]
    rfl

/-- Completeness only depends on the unchanged metric. -/
instance [CompleteSpace E] : CompleteSpace (ScalarTransport e E) :=
  inferInstanceAs (CompleteSpace E)

omit [NormedSpace 𝕜 E] in
/-- The transport does not change the norm of any vector. -/
@[simp] theorem norm_of (x : E) : ‖of (e := e) x‖ = ‖x‖ := rfl

/-! ### Bounded operators -/

/-- A `𝕜`-linear continuous map, as a `𝕂`-linear one on the transports. -/
def clm (T : E →L[𝕜] F) : ScalarTransport e E →L[𝕂] ScalarTransport e F where
  toFun x := of (e := e) (T (out x))
  map_add' _ _ := T.map_add _ _
  map_smul' _ _ := T.map_smul _ _
  cont := T.continuous

/-- The transported operator is the original function. -/
@[simp] theorem clm_apply (T : E →L[𝕜] F) (x : E) :
    clm (e := e) T (of x) = of (T x) := by
  dsimp only [clm]
  rfl

/-- Reading back an arbitrary transported operator application gives the original action. -/
@[simp] theorem out_clm_apply (T : E →L[𝕜] F) (x : ScalarTransport e E) :
    out (e := e) (clm (e := e) T x) = T (out (e := e) x) := by
  conv_lhs => rw [← of_out (e := e) x]
  rw [clm_apply, out_of]

/-- Scalar transport preserves addition of bounded operators. -/
@[simp] theorem clm_add (T R : E →L[𝕜] F) :
    clm (e := e) (T + R) = clm (e := e) T + clm (e := e) R := by
  ext x
  -- Compare the unchanged vector actions through the transport wrappers.
  change of (e := e) ((T + R) (out x)) =
    of (e := e) (T (out x)) + of (e := e) (R (out x))
  rw [add_apply, of_add]

/-- Scalar transport preserves the zero bounded operator. -/
@[simp] theorem clm_zero :
    clm (e := e) (0 : E →L[𝕜] F) = 0 := by
  ext x
  -- The zero map is unchanged as a function between transported carriers.
  change of (e := e) ((0 : E →L[𝕜] F) (out x)) = (0 : ScalarTransport e F)
  simp only [zero_apply]
  rfl

/-- Scalar transport commutes with negation of bounded operators. -/
@[simp] theorem clm_neg (T : E →L[𝕜] F) :
    clm (e := e) (-T) = -clm (e := e) T := by
  ext x
  -- Compare the unchanged vector actions through the transport wrappers.
  change of (e := e) ((-T) (out x)) = -(of (e := e) (T (out x)))
  rw [neg_apply]
  rfl

/-- Scalar transport preserves composition of bounded operators. -/
@[simp] theorem clm_comp {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    (T : F →L[𝕜] G) (R : E →L[𝕜] F) :
    clm (e := e) (T.comp R) = (clm (e := e) T).comp (clm (e := e) R) := by
  ext x
  -- Each transported operator acts on the same underlying vector.
  change of (e := e) (T (R (out x))) =
    of (e := e) (T (out (of (e := e) (R (out x)))))
  rw [out_of]

/-- Scalar transport preserves the identity bounded operator. -/
@[simp] theorem clm_id :
    clm (e := e) (ContinuousLinearMap.id 𝕜 E) =
      ContinuousLinearMap.id 𝕂 (ScalarTransport e E) := by
  ext x
  change of (e := e) (out x) = x
  exact of_out x

/-- The transport of operators is subtractive: it does not change the functions. -/
@[simp] theorem clm_sub (T R : E →L[𝕜] F) :
    clm (e := e) (T - R) = clm (e := e) T - clm (e := e) R := by
  ext x
  -- Both transported continuous maps have the original pointwise actions.
  change of (e := e) ((T - R) (out x)) =
    of (e := e) (T (out x)) - of (e := e) (R (out x))
  rw [sub_apply]
  rfl

/-- Transporting a bounded operator preserves its operator norm. -/
@[simp] theorem clm_norm (T : E →L[𝕜] F) : ‖clm (e := e) T‖ = ‖T‖ := by
  refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T) fun x => ?_)
    (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_)
  · exact T.le_opNorm (out x)
  · exact (clm (e := e) T).le_opNorm (of x)

/-- Transport of bounded operators is an additive equivalence of operator spaces. -/
def clmEquiv : (E →L[𝕜] F) ≃+ (ScalarTransport e E →L[𝕂] ScalarTransport e F) where
  toFun := clm
  invFun T :=
    { toFun := fun x => out (T (of (e := e) x))
      map_add' := fun _ _ => T.map_add _ _
      map_smul' := fun c x => by
        -- The goal is stated in transported terms; this conversion reads both
        -- sides back to the original field so the original `map_smul` and the
        -- transport scalar laws apply. The transport type is definitionally
        -- the original type, so no vector is moved.
        change out (T (of (e := e) (c • x))) = c • out (T (of (e := e) x))
        rw [of_smul, T.map_smul, out_smul, e.toRingEquiv.symm_apply_apply]
      cont := T.continuous }
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' T R := clm_add (e := e) T R

/-- Applying the operator equivalence is transport of the operator. -/
@[simp] theorem clmEquiv_apply (T : E →L[𝕜] F) :
    (clmEquiv (e := e)) T = clm (e := e) T := by
  dsimp only [clmEquiv]
  rfl

/-- Applying the inverse operator equivalence recovers the original vector action. -/
@[simp] theorem clmEquiv_symm_apply_apply
    (T : ScalarTransport e E →L[𝕂] ScalarTransport e F) (x : E) :
    ((clmEquiv (e := e)).symm T) x = out (e := e) (T (of (e := e) x)) := by
  dsimp only [clmEquiv, AddEquiv.symm]
  rfl


/-! ### Operator rank -/

/-- Transporting a bounded operator does not change its module rank. -/
theorem rank_clm_eq (T : E →L[𝕜] F) :
    LinearMap.rank ((clm (e := e) T : ScalarTransport e E →L[𝕂] ScalarTransport e F) :
        ScalarTransport e E →ₗ[𝕂] ScalarTransport e F) =
      LinearMap.rank (T : E →ₗ[𝕜] F) := by
  have hrange : LinearMap.range
      ((clm (e := e) T : ScalarTransport e E →L[𝕂] ScalarTransport e F) :
        ScalarTransport e E →ₗ[𝕂] ScalarTransport e F) =
      submodule (e := e) (LinearMap.range (T : E →ₗ[𝕜] F)) := by
    ext y
    simp only [LinearMap.mem_range, mem_submodule]
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨out x, ?_⟩
      -- `x` and `out x` denote the same ambient vector after scalar transport.
      change T (out x) = out (clm (e := e) T x)
      exact (out_clm_apply (e := e) T x).symm
    · rintro ⟨x, hx⟩
      refine ⟨of (e := e) x, ?_⟩
      calc
        clm (e := e) T (of (e := e) x) = of (e := e) (T x) := clm_apply T x
        _ = of (e := e) (out y) := congrArg (of (e := e)) hx
        _ = y := of_out y
  rw [LinearMap.rank, LinearMap.rank, hrange, ← rank_eq]


/-! ### Density of domains -/

/-- Density of the domain is unchanged: the carrier and the topology are. -/
theorem dense_pmap_domain_iff (A : E →ₗ.[𝕜] F) :
    Dense ((pmap (e := e) A).domain : Set (ScalarTransport e E)) ↔
      Dense (A.domain : Set E) := by
  have hcarrier :
      ((submodule (e := e) A.domain : Submodule 𝕂 (ScalarTransport e E)) :
          Set (ScalarTransport e E)) = (A.domain : Set E) := by
    ext x
    exact mem_submodule
  rw [pmap_domain, hcarrier]
  rfl


/-- The domain of a transported partial map is homeomorphic to its original domain;
the homeomorphism does not change the underlying vector. -/
def pmapDomainHomeomorph (A : E →ₗ.[𝕜] F) :
    (pmap (e := e) A).domain ≃ₜ A.domain where
  toFun := pmapDomainOut (e := e) A
  invFun x := ⟨of (e := e) (x : E), by
    rw [pmap_domain, mem_submodule, out_of]
    exact x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val

end Normed

/-! ## Inner-product scalar transport -/

section InnerProduct

variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- Transport the inner product by applying `e` to its value. -/
noncomputable instance : InnerProductSpace 𝕂 (ScalarTransport e E) where
  inner x y := e (inner 𝕜 (out x) (out y))
  norm_sq_eq_re_inner x := by
    -- The norm belongs to the unchanged additive metric structure.
    change ‖out x‖ ^ 2 = RCLike.re (e (inner 𝕜 (out x) (out x)))
    rw [e.re_map]
    exact norm_sq_eq_re_inner (𝕜 := 𝕜) _
  conj_inner_symm x y := by
    rw [← e.map_conj, inner_conj_symm]
  add_left x y z := by
    -- Both `out` and the addition on the transported type are identities.
    change e (inner 𝕜 (out x + out y) (out z)) =
      e (inner 𝕜 (out x) (out z)) + e (inner 𝕜 (out y) (out z))
    rw [inner_add_left, map_add]
  smul_left x y r := by
    -- The scalar action is `Module.compHom`; rewriting the inner-product
    -- structure field directly is not available during its construction.
    change e (inner 𝕜 (out (r • x)) (out y)) =
      starRingEnd 𝕂 r * e (inner 𝕜 (out x) (out y))
    rw [out_smul, inner_smul_left, map_mul, e.map_conj,
      e.toRingEquiv.apply_symm_apply]

/-- The transported inner product agrees with the original through `e`. -/
@[simp] theorem inner_of (x y : E) :
    inner 𝕂 (of (e := e) x) (of (e := e) y) = e (inner 𝕜 x y) := rfl

/-- The transported inner product of arbitrary transported vectors, expressed in the
original inner-product space. -/
@[simp] theorem inner_def (x y : ScalarTransport e E) :
    inner 𝕂 x y = e (inner 𝕜 (out x) (out y)) := by
  conv_lhs => rw [← of_out (e := e) x, ← of_out (e := e) y]
  rw [inner_of]

/-- The transport preserves orthogonal complements. -/
@[simp] theorem submodule_orthogonal (S : Submodule 𝕜 E) :
    (submodule (e := e) S)ᗮ = submodule (e := e) Sᗮ := by
  ext x
  simp only [Submodule.mem_orthogonal, mem_submodule]
  constructor
  · intro h y hy
    have h2 : inner 𝕂 (of (e := e) y) x = 0 :=
      h (of (e := e) y) (by simpa only [mem_submodule, out_of] using hy)
    have h3 : e (inner 𝕜 y (out x)) = 0 := by
      simpa only [inner_def, out_of] using h2
    exact e.toRingEquiv.injective (by simpa only [map_zero] using h3)
  · intro h y hy
    have h2 : inner 𝕜 (out y) (out x) = 0 :=
      h (out y) (by simpa only [mem_submodule] using hy)
    rw [inner_def, h2, map_zero]


/-! ### Orthogonal projections -/

/-- A transported subspace inherits its orthogonal projection. -/
instance hasOrthogonalProjection (S : Submodule 𝕜 E) [S.HasOrthogonalProjection] :
    (submodule (e := e) S).HasOrthogonalProjection where
  exists_orthogonal x := by
    obtain ⟨w, hw, hsub⟩ :=
      Submodule.HasOrthogonalProjection.exists_orthogonal (K := S) (out x)
    exact ⟨of (e := e) w,
      (mem_submodule (e := e)).mpr (by simpa only [out_of] using hw),
      by
        rw [submodule_orthogonal]
        exact (mem_submodule (e := e)).mpr (by
          -- The metric/additive structure is unchanged by scalar transport.
          change out x - w ∈ Sᗮ
          exact hsub)⟩

/-- Orthogonal projection onto a transported subspace acts as the original projection. -/
@[simp] theorem starProjection_of (S : Submodule 𝕜 E) [S.HasOrthogonalProjection] (x : E) :
    (submodule (e := e) S).starProjection (of (e := e) x) = of (e := e) (S.starProjection x) := by
  have hmem : S.starProjection x ∈ S := S.starProjection_apply_mem x
  have hperp : x - S.starProjection x ∈ Sᗮ := S.sub_starProjection_mem_orthogonal x
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (K := submodule (e := e) S)
    (u := of (e := e) x) (v := of (e := e) (S.starProjection x))
    (by simpa only [mem_submodule, out_of] using hmem) fun w hw => ?_
  have hinner : inner 𝕜 (x - S.starProjection x) (out w) = 0 :=
    (Submodule.mem_orthogonal' _ _).mp hperp (out w)
      (by simpa only [mem_submodule] using hw)
  -- The transported subtraction and coercion to the ambient space do not
  -- change underlying vectors; the inner-product output is mapped by `e`.
  change e (inner 𝕜 (x - S.starProjection x) (out w)) = 0
  rw [hinner, map_zero]


/-! ### Domains of adjoints -/

/-- The transported adjoint domain is the original one, because `e` is a homeomorphism. -/
theorem mem_pmap_adjointDomain_iff (A : E →ₗ.[𝕜] F) (y : ScalarTransport e F) :
    y ∈ (pmap (e := e) A).adjointDomain ↔ out y ∈ A.adjointDomain := by
  -- A transported domain is homeomorphic to the original domain.
  change Continuous (fun x : (pmap (e := e) A).domain =>
      inner 𝕂 y ((pmap (e := e) A) x)) ↔
    Continuous (fun x : A.domain => inner 𝕜 (out y) (A x))
  have hfun : (fun x : (pmap (e := e) A).domain =>
      inner 𝕂 y ((pmap (e := e) A) x)) =
      (fun x => e (inner 𝕜 (out y) (A (pmapDomainHomeomorph (e := e) A x)))) := by
    funext x
    rw [pmap_apply, inner_def, out_of]
    rfl
  rw [hfun]
  change Continuous (e.homeomorph ∘
      ((fun x : A.domain => inner 𝕜 (out y) (A x)) ∘
        pmapDomainHomeomorph (e := e) A)) ↔
    Continuous (fun x : A.domain => inner 𝕜 (out y) (A x))
  rw [e.homeomorph.comp_continuous_iff]
  exact (pmapDomainHomeomorph (e := e) A).comp_continuous_iff'

/-- The transported adjoint domain is the transport of the adjoint domain. -/
@[simp] theorem pmap_adjointDomain (A : E →ₗ.[𝕜] F) :
    (pmap (e := e) A).adjointDomain = submodule (e := e) A.adjointDomain :=
  SetLike.ext fun y => mem_pmap_adjointDomain_iff (e := e) A y


/-! ### Adjoints and self-adjointness -/

section Adjoints

variable [CompleteSpace E] [CompleteSpace F]

/-- The adjoint of a transported operator is the transport of its adjoint. -/
@[simp] theorem adjoint_clm (T : E →L[𝕜] F) :
    ContinuousLinearMap.adjoint (clm (e := e) T) =
      clm (e := e) (ContinuousLinearMap.adjoint T) := by
  refine ContinuousLinearMap.ext fun y => ?_
  refine ext_inner_left 𝕂 fun x => ?_
  rw [ContinuousLinearMap.adjoint_inner_right]
  -- Read both transported arguments through `of` and apply the public
  -- continuous-operator and inner-product transport laws.
  rw [← of_out (e := e) x, ← of_out (e := e) y]
  simp only [clm_apply, inner_of]
  exact congrArg e.toRingEquiv
    (ContinuousLinearMap.adjoint_inner_right T (out x) (out y)).symm

/-- Self-adjointness is preserved and reflected by the transport. -/
theorem isSelfAdjoint_clm_iff {T : E →L[𝕜] E} :
    IsSelfAdjoint (clm (e := e) T) ↔ IsSelfAdjoint T := by
  constructor
  · intro h
    have hc := adjoint_clm (e := e) T
    rw [ContinuousLinearMap.isSelfAdjoint_iff'.mp h] at hc
    refine ContinuousLinearMap.isSelfAdjoint_iff'.mpr ?_
    have : clm (e := e) (ContinuousLinearMap.adjoint T) = clm (e := e) T := hc.symm
    exact (clmEquiv (e := e)).injective this
  · intro h
    refine ContinuousLinearMap.isSelfAdjoint_iff'.mpr ?_
    rw [adjoint_clm, ContinuousLinearMap.isSelfAdjoint_iff'.mp h]

omit [CompleteSpace F] in
/-- The adjoint of a transported partial map is the transport of its adjoint. -/
theorem pmap_adjoint (A : E →ₗ.[𝕜] F) (hA : Dense (A.domain : Set E)) :
    (pmap (e := e) A).adjoint = pmap (e := e) A.adjoint := by
  have hA' : Dense ((pmap (e := e) A).domain : Set (ScalarTransport e E)) :=
    (dense_pmap_domain_iff (e := e) A).mpr hA
  refine LinearPMap.ext ?_ fun y hf hg => ?_
  · apply SetLike.ext
    intro y
    -- The adjoint-domain equality follows from its membership theorem,
    -- without inspecting the adjoint's classical value definition.
    change y ∈ (pmap (e := e) A).adjointDomain ↔ out y ∈ A.adjointDomain
    exact mem_pmap_adjointDomain_iff (e := e) A y
  refine LinearPMap.adjoint_apply_eq hA' ⟨y, hf⟩
    (x₀ := of (e := e) (A.adjoint ⟨out y, hg⟩))
    fun x => ?_
  -- The transported domain subtype and the original have identical
  -- underlying vectors; this conversion exposes the defining inner product.
  rw [pmap_apply (e := e) A x]
  -- Coercing the dependent adjoint-domain argument to its ambient space
  -- avoids rewriting inside `⟨y, hf⟩`, whose proof depends on `y`.
  change e (inner 𝕜 (A.adjoint ⟨out y, hg⟩) (out (x : ScalarTransport e E))) =
    e (inner 𝕜 (out y) (A (pmapDomainOut (e := e) A x)))
  exact congrArg e.toRingEquiv
    (LinearPMap.adjoint_isFormalAdjoint hA ⟨out y, hg⟩
      (pmapDomainOut (e := e) A x))

/-- Self-adjointness is preserved and reflected by the transport. -/
theorem isSelfAdjoint_pmap_iff {A : E →ₗ.[𝕜] E} :
    IsSelfAdjoint (pmap (e := e) A) ↔ IsSelfAdjoint A := by
  constructor
  · intro h
    have hdense : Dense (A.domain : Set E) := h.dense_domain
    have := LinearPMap.isSelfAdjoint_def.mp h
    rw [pmap_adjoint (e := e) A hdense] at this
    exact LinearPMap.isSelfAdjoint_def.mpr (pmap_injective (e := e) this)
  · intro h
    refine LinearPMap.isSelfAdjoint_def.mpr ?_
    rw [pmap_adjoint (e := e) A h.dense_domain, LinearPMap.isSelfAdjoint_def.mp h]


end Adjoints
end InnerProduct
end ScalarTransport
end TauCeti
