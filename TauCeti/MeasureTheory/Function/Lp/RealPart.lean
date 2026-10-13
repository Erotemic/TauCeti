/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import TauCeti.MeasureTheory.Function.Lp.Star
public import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity

/-!
# Real-valued classes inside RCLike-valued Lᵖ

The fixed points of pointwise conjugation are exactly the almost-everywhere real-valued
functions. The pointwise maps `RCLike.re` and `RCLike.ofReal` induce inverse linear isometries
between real Lᵖ and the real submodule of star-fixed RCLike-valued Lᵖ classes.

For complex values with a nonzero fixed part, this fixed subspace is not closed under
complex scalar multiplication. For real values, conjugation is trivial and the fixed
part is the whole Lᵖ space.
-/

public section

open MeasureTheory

open scoped ENNReal ComplexConjugate

namespace TauCeti

variable {K : Type*} [RCLike K] {p : ℝ≥0∞} {α : Type*} [MeasurableSpace α] {μ : Measure α}

section StarFixed

/-- **A `star`-fixed `Lᵖ` class is almost everywhere real**, in the form that recovers the
class from its real part.  This is the direction that does the work: it is what lets a real
representative be chosen. -/
theorem ae_ofReal_re_eq_of_star_eq_self {F : Lp K p μ} (hF : star F = F) :
    ∀ᵐ x ∂μ, ((RCLike.re ((F : α → K) x) : ℝ) : K) = (F : α → K) x := by
  have h := Lp.coeFn_star F
  rw [hF] at h
  filter_upwards [h] with x hx
  have hconj : conj ((F : α → K) x) = (F : α → K) x := by
    simpa [Pi.star_apply, RCLike.star_def] using hx.symm
  exact RCLike.conj_eq_iff_re.mp hconj

/-- The converse of `ae_ofReal_re_eq_of_star_eq_self`: an almost everywhere real class is
`star`-fixed. -/
theorem star_eq_self_of_ae_ofReal_re_eq {F : Lp K p μ}
    (h : ∀ᵐ x ∂μ, ((RCLike.re ((F : α → K) x) : ℝ) : K) = (F : α → K) x) :
    star F = F := by
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_star F, h] with x hx hre
  rw [hx]
  simpa [Pi.star_apply, RCLike.star_def] using RCLike.conj_eq_iff_re.mpr hre

/-- `star F = F` exactly when `F` has an almost everywhere real representative.** -/
theorem star_eq_self_iff_ae_ofReal_re_eq {F : Lp K p μ} :
    star F = F ↔ ∀ᵐ x ∂μ, ((RCLike.re ((F : α → K) x) : ℝ) : K) = (F : α → K) x :=
  ⟨ae_ofReal_re_eq_of_star_eq_self, star_eq_self_of_ae_ofReal_re_eq⟩

/-- The `im = 0` phrasing of `star_eq_self_iff_ae_ofReal_re_eq`.  Kept separate because the
two phrasings are convenient at different call sites: this one is the cheap test, the other
carries the real representative. -/
theorem star_eq_self_iff_ae_im_eq_zero {F : Lp K p μ} :
    star F = F ↔ ∀ᵐ x ∂μ, RCLike.im ((F : α → K) x) = 0 := by
  rw [star_eq_self_iff_ae_ofReal_re_eq]
  constructor
  · intro h
    filter_upwards [h] with x hx
    exact RCLike.conj_eq_iff_im.mp (RCLike.conj_eq_iff_re.mpr hx)
  · intro h
    filter_upwards [h] with x hx
    exact RCLike.conj_eq_iff_re.mp (RCLike.conj_eq_iff_im.mpr hx)

end StarFixed

section Maps

/-- **The real class attached to a complex one**: pointwise real part. -/
noncomputable def reLp (F : Lp K p μ) : Lp ℝ p μ :=
  (RCLike.reCLM : K →L[ℝ] ℝ).compLp F

/-- **The complex class attached to a real one**: pointwise `RCLike.ofReal`. -/
noncomputable def ofRealLp (f : Lp ℝ p μ) : Lp K p μ :=
  (RCLike.ofRealCLM : ℝ →L[ℝ] K).compLp f

/-- `reLp` is represented by the pointwise real part. -/
theorem coeFn_reLp (F : Lp K p μ) :
    ∀ᵐ x ∂μ, ((reLp F : Lp ℝ p μ) : α → ℝ) x = RCLike.re ((F : α → K) x) :=
  (RCLike.reCLM : K →L[ℝ] ℝ).coeFn_compLp F

/-- `ofRealLp` is represented by the pointwise coercion `ℝ → K`. -/
theorem coeFn_ofRealLp (f : Lp ℝ p μ) :
    ∀ᵐ x ∂μ, ((ofRealLp f : Lp K p μ) : α → K) x = (((f : α → ℝ) x : ℝ) : K) :=
  (RCLike.ofRealCLM : ℝ →L[ℝ] K).coeFn_compLp f

/-- `ofRealLp` is additive.  Stated unbundled, because consumers that also mention the
`ℝ`-module structure `Lp K p μ` inherits from `InnerProductSpace K` cannot use the bundled
`ofRealLpₗᵢ` without the two `Module ℝ` instances having to match syntactically. -/
theorem ofRealLp_add (f g : Lp ℝ p μ) :
    (ofRealLp (f + g) : Lp K p μ) = ofRealLp f + ofRealLp g :=
  map_add ((RCLike.ofRealCLM : ℝ →L[ℝ] K).compLpₗ p μ) f g

/-- `ofRealLp` is homogeneous for real scalars; stated unbundled for the same reason as
`ofRealLp_add`. -/
theorem ofRealLp_real_smul (r : ℝ) (f : Lp ℝ p μ) :
    (ofRealLp (r • f) : Lp K p μ) = r • ofRealLp f :=
  map_smul ((RCLike.ofRealCLM : ℝ →L[ℝ] K).compLpₗ p μ) r f

/-- `ofRealLp` carries a real scalar to the **coerced** scalar acting through the `K`-module
structure.  This is the form a descent argument wants: a complex space carries two `Module ℝ`
structures, and mentioning only the `K`-action is unambiguous.  Proved pointwise rather than by
transporting `ofRealLp_real_smul`, for exactly that reason. -/
theorem ofRealLp_coe_smul (r : ℝ) (f : Lp ℝ p μ) :
    (ofRealLp (r • f) : Lp K p μ) = (r : K) • ofRealLp f := by
  refine Lp.ext ?_
  filter_upwards [coeFn_ofRealLp (K := K) (r • f), Lp.coeFn_smul r f,
    Lp.coeFn_smul (r : K) (ofRealLp f : Lp K p μ), coeFn_ofRealLp (K := K) f] with x h1 h2 h3 h4
  rw [h1, h3, h2]
  simp [Pi.smul_apply, h4, RCLike.ofReal_mul]

/-- **The image of `ofRealLp` is `star`-fixed.** -/
theorem star_ofRealLp (f : Lp ℝ p μ) : star (ofRealLp f : Lp K p μ) = ofRealLp f := by
  refine star_eq_self_of_ae_ofReal_re_eq ?_
  filter_upwards [coeFn_ofRealLp (K := K) f] with x hx
  rw [hx, RCLike.ofReal_re]

/-- **`reLp` is a left inverse of `ofRealLp`**, with no hypothesis: the real part of a real
class is itself. -/
theorem reLp_ofRealLp (f : Lp ℝ p μ) : reLp (ofRealLp f : Lp K p μ) = f := by
  refine Lp.ext ?_
  filter_upwards [coeFn_reLp (ofRealLp f : Lp K p μ), coeFn_ofRealLp (K := K) f] with x h1 h2
  rw [h1, h2, RCLike.ofReal_re]

/-- **`reLp` is a right inverse of `ofRealLp` on the `star`-fixed classes**, and only there:
this is the direction that uses the characterization of star-fixed classes. -/
theorem ofRealLp_reLp_of_star_eq_self {F : Lp K p μ} (hF : star F = F) :
    (ofRealLp (reLp F) : Lp K p μ) = F := by
  refine Lp.ext ?_
  filter_upwards [coeFn_ofRealLp (K := K) (reLp F), coeFn_reLp F,
    ae_ofReal_re_eq_of_star_eq_self hF] with x h1 h2 h3
  rw [h1, h2]
  exact h3

/-- **`ofRealLp` preserves the norm**, because `‖(r : K)‖ = |r|` pointwise.  This is where the
statement stops being formal: no `compLp` of a general continuous linear map is isometric, and
Mathlib supplies only the bound `‖L.compLp f‖ ≤ ‖L‖ * ‖f‖`. -/
theorem norm_ofRealLp (f : Lp ℝ p μ) : ‖(ofRealLp f : Lp K p μ)‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  refine eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable (ofRealLp f : Lp K p μ))
    (Lp.aestronglyMeasurable f) ?_
  filter_upwards [coeFn_ofRealLp (K := K) f] with x hx
  rw [hx, RCLike.norm_ofReal, Real.norm_eq_abs]

end Maps

section Equiv

variable (K p μ) [Fact (1 ≤ p)]

/-- **The `star`-fixed classes of `Lp K p μ`, as an `ℝ`-submodule.**

Real scalars always preserve the fixed part. For `K = ℂ` with a nonzero fixed part,
multiplication by `i` does not preserve it; for `K = ℝ` or a trivial space,
this obstruction does not apply.  Mathlib cannot state this as `selfAdjoint (Lp K p μ)`,
which needs a `StarAddMonoid (Lp K p μ)` instance that does not exist; the carrier here is the
literal set `{F | star F = F}`, so `↥(starFixedSubmodule K p μ)` *is* the subtype
`{F : Lp K p μ // star F = F}`. -/
def starFixedSubmodule : Submodule ℝ (Lp K p μ) where
  carrier := {F | star F = F}
  zero_mem' := star_zero_lp
  add_mem' {F G} hF hG := by
    have hF' : star F = F := hF
    have hG' : star G = G := hG
    -- Membership unfolds to an equality of the underlying `Lp` values.
    change star (F + G) = F + G
    rw [star_add_lp, hF', hG']
  smul_mem' r F hF := by
    have hF' : star F = F := hF
    -- Membership unfolds to an equality of the underlying `Lp` values.
    change star (r • F) = r • F
    rw [star_real_smul_lp, hF']

variable {K p μ}

omit [Fact (1 ≤ p)] in
/-- Membership in `starFixedSubmodule` is `star F = F` on the nose; the carrier was chosen so
that this is `Iff.rfl` and consumers never see the submodule packaging. -/
@[simp]
theorem mem_starFixedSubmodule {F : Lp K p μ} :
    F ∈ starFixedSubmodule K p μ ↔ star F = F := Iff.rfl

variable (K p μ)

/-- Pointwise `RCLike.ofReal` as an `ℝ`-linear isometry `Lp ℝ p μ →ₗᵢ[ℝ] Lp K p μ`.**

The linear map is Mathlib's `ContinuousLinearMap.compLpₗ`; what is added is `norm_ofRealLp`,
since Mathlib has no isometric form of `compLp`. -/
noncomputable def ofRealLpₗᵢ : Lp ℝ p μ →ₗᵢ[ℝ] Lp K p μ where
  toLinearMap := (RCLike.ofRealCLM : ℝ →L[ℝ] K).compLpₗ p μ
  norm_map' f := norm_ofRealLp (K := K) f

/-- The bundled embedding acts as `ofRealLp`.  Written out rather than generated by `@[simps]`:
with the body unexposed `simps` cannot see the projection, and this is the lemma it would have
produced. -/
@[simp]
theorem ofRealLpₗᵢ_apply (f : Lp ℝ p μ) :
    ofRealLpₗᵢ K p μ f = (ofRealLp f : Lp K p μ) :=
  (rfl)

/-- **The range of the real embedding is exactly the `star`-fixed part.**  Both inclusions are
the inverse relations: `star_ofRealLp` one way, `ofRealLp_reLp_of_star_eq_self` the other. -/
theorem range_ofRealLpₗᵢ :
    LinearMap.range (ofRealLpₗᵢ K p μ).toLinearMap = starFixedSubmodule K p μ := by
  apply le_antisymm
  · rintro F ⟨f, rfl⟩
    exact star_ofRealLp (K := K) f
  · intro F hF
    exact ⟨reLp F, ofRealLp_reLp_of_star_eq_self hF⟩

/-- The resulting equivalence identifies the `star`-fixed part of a complex `Lᵖ` space
with real `Lᵖ`, linearly and isometrically over `ℝ`. Mathlib has no comparison between
`Lp ℝ p μ` and `Lp K p μ`, so this bridge is new.

The map is the pointwise real part; its inverse is the pointwise coercion `ℝ → K`.  Note that
`↥(starFixedSubmodule K p μ)` is by construction the subtype `{F : Lp K p μ // star F = F}`. -/
noncomputable def starFixedLpEquivRealLp :
    starFixedSubmodule K p μ ≃ₗᵢ[ℝ] Lp ℝ p μ where
  toFun F := reLp (F : Lp K p μ)
  map_add' F G := by
    -- Subtype addition is addition of the underlying `Lp` values.
    change reLp ((F : Lp K p μ) + (G : Lp K p μ)) = _
    exact map_add ((RCLike.reCLM : K →L[ℝ] ℝ).compLpₗ p μ) _ _
  map_smul' r F := by
    -- Subtype scalar multiplication uses the ambient real module.
    change reLp (r • (F : Lp K p μ)) = _
    exact map_smul ((RCLike.reCLM : K →L[ℝ] ℝ).compLpₗ p μ) r _
  invFun f := ⟨ofRealLp f, star_ofRealLp f⟩
  left_inv F := Subtype.ext (ofRealLp_reLp_of_star_eq_self F.2)
  right_inv f := reLp_ofRealLp f
  norm_map' F := by
    have h := norm_ofRealLp (K := K) (reLp (F : Lp K p μ))
    rw [ofRealLp_reLp_of_star_eq_self F.2] at h
    exact h.symm

/-- The equivalence acts as the pointwise real part, for the same reason `ofRealLpₗᵢ_apply` is
written out. -/
@[simp]
theorem starFixedLpEquivRealLp_apply (F : starFixedSubmodule K p μ) :
    starFixedLpEquivRealLp K p μ F = reLp (F : Lp K p μ) := (rfl)

/-- The inverse of the equivalence acts as the pointwise coercion `ℝ → K`.  This is the form
consumers need: it says the real class `f` sits inside `Lp K p μ` as `ofRealLp f` and nothing
else. -/
@[simp]
theorem starFixedLpEquivRealLp_symm_apply (f : Lp ℝ p μ) :
    ((starFixedLpEquivRealLp K p μ).symm f : Lp K p μ) = ofRealLp f := (rfl)

end Equiv

end TauCeti
