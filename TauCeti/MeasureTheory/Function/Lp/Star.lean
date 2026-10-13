/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5, GPT-5.6 Sol
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Star on Lᵖ spaces

Mathlib provides pointwise `Star` and the representative equation `Lp.coeFn_star`.
This module adds the norm, subtraction, isometry, and continuity properties of star.
For RCLike values, pointwise conjugation agrees with the induced real-linear map on Lᵖ;
this yields additivity, preservation of zero, and real-scalar homogeneity.

The corresponding real-vector-subspace equivalence is in `RealPart.lean`.
-/

public section

open MeasureTheory

namespace TauCeti

section GenericStar

variable {α R : Type*} [MeasurableSpace α]
variable [NormedAddCommGroup R] [StarAddMonoid R] [NormedStarGroup R]
variable {μ : Measure α} {p : ENNReal}

/-- Pointwise star preserves the `Lᵖ` norm. -/
theorem norm_star_lp (F : Lp R p μ) : ‖star F‖ = ‖F‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  refine eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable (star F))
    (Lp.aestronglyMeasurable F) ?_
  filter_upwards [Lp.coeFn_star F] with x hx
  rw [hx, Pi.star_apply, norm_star]

/-- Pointwise star preserves subtraction on `Lᵖ`.

Mathlib gives `Lp` the pointwise `Star` operation but not a `StarAddMonoid` instance, so this law
is recorded explicitly at the `Lp` level. -/
theorem star_sub_lp (F G : Lp R p μ) : star (F - G) = star F - star G := by
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_star (F - G), Lp.coeFn_sub F G,
    Lp.coeFn_sub (star F) (star G), Lp.coeFn_star F, Lp.coeFn_star G] with x h1 h2 h3 h4 h5
  rw [h1, h3]
  simp only [Pi.star_apply, Pi.sub_apply, h2, h4, h5, star_sub]

section Normed

variable [Fact (1 ≤ p)]

/-- Pointwise star is an isometry of `Lᵖ` for `p ≥ 1`. -/
theorem isometry_star_lp : Isometry (star : Lp R p μ → Lp R p μ) :=
  Isometry.of_dist_eq fun F G => by
    rw [dist_eq_norm, dist_eq_norm, ← star_sub_lp, norm_star_lp]

/-- Pointwise star is continuous on `Lᵖ` for `p ≥ 1`. -/
theorem continuous_star_lp : Continuous (star : Lp R p μ → Lp R p μ) :=
  isometry_star_lp.continuous

end Normed

end GenericStar

section RCLikeStar

variable {K : Type*} [RCLike K] {α : Type*} [MeasurableSpace α]
variable {p : ENNReal} {μ : Measure α}

section LpStar

/-- **`star` on `Lp K p μ` is `compLp` of the `ℝ`-linear conjugation of `K`.**

Mathlib gives `Lp` a bare `Star` and an `InvolutiveStar` and no `StarAddMonoid`, so none of the
algebraic laws for `star` are available and each would otherwise be proved from
representatives.  Identifying `star` with a `compLp` imports all of them at once from
`ContinuousLinearMap.compLpₗ`, which Mathlib has already proved linear. -/
theorem star_eq_compLp (F : Lp K p μ) :
    star F = ((RCLike.conjCLE (K := K)).toContinuousLinearMap).compLp F := by
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_star F,
    ((RCLike.conjCLE (K := K)).toContinuousLinearMap).coeFn_compLp F] with x h1 h2
  rw [h1, h2]
  simp [Pi.star_apply, RCLike.star_def]

/-- Pointwise conjugation on `Lᵖ` is additive.  Not available from Mathlib, which puts no
`StarAddMonoid` on `Lp`; see `star_eq_compLp`. -/
theorem star_add_lp (F G : Lp K p μ) : star (F + G) = star F + star G := by
  simp only [star_eq_compLp]
  exact map_add (((RCLike.conjCLE (K := K)).toContinuousLinearMap).compLpₗ p μ) F G

/-- Pointwise conjugation on `Lᵖ` kills zero. -/
theorem star_zero_lp : star (0 : Lp K p μ) = 0 := by
  simp only [star_eq_compLp]
  exact map_zero (((RCLike.conjCLE (K := K)).toContinuousLinearMap).compLpₗ p μ)

/-- Pointwise conjugation is homogeneous for real scalars. Over complex scalars it is
conjugate-linear, so its fixed part is naturally a real submodule; for `K = ℝ` it is also
`K`-linear. -/
theorem star_real_smul_lp (r : ℝ) (F : Lp K p μ) : star (r • F) = r • star F := by
  simp only [star_eq_compLp]
  exact map_smul (((RCLike.conjCLE (K := K)).toContinuousLinearMap).compLpₗ p μ) r F

end LpStar

end RCLikeStar

end TauCeti
