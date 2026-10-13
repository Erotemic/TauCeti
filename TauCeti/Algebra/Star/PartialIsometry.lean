/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 4.8
-/
module

public import Mathlib.Algebra.Star.StarProjection

/-!
# Partial isometries in star monoids

An element `u` of a star monoid is a partial isometry if `u * star u * u = u`.
In that case `star u * u` is a star projection, and partial isometries are
closed under the involution. The converse of the projection implication need
not hold in an arbitrary star monoid.

The operator specialization and the connection with norm preservation belong
in `TauCeti.Analysis.InnerProductSpace.PartialIsometry`.

This development was adapted from the Apache-2.0 DKPS formalization (Kitware, Inc.).
-/

public section

namespace TauCeti

/-- A partial isometry in a star monoid satisfies `u * star u * u = u`. -/
def IsPartialIsometry {R : Type*} [Monoid R] [StarMul R] (u : R) : Prop :=
  u * star u * u = u

/-- The defining star-monoid equation for a partial isometry. -/
theorem isPartialIsometry_iff {R : Type*} [Monoid R] [StarMul R] {u : R} :
    IsPartialIsometry u ↔ u * star u * u = u := Iff.rfl

namespace IsPartialIsometry

variable {R : Type*} [Monoid R] [StarMul R]

/-- The initial idempotent `_root_.star u * u` is a star projection. -/
theorem isStarProjection_star_mul_self {u : R} (hu : IsPartialIsometry u) :
    IsStarProjection (_root_.star u * u) :=
  isStarProjection_iff'.mpr
    ⟨by rw [mul_assoc, ← mul_assoc u (_root_.star u) u, hu], by rw [star_mul, _root_.star_star]⟩

/-- Taking the involution preserves partial isometries. -/
theorem star {u : R} (hu : IsPartialIsometry u) : IsPartialIsometry (_root_.star u) := by
  unfold IsPartialIsometry
  rw [_root_.star_star]
  have h := congrArg _root_.star hu
  rwa [star_mul, star_mul, _root_.star_star, ← mul_assoc] at h

/-- An element with `_root_.star u * u = 1` is a partial isometry. -/
theorem of_star_mul_self_eq_one {u : R} (h : _root_.star u * u = 1) : IsPartialIsometry u := by
  unfold IsPartialIsometry
  rw [mul_assoc, h, mul_one]

end IsPartialIsometry
end TauCeti

end
