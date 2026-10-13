/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric

/-!
# Real algebra structure on bounded operators over `RCLike`

For a complete inner-product space `E` over `RCLike 𝕜`, scalar restriction along
`algebraMap ℝ 𝕜` gives the operator algebra `E →L[𝕜] E` an `ℝ`-algebra structure
compatible with its `𝕜`-scalar action.  This is one of the structures required
for the bounded self-adjoint real continuous functional calculus.

The structures below are definitions, **not global instances**.  Consumers may activate
them locally when they need the real functional calculus, without changing typeclass
synthesis for unrelated scalar multiplication on continuous linear maps:

```lean
attribute [local instance 100] ContinuousLinearMap.realAlgebra
  ContinuousLinearMap.realIsScalarTower
```

At `𝕜 = ℝ` or `𝕜 = ℂ`, these structures agree with the corresponding standard
Mathlib structures.  The instance priority permits Mathlib's canonical choices.

Developed for the Davis--Kahan / DKPS formalization by Jon Crall and Claude Opus 5
(Kitware, Inc.); this operator-algebra infrastructure was authored directly for the
scalar-generic construction.
-/

public section

namespace ContinuousLinearMap

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- **The operator algebra over an `RCLike` field is a real algebra**, by restriction of
scalars along `algebraMap ℝ 𝕜`.  Not an instance; see the module docstring. -/
@[expose, instance_reducible]
noncomputable def realAlgebra : Algebra ℝ (E →L[𝕜] E) :=
  RestrictScalars.algebra ℝ 𝕜 (E →L[𝕜] E)

attribute [local instance 100] realAlgebra

omit [CompleteSpace E] in
/-- The real action on operators factors through the `𝕜`-action.  Not an instance; see the
module docstring. -/
theorem realIsScalarTower : IsScalarTower ℝ 𝕜 (E →L[𝕜] E) :=
  RestrictScalars.isScalarTower ℝ 𝕜 (E →L[𝕜] E)

attribute [local instance 100] realIsScalarTower

/-! The complex case is an elaboration witness: activating the local structures above
suffices to synthesize Mathlib's real continuous functional calculus on bounded operators. -/

example {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] :
    ContinuousFunctionalCalculus ℝ (F →L[ℂ] F) IsSelfAdjoint := inferInstance

end ContinuousLinearMap
