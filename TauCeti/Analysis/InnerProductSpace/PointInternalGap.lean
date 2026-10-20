/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import TauCeti.Analysis.InnerProductSpace.PointSpectrum

/-!
# Internal gaps between restricted point spectra

An internal point-spectrum gap of an endomorphism records an invariant subspace and a
uniform separation between the real eigenvalues carried by that subspace and those
carried by its orthogonal complement. Unlike an ordered gap, it does not prescribe
which spectral block lies above the other.

The predicate provides a common hypothesis for residual and spectral-subspace
perturbation estimates.

## References

* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a perturbation. III*,
  SIAM J. Numer. Anal. **7** (1970), 1–46.

Adapted from the Kitware DKPS formalization,
`ForTauCeti/Analysis/InnerProductSpace/Spectral/Gap.lean`.
-/

public section

open scoped InnerProductSpace

namespace Module.End

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {A : Module.End 𝕜 E} {U : Submodule 𝕜 E} {δ δ' : ℝ}

/-- An invariant subspace whose restricted point spectrum is separated by at least `δ`
from the restricted point spectrum of its orthogonal complement. -/
@[expose]
def PointInternalGap (A : Module.End 𝕜 E) (U : Submodule 𝕜 E) (δ : ℝ) : Prop :=
  (∀ x ∈ U, A x ∈ U) ∧ A.PointSpectraSeparated U A Uᗮ δ

/-- The selected subspace of an internal point-spectrum gap is invariant. -/
theorem PointInternalGap.invariant (h : A.PointInternalGap U δ) :
    ∀ x ∈ U, A x ∈ U :=
  h.1

/-- The selected and complementary restricted point spectra satisfy the gap bound. -/
theorem PointInternalGap.pointSpectraSeparated (h : A.PointInternalGap U δ) :
    A.PointSpectraSeparated U A Uᗮ δ :=
  h.2

/-- Weakening the separation bound preserves an internal point-spectrum gap. -/
theorem PointInternalGap.mono_gap (h : A.PointInternalGap U δ) (hδ : δ' ≤ δ) :
    A.PointInternalGap U δ' :=
  ⟨h.invariant, h.pointSpectraSeparated.mono le_rfl le_rfl hδ⟩

/-- An invariant subspace with an ordered gap from its complement has an internal gap. -/
theorem PointInternalGap.of_orderedGap (hU : ∀ x ∈ U, A x ∈ U)
    (h : A.PointOrderedGap U A Uᗮ δ) : A.PointInternalGap U δ :=
  ⟨hU, h.pointSpectraSeparated⟩

/-- Spectral containment in separated sets gives an internal point-spectrum gap. -/
theorem PointInternalGap.of_pointSpectrumIn {s t : Set ℝ}
    (hU : ∀ x ∈ U, A x ∈ U) (hs : A.PointSpectrumIn U s)
    (ht : A.PointSpectrumIn Uᗮ t)
    (hsep : ∀ a ∈ s, ∀ b ∈ t, δ ≤ |a - b|) : A.PointInternalGap U δ :=
  ⟨hU, PointSpectraSeparated.of_pointSpectrumIn hs ht hsep⟩

end Module.End
