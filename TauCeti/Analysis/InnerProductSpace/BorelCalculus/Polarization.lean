/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import TauCeti.Analysis.InnerProductSpace.BorelCalculus.DiagonalMeasure
import Mathlib.Tactic.Ring

/-!
# Polarized diagonal integrals

For a normal bounded operator `a` on a complex Hilbert space, the diagonal
spectral measures determine the matrix elements of its continuous functional
calculus by the complex polarization identity. The same four-term expression
can be formed for an arbitrary symbol on the spectrum; when the symbol is
continuous, it agrees with the continuous functional calculus.

This implements **SA-B04 (polarized pairing)** in the
`SelfAdjointSpectralTheory` roadmap. It adapts the existing proof from
`ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Polarization.lean` to
TauCeti's canonical `ContinuousLinearMap.diagMeasure` API.

The extension of this pairing to the bounded Borel functional calculus is a
separate roadmap target (SA-B05); this file makes no such claim.
-/

public section

open MeasureTheory
open scoped InnerProductSpace

namespace TauCeti
namespace BorelCalculus

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The complex polarization identity for the sesquilinear form of a bounded
operator, recovered from its diagonal quadratic form. -/
theorem inner_polarization (T : H →L[ℂ] H) (ψ ξ : H) :
    (1 / 4 : ℂ) *
        (⟪ξ + ψ, T (ξ + ψ)⟫_ℂ
          + Complex.I * ⟪ξ + Complex.I • ψ, T (ξ + Complex.I • ψ)⟫_ℂ
          - ⟪ξ - ψ, T (ξ - ψ)⟫_ℂ
          - Complex.I * ⟪ξ - Complex.I • ψ, T (ξ - Complex.I • ψ)⟫_ℂ)
      = ⟪ψ, T ξ⟫_ℂ := by
  simp only [map_add, map_sub, map_smul, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, Complex.conj_I]
  ring_nf
  rw [Complex.I_sq]
  ring

variable [CompleteSpace H]

/-- **SA-B04.** The polarized pairing of a symbol on the spectrum of a normal
bounded operator. For a continuous symbol it computes a matrix element of
`cfcHom`, as established by `pair_of_continuous` below. -/
noncomputable def pair (a : H →L[ℂ] H) [IsStarNormal a]
    (f : spectrum ℂ a → ℂ) (ψ ξ : H) : ℂ :=
  (1 / 4 : ℂ) *
    ((∫ x, f x ∂(a.diagMeasure (ξ + ψ)))
      + Complex.I * (∫ x, f x ∂(a.diagMeasure (ξ + Complex.I • ψ)))
      - (∫ x, f x ∂(a.diagMeasure (ξ - ψ)))
      - Complex.I * (∫ x, f x ∂(a.diagMeasure (ξ - Complex.I • ψ))))

/-- API for rewriting the polarized pairing without unfolding its definition. -/
theorem pair_def (a : H →L[ℂ] H) [IsStarNormal a]
    (f : spectrum ℂ a → ℂ) (ψ ξ : H) :
    pair a f ψ ξ = (1 / 4 : ℂ) *
      ((∫ x, f x ∂(a.diagMeasure (ξ + ψ)))
        + Complex.I * (∫ x, f x ∂(a.diagMeasure (ξ + Complex.I • ψ)))
        - (∫ x, f x ∂(a.diagMeasure (ξ - ψ)))
        - Complex.I * (∫ x, f x ∂(a.diagMeasure (ξ - Complex.I • ψ)))) :=
  (rfl)

/-- For continuous symbols, the polarized pairing is the matrix element of
the continuous functional calculus. -/
theorem pair_of_continuous (a : H →L[ℂ] H) [IsStarNormal a]
    (f : C(spectrum ℂ a, ℂ)) (ψ ξ : H) :
    pair a (fun x => f x) ψ ξ = ⟪ψ, cfcHom (a := a) ‹_› f ξ⟫_ℂ := by
  rw [pair_def,
    a.integral_diagMeasure_eq_inner_cfcHom (ξ + ψ) f,
    a.integral_diagMeasure_eq_inner_cfcHom (ξ + Complex.I • ψ) f,
    a.integral_diagMeasure_eq_inner_cfcHom (ξ - ψ) f,
    a.integral_diagMeasure_eq_inner_cfcHom (ξ - Complex.I • ψ) f]
  exact inner_polarization (cfcHom (a := a) ‹_› f) ψ ξ

end BorelCalculus
end TauCeti
