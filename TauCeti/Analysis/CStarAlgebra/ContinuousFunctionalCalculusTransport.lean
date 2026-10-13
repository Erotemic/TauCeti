/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital

/-!
# Transporting a continuous functional calculus along a star-algebra equivalence

Let `Φ : A ≃⋆ₐ[R] B`.  The spectra of `a : A` and `Φ a` are equal subsets of `R`.
Consequently a continuous functional calculus on `B` for a predicate `q` induces one on `A`
for a predicate `p`, provided the predicates correspond along `Φ` and `Φ.symm` is continuous.

Only `Continuous Φ.symm` is required: the transported homomorphism is the calculus on `B`
followed by `Φ.symm`.  Its injectivity and spectral mapping property follow from
`AlgEquiv.spectrum_eq` and the corresponding properties on `B`.

The naturality law for evaluating a calculus under star-algebra homomorphisms is already
`StarAlgHomClass.map_cfc` in Mathlib and is not duplicated here.

Source: [Davis--Kahan / DKPS formalization](https://github.com/AIQ-Kitware/aiq-dkps-formalization),
`ForTauCeti/Analysis/CStarAlgebra/ContinuousFunctionalCalculusTransport.lean`.
-/

public section

namespace StarAlgEquiv

open ContinuousFunctionalCalculus

variable {R A B : Type*}
  [CommSemiring R] [StarRing R] [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R]
  [Ring A] [StarRing A] [TopologicalSpace A] [Algebra R A]
  [Ring B] [StarRing B] [TopologicalSpace B] [Algebra R B]
  {p : A → Prop} {q : B → Prop}

/-- The identity, read as a map from the spectrum of `a` to the spectrum of `Φ a`.  The two
spectra are equal as subsets of `R`, so this moves no points and is a bijection. -/
private def spectrumEquivMap (Φ : A ≃⋆ₐ[R] B) (a : A) :
    C(spectrum R (Φ a), spectrum R a) :=
  ⟨Set.inclusion (AlgEquiv.spectrum_eq Φ a).subset, continuous_inclusion _⟩

omit [StarRing R] [IsTopologicalSemiring R] [ContinuousStar R] [TopologicalSpace A]
  [TopologicalSpace B] in
private theorem spectrumEquivMap_surjective (Φ : A ≃⋆ₐ[R] B) (a : A) :
    Function.Surjective (spectrumEquivMap Φ a) := fun y =>
  ⟨⟨(y : R), by rw [AlgEquiv.spectrum_eq Φ a]; exact y.2⟩, Subtype.ext rfl⟩

/-- **A continuous functional calculus transports along an isomorphism of topological
`R`-`⋆`-algebras** that matches the two predicates.

Every field of the class is read off through `Φ`: spectra agree by `AlgEquiv.spectrum_eq`, so
the symbol algebras agree, and the calculus of `a` is the calculus of `Φ a` followed by
`Φ.symm`. -/
theorem continuousFunctionalCalculus [ContinuousFunctionalCalculus R B q]
    (Φ : A ≃⋆ₐ[R] B) (hΦsymm : Continuous Φ.symm) (hpq : ∀ a, p a ↔ q (Φ a)) :
    ContinuousFunctionalCalculus R A p := by
  have hspec : ∀ a : A, spectrum R (Φ a) = spectrum R a := fun a => AlgEquiv.spectrum_eq Φ a
  refine
    { predicate_zero := (hpq 0).2 (by
        rw [map_zero]
        exact ContinuousFunctionalCalculus.predicate_zero R (A := B))
      compactSpace_spectrum := fun a => ?_
      spectrum_nonempty := fun a ha => ?_
      exists_cfc_of_predicate := fun a ha => ?_ }
  · rw [← hspec a]
    exact ContinuousFunctionalCalculus.compactSpace_spectrum (R := R) (Φ a)
  · have : Nontrivial B := ⟨Φ 0, Φ 1, fun h => zero_ne_one (Φ.injective h)⟩
    rw [← hspec a]
    exact ContinuousFunctionalCalculus.spectrum_nonempty (R := R) (Φ a) ((hpq a).1 ha)
  · have hb : q (Φ a) := (hpq a).1 ha
    refine
      ⟨(Φ.symm.toStarAlgHom.comp
          ((cfcHom hb).comp (ContinuousMap.compStarAlgHom' R R (spectrumEquivMap Φ a)))),
        ?_, ?_, ?_, ?_, ?_⟩
    · exact hΦsymm.comp
        ((cfcHom_continuous hb).comp (ContinuousMap.continuous_precomp (spectrumEquivMap Φ a)))
    · intro f g hfg
      have h := cfcHom_injective hb (Φ.symm.injective hfg)
      refine ContinuousMap.ext fun x => ?_
      obtain ⟨y, rfl⟩ := spectrumEquivMap_surjective Φ a x
      exact congrFun (congrArg DFunLike.coe h) y
    · have hid : ((ContinuousMap.id R).restrict (spectrum R a)).comp (spectrumEquivMap Φ a) =
          (ContinuousMap.id R).restrict (spectrum R (Φ a)) := ContinuousMap.ext fun _ => rfl
      -- The goal is the application of a composite bundled star-algebra homomorphism.
      -- Expose that application once to rewrite the identity symbol via `hid`.
      change Φ.symm (cfcHom hb (((ContinuousMap.id R).restrict (spectrum R a)).comp
        (spectrumEquivMap Φ a))) = a
      rw [hid, cfcHom_id hb, Φ.symm_apply_apply]
    · intro f
      -- Expose the same bundled composite at a general symbol, allowing spectral mapping
      -- and surjectivity of `spectrumEquivMap` to finish the proof.
      change spectrum R (Φ.symm (cfcHom hb (f.comp (spectrumEquivMap Φ a)))) = Set.range f
      rw [AlgEquiv.spectrum_eq Φ.symm, cfcHom_map_spectrum hb]
      exact (spectrumEquivMap_surjective Φ a).range_comp f
    · intro f
      refine (hpq _).2 ?_
      -- The predicate field sees the application of the composite twice (after `Φ`).
      -- This conversion exposes the cancellation `Φ (Φ.symm _)` for `rw`.
      change q (Φ (Φ.symm (cfcHom hb (f.comp (spectrumEquivMap Φ a)))))
      rw [Φ.apply_symm_apply]
      exact cfcHom_predicate hb _

end StarAlgEquiv
