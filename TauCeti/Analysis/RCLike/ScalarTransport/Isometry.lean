/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import TauCeti.Analysis.RCLike.ScalarTransport.Basic

/-!
# Isometries of scalar-transported normed spaces

A linear isometric equivalence of normed spaces over `𝕜` induces one
between their `𝕂`-scalar transports. Transported submodule subtypes are
canonically isometric to subtypes of transported submodules. In Hilbert
spaces this identification also respects orthogonal complements.

## Source

Developed for the Davis--Kahan/DKPS formalization
(https://github.com/AIQ-Kitware/aiq-dkps-formalization; Kitware, Inc.;
Apache 2.0), by Jon Crall and Claude Opus 5.
-/

public section

namespace TauCeti
namespace ScalarTransport

universe u w v

variable {𝕜 : Type u} {𝕂 : Type w} [RCLike 𝕜] [RCLike 𝕂] {e : RCLikeIso 𝕜 𝕂}

section Normed

variable {X Y : Type v}
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- **A linear isometric equivalence transports.** -/
noncomputable def linearIsometryEquiv (f : X ≃ₗᵢ[𝕜] Y) :
    ScalarTransport e X ≃ₗᵢ[𝕂] ScalarTransport e Y where
  toFun x := of (e := e) (f (out (e := e) x))
  invFun y := of (e := e) (f.symm (out (e := e) y))
  left_inv x := by
    simpa only [out_of, f.symm_apply_apply] using (of_out (e := e) x)
  right_inv y := by
    simpa only [out_of, f.apply_symm_apply] using (of_out (e := e) y)
  map_add' x y := by
    simp only [out_add, f.map_add, of_add]
  map_smul' c x := by
    simp only [out_smul, f.map_smul, of_smul,
      e.toRingEquiv.apply_symm_apply, RingHom.id_apply]
  norm_map' x := f.norm_map _

/-- The transported equivalence acts through the original one. -/
@[simp] theorem linearIsometryEquiv_apply (f : X ≃ₗᵢ[𝕜] Y)
    (x : ScalarTransport e X) :
    linearIsometryEquiv (e := e) f x = of (e := e) (f (out (e := e) x)) := by
  dsimp only [linearIsometryEquiv]
  rfl

/-- The inverse acts through the inverse original equivalence. -/
@[simp] theorem linearIsometryEquiv_symm_apply (f : X ≃ₗᵢ[𝕜] Y)
    (y : ScalarTransport e Y) :
    (linearIsometryEquiv (e := e) f).symm y =
      of (e := e) (f.symm (out (e := e) y)) := by
  dsimp only [linearIsometryEquiv, Equiv.symm]
  rfl

/-- **The subtype of a transported subspace is the transport of the original subtype.**

`ScalarTransport.submodule S` keeps exactly the carrier of `S`, while
`ScalarTransport e S` transports the normed-space structure on the subtype itself.
This canonical isometry is the adapter between those two spellings.  The equivalence
identifies a submodule subtype with the corresponding subtype of the
transported ambient space, without changing underlying vectors. -/
noncomputable def submoduleSubtypeEquiv (S : Submodule 𝕜 X) :
    ScalarTransport e S ≃ₗᵢ[𝕂]
      (submodule (e := e) S : Submodule 𝕂 (ScalarTransport e X)) where
  toFun x := ⟨of (e := e) ((out (e := e) x : S) : X),
    by simpa only [mem_submodule, out_of] using (out (e := e) x : S).2⟩
  invFun y := of (e := e) (⟨out (e := e) (y : ScalarTransport e X),
    by simpa only [mem_submodule] using y.2⟩ : S)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' _ := rfl

/-- The transported-subspace adapter does not move the ambient vector. -/
@[simp] theorem submoduleSubtypeEquiv_coe_apply (S : Submodule 𝕜 X)
    (x : ScalarTransport e S) :
    (((submoduleSubtypeEquiv (e := e) S x :
        submodule (e := e) S) : ScalarTransport e X)) =
      of (e := e) (((out (e := e) x : S) : X)) := by
  dsimp only [submoduleSubtypeEquiv]
  rfl
/-- Nor does its inverse move the ambient vector. -/
@[simp] theorem submoduleSubtypeEquiv_symm_coe_apply (S : Submodule 𝕜 X)
    (x : submodule (e := e) S) :
    out (e := e) ((submoduleSubtypeEquiv (e := e) S).symm x) =
      (⟨out (e := e) (x : ScalarTransport e X),
        by simpa only [mem_submodule] using x.2⟩ : S) := by
  dsimp only [submoduleSubtypeEquiv, Equiv.symm]
  rfl


end Normed

section Orthogonal

-- Use the normed-space structure inherited from the inner-product space.
-- A separate `NormedSpace` parameter here would make the dependent Submodule
-- types incompatible with the orthogonality API.
variable {X : Type v} [NormedAddCommGroup X] [InnerProductSpace 𝕜 X]

/-- Transport of an orthogonal-complement subtype to the complement of
its transported parent submodule. It is the same ambient vector. -/
noncomputable def orthogonalSubmoduleSubtypeEquiv (S : Submodule 𝕜 X) :
    ScalarTransport e Sᗮ ≃ₗᵢ[𝕂]
      ((submodule (e := e) S)ᗮ : Submodule 𝕂 (ScalarTransport e X)) where
  toFun x := ⟨of (e := e) ((out (e := e) x : Sᗮ) : X), by
    rw [submodule_orthogonal]
    simpa only [mem_submodule, out_of] using (out (e := e) x : Sᗮ).2⟩
  invFun y := of (e := e) (⟨out (e := e) (y : ScalarTransport e X), by
    have hy : (y : ScalarTransport e X) ∈ submodule (e := e) Sᗮ := by
      rw [← submodule_orthogonal]
      exact y.2
    exact (mem_submodule (e := e)).mp hy⟩ : Sᗮ)
  -- The transport changes only scalar actions, not the carrier or norm.
  -- Both directions erase to the original vector, so these laws are reflexivity.
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' _ := rfl

/-- The orthogonal-subtype adapter preserves the ambient vector. -/
@[simp] theorem orthogonalSubmoduleSubtypeEquiv_coe_apply (S : Submodule 𝕜 X)
    (x : ScalarTransport e Sᗮ) :
    (((orthogonalSubmoduleSubtypeEquiv (e := e) S x :
        ((submodule (e := e) S)ᗮ : Submodule 𝕂 (ScalarTransport e X))) :
          ScalarTransport e X)) =
      of (e := e) (((out (e := e) x : Sᗮ) : X)) := by
  dsimp only [orthogonalSubmoduleSubtypeEquiv]
  rfl

/-- The inverse orthogonal-subtype adapter preserves the ambient vector. -/
@[simp] theorem orthogonalSubmoduleSubtypeEquiv_symm_coe_apply (S : Submodule 𝕜 X)
    (x : ((submodule (e := e) S)ᗮ : Submodule 𝕂 (ScalarTransport e X))) :
    (((out (e := e) ((orthogonalSubmoduleSubtypeEquiv (e := e) S).symm x) : Sᗮ) : X)) =
      out (e := e) (x : ScalarTransport e X) := by
  dsimp only [orthogonalSubmoduleSubtypeEquiv, Equiv.symm]
  rfl

end Orthogonal

end ScalarTransport
end TauCeti
