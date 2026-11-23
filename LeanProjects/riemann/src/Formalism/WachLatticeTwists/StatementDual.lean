import Formalism.CharacterColumnKernels.Statement

noncomputable section

namespace Formalism.RepresentationBoundsCohomology

def annKO (O : Type*) [CommRing O] [IsDomain O] {H : Type*} [AddCommGroup H] [Module O H]
    (S : Submodule O H) : Submodule O (H →ₗ[O] Formalism.NG.KO O) where
  carrier := {φ | ∀ x ∈ S, φ x = 0}
  add_mem' := by intro a b ha hb x hx; simp [ha x hx, hb x hx]
  zero_mem' := by intro x _; rfl
  smul_mem' := by intro c a ha x hx; simp [ha x hx]

def StatDualColength : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (H : Type*) [AddCommGroup H] [Module O H] [Module.Finite O H] (I M : Submodule O H), I ≤ M →
    Module.length O (annKO O I ⧸ (annKO O M).comap (annKO O I).subtype) =
      Module.length O (M ⧸ I.comap M.subtype)

end Formalism.RepresentationBoundsCohomology
