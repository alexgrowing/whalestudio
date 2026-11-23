import Formalism.LocalToGlobal.IndefiniteReal.CongNormal

noncomputable section

open NumberField

namespace Formalism.IndefR.principalLevelFrame

section SSP

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
variable {A : Type} [AddCommGroup A] [Module ℂ A]
variable {ρ : Formalism.AUTREP.GAf L n →* Module.End ℂ A} {B : A →ₗ⋆[ℂ] A →ₗ[ℂ] ℂ}

def StabA (ρ : Formalism.AUTREP.GAf L n →* Module.End ℂ A) (U : Submodule ℂ A) : Prop :=
  ∀ g, ∀ u ∈ U, ρ g u ∈ U

def perpA (B : A →ₗ⋆[ℂ] A →ₗ[ℂ] ℂ) (U : Submodule ℂ A) : Submodule ℂ A where
  carrier := {x | ∀ u ∈ U, B u x = 0}
  zero_mem' := fun u _ => map_zero _
  add_mem' := fun hx hy u hu => by rw [map_add, hx u hu, hy u hu, add_zero]
  smul_mem' := fun c x hx u hu => by rw [map_smul, hx u hu, smul_zero]

def lperp (B : A →ₗ⋆[ℂ] A →ₗ[ℂ] ℂ) (U : Submodule ℂ A) : Submodule ℂ A where
  carrier := {x | ∀ u ∈ U, B x u = 0}
  zero_mem' := fun u _ => by simp
  add_mem' := fun hx hy u hu => by rw [map_add, LinearMap.add_apply, hx u hu, hy u hu, add_zero]
  smul_mem' := fun c x hx u hu => by rw [map_smulₛₗ, LinearMap.smul_apply, hx u hu, smul_zero]

def cspan (ρ : Formalism.AUTREP.GAf L n →* Module.End ℂ A) (a : A) : Submodule ℂ A :=
  Submodule.span ℂ (Set.range fun g => ρ g a)

def IrrA (ρ : Formalism.AUTREP.GAf L n →* Module.End ℂ A) (X : Submodule ℂ A) : Prop :=
  StabA ρ X ∧ X ≠ ⊥ ∧ ∀ Y ≤ X, StabA ρ Y → Y = ⊥ ∨ Y = X

def Intw (π π' : Formalism.L2.NG.FinTyp L n) (T : π.S →ₗ[ℂ] π'.S) : Prop :=
  ∀ (h : Formalism.AUTREP.GAf L n) (f : π.S), T ⟨Formalism.L2.NG.rt L n h f, π.stable h f f.2⟩ =
    ⟨Formalism.L2.NG.rt L n h (T f), π'.stable h _ (T f).2⟩

end SSP

end Formalism.IndefR.principalLevelFrame
