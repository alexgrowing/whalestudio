import Formalism.LocalToGlobal.IndefiniteReal.PrincipalLevelFrame

noncomputable section

open NumberField

namespace Formalism.IndefR.principalLevelFrame

section SS

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
variable {A : Type} [AddCommGroup A] [Module ℂ A]

variable (L n) in

def CongNormal : Prop :=
  ∀ (N : ℕ) (u κ : Formalism.AUTREP.GAf L n), u ∈ ReciprocityTheory.Aut.Umax L n → Formalism.L2.NG.Cong L n N κ →
    Formalism.L2.NG.Cong L n N (u * κ * u⁻¹)

def fixN (ρ : Formalism.AUTREP.GAf L n →* Module.End ℂ A) (N : ℕ) : Submodule ℂ A where
  carrier := {a | ∀ κ, Formalism.L2.NG.Cong L n N κ → ρ κ a = a}
  zero_mem' := fun κ _ => map_zero _
  add_mem' := fun ha hb κ hκ => by rw [map_add, ha κ hκ, hb κ hκ]
  smul_mem' := fun c a ha κ hκ => by rw [map_smul, ha κ hκ]

structure UAdm (ρ : Formalism.AUTREP.GAf L n →* Module.End ℂ A) (B : A →ₗ⋆[ℂ] A →ₗ[ℂ] ℂ) : Prop where
  smooth : ∀ a, ∃ N : ℕ, 0 < N ∧ a ∈ fixN ρ N
  adm : ∀ N : ℕ, 0 < N → FiniteDimensional ℂ (fixN ρ N)
  herm : ∀ x y, B y x = star (B x y)
  pos : ∀ x, x ≠ 0 → 0 < (B x x).re
  inv : ∀ g x y, B (ρ g x) (ρ g y) = B x y

def IsEqvA (ρ : Formalism.AUTREP.GAf L n →* Module.End ℂ A) (π : Formalism.L2.NG.FinTyp L n) (Φ : π.S →ₗ[ℂ] A) : Prop :=
  ∀ (h : Formalism.AUTREP.GAf L n) (f : π.S), Φ ⟨Formalism.L2.NG.rt L n h f, π.stable h f f.2⟩ = ρ h (Φ f)

def isotA (ρ : Formalism.AUTREP.GAf L n →* Module.End ℂ A) (π : Formalism.L2.NG.FinTyp L n) : Submodule ℂ A :=
  ⨆ (Φ : π.S →ₗ[ℂ] A) (_ : IsEqvA ρ π Φ), LinearMap.range Φ

def SpanIsotA (ρ : Formalism.AUTREP.GAf L n →* Module.End ℂ A) : Prop :=
  ∀ a : A, a ∈ ⨆ π : Formalism.L2.NG.FinTyp L n, isotA ρ π

def OrthIsotA (ρ : Formalism.AUTREP.GAf L n →* Module.End ℂ A) (B : A →ₗ⋆[ℂ] A →ₗ[ℂ] ℂ) : Prop :=
  ∀ π π' : Formalism.L2.NG.FinTyp L n, ¬ π.Iso π' → ∀ x ∈ isotA ρ π, ∀ y ∈ isotA ρ π', B x y = 0

end SS

end Formalism.IndefR.principalLevelFrame
