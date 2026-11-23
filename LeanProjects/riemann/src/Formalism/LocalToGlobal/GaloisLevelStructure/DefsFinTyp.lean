import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP

namespace Formalism.L2.NG

variable (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)

structure FinTyp where
  S : Submodule ℂ (GAf L n → ℂ)
  stable : ∀ h, ∀ f ∈ S, rt L n h f ∈ S
  smooth : ∀ f ∈ S, ∃ N : ℕ, 0 < N ∧ ∀ κ, Cong L n N κ → rt L n κ f = f
  ne : S ≠ ⊥
  irr : ∀ S' : Submodule ℂ (GAf L n → ℂ), S' ≤ S → (∀ h, ∀ f ∈ S', rt L n h f ∈ S') → S' = ⊥ ∨ S' = S

variable {L n}

def FinTyp.Iso (π π' : FinTyp L n) : Prop := IsoRep π.S π'.S

end Formalism.L2.NG
