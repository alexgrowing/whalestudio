import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.Development

noncomputable section

open NumberField Formalism.MainNotions.S IsDedekindDomain
open scoped TensorProduct

namespace PI.ScRefExists.Id

def LocIdem : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (g : ℕ)
    (α β : v.adicCompletion F), 1 ≤ g → Valued.v ((g : ℕ) : v.adicCompletion F) < 1 →
    Valued.v α ≤ 1 → Valued.v β ≤ 1 →
    ∃ c₁ c₂ : v.adicCompletion F, Valued.v c₁ ≤ 1 ∧ Valued.v c₂ ≤ 1 ∧
      (1 + (g : v.adicCompletion F) * α) * (1 + g * c₁) ^ 2 - 2 * (1 + g * c₁) * (g * c₂) = 1 + g * c₁ ∧
      (g * c₂) ^ 2 - g * β * (1 + g * c₁) ^ 2 = -(g * c₂) ∧
      (g * c₂) ^ 2 - (1 + g * α) * (g * c₂) * (1 + g * c₁) + g * β * (1 + g * c₁) ^ 2 = 0

def AdIdem : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (g : ℕ) (α β : Af F), 1 ≤ g →
    α ∈ Formalism.UG.intAd F → β ∈ Formalism.UG.intAd F →
    ∃ C₁ C₂ : Af F, C₁ ∈ Formalism.UG.intAd F ∧ C₂ ∈ Formalism.UG.intAd F ∧
      (1 + (g : Af F) * α) * (1 + g * C₁) ^ 2 - 2 * (1 + g * C₁) * (g * C₂) = 1 + g * C₁ ∧
      (g * C₂) ^ 2 - g * β * (1 + g * C₁) ^ 2 = -(g * C₂) ∧
      (g * C₂) ^ 2 - (1 + g * α) * (g * C₂) * (1 + g * C₁) + g * β * (1 + g * C₁) ^ 2 = 0

def AdOfLoc : Prop := LocIdem → AdIdem

def FixInt : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (s : 𝓞 I.E), star (s : I.E) = s →
    ∃ a : 𝓞 I.F, algebraMap I.F I.E (a : I.F) = s

def TenStep : Prop := AdIdem → FixInt → PI.ScRefExists.Sk.IdemLift

theorem idemLift_of_steps (h1 : LocIdem) (h2 : AdOfLoc) (h3 : FixInt) (h4 : TenStep) :
    PI.ScRefExists.Sk.IdemLift := h4 (h2 h1) h3

end PI.ScRefExists.Id
