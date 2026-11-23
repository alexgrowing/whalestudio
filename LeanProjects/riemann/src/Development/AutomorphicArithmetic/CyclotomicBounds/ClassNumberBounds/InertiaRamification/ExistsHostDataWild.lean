import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.QuadraticCharacterLegendreSymbol

namespace KStar.Ram

open DirichletCharacter

variable {N : ℕ}

noncomputable def realCycSup (n : ℕ) (Y : Subgroup (DirichletCharacter ℂ N)) :
    Subgroup (DirichletCharacter ℂ N) :=
  evenPart (condDvd N (4 * n)) ⊔ Y

noncomputable def hostCharsOf (n : ℕ) (ch ps : DirichletCharacter ℂ N)
    (Y : Subgroup (DirichletCharacter ℂ N)) : Subgroup (DirichletCharacter ℂ N) :=
  Subgroup.closure {ch, ps} ⊔ realCycSup n Y

def HostDataOf (n d q₁ : ℕ) (ch ps : DirichletCharacter ℂ N)
    (Y : Subgroup (DirichletCharacter ℂ N)) : Prop :=
  (∃ e, 2 ≤ e ∧ n = 2 ^ e) ∧ 4 * n ∣ N ∧ d.Prime ∧ d % 16 = 7 ∧ q₁.Prime ∧ q₁ % 8 = 3 ∧
    IsImagQuad ch d ∧ IsImagQuad ps q₁ ∧ ∀ ψ ∈ Y, ¬ d ∣ ψ.conductor ∧ ¬ q₁ ∣ ψ.conductor

end KStar.Ram
