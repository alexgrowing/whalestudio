import Formalism.PeriodIntegrals.LatDefs

noncomputable section

namespace PI

namespace WeierUnif

def IsLat (Λ : AddSubgroup ℂ) : Prop :=
  DiscreteTopology Λ ∧ Submodule.span ℝ (Λ : Set ℂ) = ⊤

end WeierUnif

open WeierUnif

def WeierUnif : Prop :=
  ∀ a b : ℂ, a ^ 3 - 27 * b ^ 2 ≠ 0 →
    (∃ Λ : AddSubgroup ℂ, IsLat Λ ∧ g2 Λ = a ∧ g3 Λ = b) ∧
    ∀ Λ Λ' : AddSubgroup ℂ, IsLat Λ → IsLat Λ' → g2 Λ = a → g3 Λ = b → g2 Λ' = a → g3 Λ' = b →
      Λ = Λ'

end PI

end
