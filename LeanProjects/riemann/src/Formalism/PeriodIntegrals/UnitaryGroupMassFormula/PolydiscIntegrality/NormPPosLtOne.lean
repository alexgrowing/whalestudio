import Mathlib
import Formalism.PeriodIntegrals.PolydiscInt

namespace PI.PolydiscIntegrality₂

def Hyp (p : ℕ) [Fact p.Prime] (n : ℕ) (a : (Fin n →₀ ℕ) → ℂ_[p]) : Prop :=
  ∀ z : Fin n → ℂ_[p], (∀ i, ‖z i‖ < 1) →
      Summable (fun α : Fin n →₀ ℕ => a α * ∏ i, z i ^ α i) ∧
      ‖∑' α : Fin n →₀ ℕ, a α * ∏ i, z i ^ α i‖ ≤ 1

def KeyBound : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (a : (Fin n →₀ ℕ) → ℂ_[p]), Hyp p n a →
    ∀ c : ℂ_[p], ‖c‖ < 1 → ∀ β : Fin n →₀ ℕ, ‖a β‖ * ‖c‖ ^ (∑ i, β i) ≤ 1

end PI.PolydiscIntegrality₂
