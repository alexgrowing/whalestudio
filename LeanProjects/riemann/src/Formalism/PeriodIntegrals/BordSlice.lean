import Formalism.PeriodIntegrals.BordDefs

open Matrix

noncomputable section

namespace PI

open Formalism.QuantumDeterminants

def BordSlice : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ),
  inWb k r z → inWb k r z' → ∀ (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ), (∀ a, c a ≠ 0) → μ ∈ UH (Hb k) →
    omG k r z z' (bigCell k r c μ) = omF k r z z' c μ ∧ omG' k r z z' (bigCell k r c μ) = omF' k r z z' c μ

end PI
