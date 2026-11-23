import Formalism.PeriodIntegrals.BordDefs

open Matrix

noncomputable section

namespace PI

open Formalism.QuantumDeterminants

def BordInv : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ),
  inWb k r z → inWb k r z' → ∀ g, ∀ n ∈ Nset k r, ∀ n' ∈ Nset k r,
    omG k r z z' (n * g * n') = omG k r z z' g ∧ omG' k r z z' (n * g * n') = omG' k r z z' g

end PI
