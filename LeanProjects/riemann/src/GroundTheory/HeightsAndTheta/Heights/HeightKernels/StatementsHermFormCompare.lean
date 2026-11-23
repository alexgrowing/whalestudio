import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix
open scoped ComplexOrder

noncomputable section

def HermFormCompare.Statement : Prop :=
  ∀ (n : ℕ) (M N : Matrix (Fin n) (Fin n) ℂ), M.PosDef → N.PosDef →
    ∃ c : ℝ, 0 < c ∧ ∀ x : Fin n → ℂ, (star x ⬝ᵥ (M *ᵥ x)).re ≤ c * (star x ⬝ᵥ (N *ᵥ x)).re

example : (Matrix.diagonal ![(4 : ℂ), 1] : Matrix (Fin 2) (Fin 2) ℂ).PosDef ∧
    (1 : Matrix (Fin 2) (Fin 2) ℂ).PosDef :=
  ⟨Matrix.posDef_diagonal_iff.mpr fun j => by fin_cases j <;> norm_num, Matrix.PosDef.one⟩

end

end GroundTheory.Heights₂.Heights
