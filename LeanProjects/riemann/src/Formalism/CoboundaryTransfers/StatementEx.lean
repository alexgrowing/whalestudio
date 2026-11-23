import Formalism.CoboundaryTransfers.StatementAPI

noncomputable section

namespace Formalism.CoboundaryTransfers

def NonemptyG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∃ (B : Base ℤ_[p] (Polynomial ℤ_[p]))
    (W : WachMod B 0 (FractionRing (Polynomial ℤ_[p]))),
    B.p = p ∧ W.N ≠ ⊥ ∧ ¬ IsUnit B.X ∧ ¬ IsUnit B.Q ∧ B.φ B.X = B.X * B.Q ∧
    B.GammaX (-1) ∧ B.GammaQ ∧ (∃ x, W.γ x ≠ x)

end Formalism.CoboundaryTransfers
