import Mathlib

noncomputable section

namespace Formalism.HermitianLattices.Ext.SupplyAP

def gExp (t : ℝ) : ℝ := 1 / (Real.exp t - 1) - 1 / t

def ExcBoundAt (A : ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (β : ℝ),
    χ ^ 2 = 1 → χ ≠ 1 → DirichletCharacter.LFunction χ (β : ℂ) = 0 → β ≤ 1 - c * (q : ℝ) ^ (-(A : ℝ))

end Formalism.HermitianLattices.Ext.SupplyAP
