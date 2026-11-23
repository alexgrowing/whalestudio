import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.CBFiLower

noncomputable section

open Finset

namespace Formalism.MainNotions.Ext.CutB

def cBCardNC : Prop :=
  ∀ (N : ℕ) (ε : Fin N → Bool), Fintype.card (cBNC ε) = cBp ε * cBq ε

def cBhsPP : Prop :=
  ∀ (N : ℕ) (ε : Fin N → Bool) (z : cBNC ε → ℂ), cBhs (cBpp ε z) = 2 * ∑ pr : cBNC ε, ‖z pr‖ ^ 2

def cBHCGap : Prop :=
  ∀ (N : ℕ) (lam : Fin N → ℝ) (c : ℝ), StrictAnti lam → (∀ a, ∃ m : ℤ, lam a - c = m) →
    ∀ a b : Fin N, a < b → ((b.val : ℝ) - a.val) ≤ lam a - lam b

end Formalism.MainNotions.Ext.CutB
