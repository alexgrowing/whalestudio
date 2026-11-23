import Formalism.StatementOC

open Complex

noncomputable section

namespace Formalism.ZF

def ZeroFreeRegion : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ s : ℂ, s ≠ 1 → 1 - c / Real.log (|s.im| + 2) ≤ s.re → riemannZeta s ≠ 0

def LogDerivRegion : Prop :=
  ∃ c C : ℝ, 0 < c ∧ ∀ s : ℂ, s ≠ 1 → 1 - c / Real.log (|s.im| + 2) ≤ s.re →
    ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1)‖ ≤ C * Real.log (|s.im| + 2) ^ 2

def GzPNT : Prop :=
  ∃ c K : ℝ, 0 < c ∧ ∀ y : ℝ, 2 ≤ y →
    |Formalism.Gz y| ≤ K * y * Real.exp (-c * Real.sqrt (Real.log y))

end Formalism.ZF
