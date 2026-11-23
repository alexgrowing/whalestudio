import Mathlib

noncomputable section

namespace PI.EF

def ZetaGrowth (C : ℝ) : Prop :=
  ∀ s : ℂ, -4 ≤ s.re → s.re ≤ 8 → ‖(s - 1) * riemannZeta s‖ ≤ C * (|s.im| + 2) ^ 7

end PI.EF
