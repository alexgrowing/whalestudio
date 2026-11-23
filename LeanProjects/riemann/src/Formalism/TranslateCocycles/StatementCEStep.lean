import Mathlib

namespace Formalism.CG

def CECondition : Prop :=
  ∀ (C CE f m N t η : ℝ), 0 ≤ C → 0 ≤ f → 0 ≤ m → 0 ≤ N → 0 ≤ t → t ≤ N → 0 ≤ η → 2 * C ≤ CE →
    C * f * m * N * (N + t) + C * f * m ^ 3 * η ≤ m * CE * f * (N ^ 2 + m ^ 2 * η)

def ColumnPlaceCE : Prop :=
  ∀ (J : Finset ℕ) (col vc C CE f m N t η : ℝ) (nn : ℕ → ℝ),
    0 ≤ C → 0 ≤ f → 0 ≤ m → 0 ≤ N → 0 ≤ t → t ≤ N → 0 ≤ η → 2 * C ≤ CE → vc = 0 →
    -(∑ j ∈ J, nn j) + vc - (C * f * m * N * (N + t) + C * f * m ^ 3 * η) ≤ col →
      -(∑ j ∈ J, nn j) - m * CE * f * (N ^ 2 + m ^ 2 * η) ≤ col

end Formalism.CG
