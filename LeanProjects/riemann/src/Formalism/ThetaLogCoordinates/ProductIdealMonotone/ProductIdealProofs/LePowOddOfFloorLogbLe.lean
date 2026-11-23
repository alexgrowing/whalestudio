import Formalism.ThetaLogCoordinates.ProductIdealMonotone.ParamDefs

noncomputable section

open scoped BigOperators Classical

namespace Formalism.InvariantFactorPaths.G0

variable {n : ℕ}

theorem gam_le {p : ℝ} (hp : 5 ≤ p) : gam p ≤ 25 / (24 * p) := by
  unfold gam
  have h1 : 0 < p ^ 2 - 1 := by nlinarith
  have h2 : 0 < 24 * p := by linarith
  rw [div_le_div_iff₀ h1 h2]
  nlinarith

end Formalism.InvariantFactorPaths.G0
