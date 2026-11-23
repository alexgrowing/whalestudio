import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NineStatements

open scoped Matrix ComplexOrder

def GramDetSandwich.Statement : Prop :=
  ∀ {N k : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) (A : Matrix (Fin N) (Fin k) ℂ) (c M : ℝ), 0 < c → H.PosDef →
    (H⁻¹ - (c : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosSemidef →
    ((M : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - H⁻¹).PosSemidef →
    M⁻¹ ^ k * (Aᴴ * A).det.re ≤ (Aᴴ * H * A).det.re ∧ (Aᴴ * H * A).det.re ≤ c⁻¹ ^ k * (Aᴴ * A).det.re

end GroundTheory.Heights₂.Heights.NineStatements
