import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsKodairaGeneric
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter

noncomputable section

def DiagonalSectionDifference.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ),
    1 ≤ D → IsArithVar (mCoordIdeal y) (D + 1) →
    ∃ C : ℝ, ∀ᶠ j : ℕ in atTop,
      (Module.finrank ℚ (chartLatQ y ((j : ℤ) • (1 : K → ℤ)) 1) : ℝ) ≤
        (Module.finrank ℚ (chartLatQ y ((j : ℤ) • (1 : K → ℤ) - 1) 1) : ℝ) + C * (j : ℝ) ^ (D - 1)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
