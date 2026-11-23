import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveSectionSupLower
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsArith
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def CurveFormNonvanishing.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (d : K → ℕ) (g : MRing ι),
    IsArithVar (mCoordIdeal y) 1 → IsMultiHomog g d → aeval y g ≠ 0 →
      ∀ z ∈ mcPts (mCoordIdeal y), eval z (map (Int.castRingHom ℂ) g) ≠ 0

end

end GroundTheory.Heights₂.Heights.Targets
