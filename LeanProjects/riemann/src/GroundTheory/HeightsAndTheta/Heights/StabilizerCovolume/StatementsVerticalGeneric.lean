import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.LineField
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.HilbertSamuel

def VerticalGenericDeg.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P W : Ideal (MRing ι)) (d p : ℕ) (b : K → ℤ)
    (f g : MRing ι), IsArithVar P (d + 1) → p.Prime → IsVerticalDivisorAt P p b f g → IsArithVar W 2 → P ≤ W →
    genDeg W 1 b = 0

end GroundTheory.Heights₂.Heights.NineStatements
