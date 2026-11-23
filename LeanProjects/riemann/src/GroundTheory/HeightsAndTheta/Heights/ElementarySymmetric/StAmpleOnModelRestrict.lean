import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsArithNakaiMoishezon
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

def AmpleOnModelRestrict.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω Ω' : Type) [Field Ω] [Field Ω']
    (y : (Σ k, ι k) → Ω) (y' : (Σ k, ι k) → Ω') (a : K → ℤ),
    mCoordIdeal y ≤ mCoordIdeal y' → IsAmpleOnModel y a → IsAmpleOnModel y' a

end

end GroundTheory.Heights₂.Heights.Targets
