import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def GenFibreHomog.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω),
    GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomogIdeal
      ((mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ)))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
