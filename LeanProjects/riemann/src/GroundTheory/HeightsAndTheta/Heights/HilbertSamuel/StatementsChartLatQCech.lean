import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsKodairaGeneric
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.GeneratedModOfSubsingleton
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def ChartLatQCech.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (d : ℕ) (b : K → ℤ),
    IsArithVar (mCoordIdeal y) d →
    Nonempty (chartLatQ y b 1 ≃ₗ[ℚ]
      KH.cechHc ι (KH.quotPart ℚ ((mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ)))) b 0)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
