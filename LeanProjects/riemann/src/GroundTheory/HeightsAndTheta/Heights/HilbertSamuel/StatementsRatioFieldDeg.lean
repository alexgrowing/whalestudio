import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ProjFrameGraphChart
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def RatioFieldDeg.Statement : Prop :=
  ∀ (ι : Type) (E₁ E₂ : Type) [Field E₁] [CharZero E₁] [Field E₂] [CharZero E₂] (u : ι → E₁) (v : ι → E₂)
    (D : ℕ) (e : Fin (D + 1) → ι), coordIdeal ℤ u = coordIdeal ℤ v → projDeg u e = projDeg v e

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
