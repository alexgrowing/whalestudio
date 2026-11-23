import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def KrullDimMatAct.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] (J : Type) [Fintype J] (x : J → Ω) (B : Matrix J J ℚ), IsInvMat B →
    ringKrullDim (MvPolynomial J ℤ ⧸ coordIdeal ℤ (matAct B x)) = ringKrullDim (MvPolynomial J ℤ ⧸ coordIdeal ℤ x)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
