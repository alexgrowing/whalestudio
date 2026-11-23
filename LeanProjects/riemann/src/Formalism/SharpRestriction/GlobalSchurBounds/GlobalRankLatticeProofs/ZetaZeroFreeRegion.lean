import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.ZetaZeroFreeRegion
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.LandauZeroFreeHalfPlane

noncomputable section

namespace Formalism.MainNotions.ZetaZeroFreeRegion

theorem G_eq_Gz (y : ℝ) : Formalism.MainNotions.GlobalTheoryTheory.G y = Formalism.Gz y := by
  rw [Formalism.MainNotions.GlobalTheoryTheory.G_eq_Gfun]
  unfold Formalism.BasicNotions.Gfun Formalism.Gz Formalism.Sz
  ring

theorem points_property_of_d7 : PointsLemma := by
  intro θ y0 h0 h1 hG s hs
  exact SlopeTestRemainingChoices.landau_zero_free_half_plane θ h0 h1 y0 (fun y hy => (G_eq_Gz y) ▸ hG y hy) s hs

end Formalism.MainNotions.ZetaZeroFreeRegion

end
