import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsProjFSMass
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.AMassStB
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

theorem ProjFSMass.proof : ProjFSMass.Statement := by
  intro D Ω _ _ κ _ x e m hfr hFS
  exact ⟨gbPsi e, gb_isGoodProj hfr, gb_ptsIntegralAt hfr hFS⟩

end GroundTheory.Heights₂.Heights.HilbertSamuel
