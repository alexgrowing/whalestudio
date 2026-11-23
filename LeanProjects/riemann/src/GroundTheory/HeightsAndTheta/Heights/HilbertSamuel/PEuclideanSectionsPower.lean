import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsEuclideanSectionsPower
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ImportsBisAlt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter MeasureTheory

theorem EuclideanSectionsPower.proof (hL : SectionL2Lattice.Statement) (hP : TensorPowerL2Degree.Statement) :
    EuclideanSectionsPower.Statement := by
  intro K _ ι _ Ω _ _ y D A P0 II hD hII har hb hA hc
  obtain ⟨μ, m, hμ, hcon, hZ, hm, hdeg⟩ := hP K ι Ω y D A P0 II hD hII har hb hA hc
  obtain ⟨r, φ, hinj, hdisc, hlat, hsup, hmul, hrank, hnorm⟩ :=
    hL K ι Ω y D A har hb hA.semipos.1.continuousOn μ hμ hcon hZ
  refine ⟨r, φ, hinj, hdisc, hlat, hsup, hmul, hrank, m, hm, fun ε hε => ?_⟩
  filter_upwards [hdeg ε hε] with q hq
  intro _ _
  exact hq (r (m * q)) (φ (m * q)) (hinj _) (hnorm _)

end GroundTheory.Heights₂.Heights.HilbertSamuel
