import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsNefGeneric
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsFibreHilbertFlat
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsFibreCycleDegree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

universe u w

theorem ConservationOfDegree.proof (hA : FibreHilbertFlat.Statement.{u, w})
    (hB : FibreCycleDegree.Statement.{u, w}) : ConservationOfDegree.Statement.{u, w} := by
  intro S _ _ F _ _ _ Ω _ _ _ _ N x M 𝔪 h𝔪 qq hq hconst hsub
  have h1 := hA S F Ω N x M 𝔪 h𝔪 qq hq hconst hsub
  have h2 := hB S F Ω N x M 𝔪 h𝔪 qq hq hconst hsub
  rw [interNum]
  refine Tendsto.limUnder_eq (tendsto_const_nhds.congr' ?_)
  filter_upwards [h1, h2] with c e1 e2
  rw [e1, e2]

end GroundTheory.Heights₂.Heights.Kleiman
