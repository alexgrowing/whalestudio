import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsOmNVbInt
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsTpCuspIntegrable
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StNbarSmooth
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.RegWeightLevi
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

theorem OmNVbInt.proof (hT : TpCuspIntegrable.Statement) (hS : NbarSmooth.Statement) : OmNVbInt.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X B p q _ _
  filter_upwards [X.S.eventually_chartLevi X.S_tied] with t ht
  exact hT II Ψ K ι Ω E D O Lt X B p q t (hS II Ψ K ι Ω E D O Lt X B p q t ht.1)

end GroundTheory.Heights₂.Heights.LowerBoundFree
