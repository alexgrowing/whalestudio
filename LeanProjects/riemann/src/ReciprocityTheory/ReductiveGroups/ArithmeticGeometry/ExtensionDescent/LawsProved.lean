import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.WeightIndep
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.UnramExt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull

namespace ReciprocityTheory.ChartRestriction.G.Out

open Semi

theorem proved_WeightIndepSt : WeightIndepSt := ReciprocityTheory.ChartRestriction.G.Out.WeightPf.weightIndep
theorem proved_UnramExtSt : UnramExtSt := ReciprocityTheory.ChartRestriction.G.Semi.Unr.unramExt
theorem proved_CubePullSt : CubePullSt := ReciprocityTheory.ChartRestriction.G.Out.CubePf.cubePull

end ReciprocityTheory.ChartRestriction.G.Out
