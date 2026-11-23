import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.NuExtPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.NuExtB

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.DVR

theorem nuExt : NuExtSt :=
  nuExt_of fun _ _ _ _ _ hϖ _ _ hv _ _ _ hE _ hr f hf => secB_dvd_of_vge hϖ hv hE hr f hf

end ReciprocityTheory.ChartRestriction.G.DVR
