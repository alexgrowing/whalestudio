import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.CutTailC
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.KerSplitLIntSub
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.DomOneMeasure

noncomputable section

open PositivityTheory.Rg.BcB.Desc

namespace DiscreteGroups.T1.G

theorem rGrowthPiJ_of (hU : PiVecEx → PiInv → UncutHalf) (hT : PiVecEx → PiInv → CutTail2) : RGrowthPiJ :=
  fun hE hS hV hI => growth_of_ellipticFormula hE hS domOne kerSplit (hU hV hI) (hT hV hI)

end DiscreteGroups.T1.G

end
