import Formalism.LocalToGlobal.SiegelLatticeTheory.WeightedGaugeFactors.FactsDS
import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.LocalUniquenessReduction
import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.LocScalar

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.Closed.BM

theorem wuDecayOfGap_of_uniqGap (h : CompanionTheory.Lime.BM.UniqGap) : WuDecayOfGap :=
  WuDec.BM.wuDecay_gap h BesselNVGap_holds CoefWeightedLoc_holds WlocExists_holds QuotProdK_holds NUnimodLoc_holds
    WuDec.LS.local_scalar_reduction

end Formalism.L2.SG.Pf
