import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.FinXHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.PairTiesPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AtPtRel
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.IotaKerHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.FinLevi
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IotaDictAll

namespace Formalism.L2.SG.Pf

theorem fibFinAll_holds : Formalism.L2.SG.TermTieOf.FibFinAll := FinXP.fibFin_holds

theorem pairIndepAll_holds : Formalism.L2.SG.TermTieOf.PairIndepAll :=
  FinXP.pairIndep_of Formalism.L2.SG.Pf.KernelOfEmbedding.IotaKer_holds

theorem iotaRowC_holds : FinXP.IotaRowC := fun _ _ Y _ _ s₁ s₂ hr =>
  Formalism.L2.SG.Pf.iotaDict_fwd Y s₁ s₂ (congrArg (fun q => q.1.1) hr) (congrArg (fun q => q.2.1.1) hr)
    (congrArg (fun q => q.2.2) hr)

theorem pairTiesAll_holds : Formalism.L2.SG.TermTieOf.PairTiesAll := FinXP.pairTies_of iotaRowC_holds

theorem atPtRelevantAll_holds : FinXP.AtPtRelevantAll := FinXP.atPtRelevant_holds

variable [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] in

theorem finXC_of (hWu : Formalism.L2.SG.Pf.WuDecayOfGap) (hRF : Formalism.L2.SG.RowsDef.RowsFinDim) :
    Formalism.L2.SG.PoincareAmplitudeLowerBounds.FinXC :=
  FinXP.finX_holds hWu hRF Formalism.L2.SG.Pf.FinLeviPf.finLeviC_holds Formalism.L2.SG.Pf.KernelOfEmbedding.IotaKer_holds

end Formalism.L2.SG.Pf
