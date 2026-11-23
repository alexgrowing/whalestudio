import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocQuad1GHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RealObjInInfinityXOfG
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DoubleCosetBesselBoundOfBesselUniq
import Formalism.LocalToGlobal.SiegelLatticeTheory.BesselDiscreteSeries.DecInfPf

noncomputable section

namespace Formalism.L2.SG.RealObj.EnergyConvJ

variable [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] in

theorem threeDimData_inputs_of_besselMapUniq (hJ : PI.BesselMapUniq.BesselMapUniq) : Formalism.FourierDecayAlt.ThreeDimData.Inputs :=
  Formalism.MainNotions.BridgeCS3dClosed.inputs_of Formalism.L2.SG.BesselDiscreteSeries.decInf hJ

variable [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] in

theorem stepIntG_jsz (hJ : PI.BesselMapUniq.BesselMapUniq) : Formalism.L2.SG.RealObj.EnergyInt.StepIntG :=
  Formalism.L2.SG.RealObj.EnergyFinal.stepIntG_holds (threeDimData_inputs_of_besselMapUniq hJ)

variable [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] in

theorem stepConvG_jsz (hJ : PI.BesselMapUniq.BesselMapUniq) : Formalism.L2.S.Pv.ConvG.StepConvG :=
  stepConvG_holds (threeDimData_inputs_of_besselMapUniq hJ)

variable [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] in

theorem realObj_inInfinityX_jsz (hJ : PI.BesselMapUniq.BesselMapUniq) {D : Formalism.BasicNotions.D7}
    (hg : Formalism.L2.SG.ConcreteSettingExists.GapHyp D) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (sc : ℝ)
    (hsc : 0 < sc) : Formalism.L2.SG.RealObj.InInfinityX X u u' sc :=
  Formalism.L2.SG.Pf.realObj_inInfinityX_ofG (stepIntG_jsz hJ) (stepConvG_jsz hJ) hg X u u' sc hsc

end Formalism.L2.SG.RealObj.EnergyConvJ
