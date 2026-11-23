import Formalism.LocalToGlobal.SiegelLatticeTheory.WeightedGaugeFactors.FactsDS
import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.LocQuad1GHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyJSZ

noncomputable section

namespace Formalism.L2.SG.RealObj.EnergyConvJ

namespace BM

theorem stepIntG_jsz (hJ : CompanionTheory.Lime.BM.UniqGap) : Formalism.L2.SG.RealObj.EnergyInt.StepIntG :=
  Formalism.L2.SG.RealObj.EnergyFinal.BM.stepIntG_holds (CompanionTheory.Lime.BM.inputs2_of hJ)

theorem stepConvG_jsz (hJ : CompanionTheory.Lime.BM.UniqGap) : Formalism.L2.S.Pv.ConvG.StepConvG :=
  Formalism.L2.SG.RealObj.EnergyConvJ.BM.stepConvG_holds (CompanionTheory.Lime.BM.inputs2_of hJ)

theorem realObj_inInfinityX_jsz (hJ : CompanionTheory.Lime.BM.UniqGap) {D : Formalism.BasicNotions.D7}
    (hg : Formalism.L2.SG.ConcreteSettingExists.GapHyp D) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (sc : ℝ)
    (hsc : 0 < sc) : Formalism.L2.SG.RealObj.InInfinityX X u u' sc :=
  Formalism.L2.SG.Pf.realObj_inInfinityX_ofG (Formalism.L2.SG.RealObj.EnergyConvJ.BM.stepIntG_jsz hJ) (Formalism.L2.SG.RealObj.EnergyConvJ.BM.stepConvG_jsz hJ) hg X u u' sc hsc

end BM

end Formalism.L2.SG.RealObj.EnergyConvJ
