import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsPos
import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
import CompanionTheory.AutomorphicTheory.UniformLocalFormulas.Closed
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StepChoiceConstantsCOfSiegelWeilAtInfinity
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowPositivityOfSiegelWeilConstants

namespace GlobalTheory

theorem rowNGP_of_siegelWeil :
    HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → Formalism.L2.SG.RowsPos.RowNGP :=
  fun h => GlobalTheory.rowNGP_of_siegelWeil_of_stepChoice h
    (GlobalTheory.St.stepChoiceDataC_of_siegelWeil_inInfinity h (fun _ X u u' hg =>
      Formalism.L2.SG.RealObj.EnergyConvJ.BM.realObj_inInfinityX_jsz CompanionTheory.Lime.BM.uniqGap_holds hg X u u' 1 one_pos))
    Formalism.MainStatements.RowRest.analytic_pinnedTheoremB_uniform

end GlobalTheory
