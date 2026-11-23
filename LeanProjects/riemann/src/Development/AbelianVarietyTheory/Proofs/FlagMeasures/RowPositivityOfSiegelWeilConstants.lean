import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsPos
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SwxsOfSiegelWeil
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StepPinExistsAndFormNGC
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CorankOneNonGenericRowBoundClosedStatement

namespace GlobalTheory

theorem rowNGP_of_siegelWeil_of_stepChoice :
    HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → Formalism.L2.SG.NGAnalytic.StepChoiceConstantsC →
      Formalism.L2.SG.NGAnalytic.StepThmBPinnedC → Formalism.L2.SG.RowsPos.RowNGP := by
  intro h hB hT
  refine GlobalTheory.T.corankOneNonGenericRowBound_closed (GlobalTheory.St.swxs_of_siegelWeil h) hB GlobalTheory.stepPinExists_and_formNGC.1 GlobalTheory.stepPinExists_and_formNGC.2 ?_
  intro Cg cb Cw cT CT C0 _ _ A
  obtain ⟨CB, h0, a, b, H⟩ := hT Cg cb Cw cT CT C0 A
  exact ⟨CB, h0, a, b, fun C' Cl h1 h2 D large₂ X Y u u' _ => H C' Cl h1 h2 D large₂ X Y u u'⟩

end GlobalTheory
