import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.InLevelSAtOfParts
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.KSpTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.CMInst
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.FrameStd
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.LatAdapted
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.ProdNH
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.GlobFromParts
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.EvalVOpen
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.UnipotentIntegralInLevel
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.PsiVMulVec
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LevelKSplit
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Volumes

noncomputable section

namespace MassDataLevelSSteps

open Formalism.L2.SG.TypedSets Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge

theorem levelSAll_holds : Formalism.L2.SG.Volumes.LevelSAll := level_s_all_split

theorem inLevelSAt_holds :
    ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
      (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
      (L : LocIn (TypX X)) (A : AnIn), InLevelSAt X hb hK FdN FdN' u u' X0 L A :=
  inLevelSAt_of_parts levelSAll_holds kSpCompact_holds kSpOpen_holds cmInst_holds frameStd_holds
    latAdapted_holds prodNH_holds globFromParts_holds haarIdxLoc_holds haarIdxGlob_holds locLevi_holds
    globProd_holds

end MassDataLevelSSteps
