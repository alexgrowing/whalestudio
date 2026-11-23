import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowSplitFiniteArchimedeanPartsOfSteps
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGVanish
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.StepAnalyticConstantsP
open Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic GlobalTheory.NGRow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowSplitFiniteArchimedeanParts_of_steps : StepAnalyticConstantsP → StepSizes → StepClass → StepNormals → StepPoints → StepHeight → NGCut2P := by
  first | exact @GlobalTheory.NGRow.ngCut2P_of_steps | exact GlobalTheory.NGRow.ngCut2P_of_steps | (intros; apply GlobalTheory.NGRow.ngCut2P_of_steps <;> assumption)
