import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EqualWordsNonGenericEstimatesChain
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.StepLocGenPinnedGP
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqWire
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGVanish
open Formalism.FourierDecayAlt Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.equalWords_nonGeneric_estimates_chain : PN.NGChain ∧ StepClassG ∧ StepPointsG ∧ StepNormOneG ∧ TieOfCtx ∧ StepPinExists ∧ StepTermVanishG ∧ Formalism.L2.SG.NGVanish.FormNGC ∧ (Formalism.L2.SG.Pf.MainEqFam.StepFamG → StepLocGenPinnedG) := by
  first | exact @GlobalTheory.closed_steps_equal_words | exact GlobalTheory.closed_steps_equal_words | (intros; apply GlobalTheory.closed_steps_equal_words <;> assumption)
