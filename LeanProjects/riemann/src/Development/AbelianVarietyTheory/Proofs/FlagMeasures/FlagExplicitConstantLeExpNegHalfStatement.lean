import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagExplicitConstantLeExpNegHalf
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_explicit_constant_le_exp_neg_half : ConstantBound := by
  first | exact @GlobalTheory.FlagMeas.constantBound | exact GlobalTheory.FlagMeas.constantBound | (intros; apply GlobalTheory.FlagMeas.constantBound <;> assumption)
