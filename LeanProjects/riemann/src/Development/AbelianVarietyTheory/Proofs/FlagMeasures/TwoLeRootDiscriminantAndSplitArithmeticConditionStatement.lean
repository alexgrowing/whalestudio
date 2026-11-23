import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TwoLeRootDiscriminantAndSplitArithmeticCondition
import Formalism.LocalToGlobal.SiegelLatticeTheory.ResidEvFree
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_le_rootDiscriminant_and_split_arithmetic_conditions : ∀ D : D7, 2 ≤ D.host.rdE ∧ ArithmeticConditionsOfDatum D := by
  first | exact @GlobalTheory.two_le_rdE_and_arithmeticConditionsS0 | exact GlobalTheory.two_le_rdE_and_arithmeticConditionsS0 | (intros; apply GlobalTheory.two_le_rdE_and_arithmeticConditionsS0 <;> assumption)
