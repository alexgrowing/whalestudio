import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LambdaLowGivesFirstIdentity
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair
open Formalism.BasicNotions Formalism.MainNotions NumberField Formalism.L2.Indef Formalism.L2.Indef.Tree GlobalTheory.BigTop GlobalTheory.BigTop.Fun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lambda_low_gives_first_identity : GlobalTheory.BigTop.LamLow → IPb := by
  first | exact @GlobalTheory.BigTop.Fun.ipb_of_lamLow | exact GlobalTheory.BigTop.Fun.ipb_of_lamLow | (intros; apply GlobalTheory.BigTop.Fun.ipb_of_lamLow <;> assumption)
