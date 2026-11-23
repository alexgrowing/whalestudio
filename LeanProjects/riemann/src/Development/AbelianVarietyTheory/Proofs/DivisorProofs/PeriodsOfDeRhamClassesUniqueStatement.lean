import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodsOfDeRhamClassesUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodHom
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.FamUnif
open GlobalTheory.AnPer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periods_of_deRham_classes_unique : PUniq := by
  first | exact @GlobalTheory.AnPer.period_unique | exact GlobalTheory.AnPer.period_unique | (intros; apply GlobalTheory.AnPer.period_unique <;> assumption)
