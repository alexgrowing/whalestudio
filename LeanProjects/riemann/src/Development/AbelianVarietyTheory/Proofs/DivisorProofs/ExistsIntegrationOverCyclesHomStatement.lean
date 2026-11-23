import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegrationOverCyclesHom
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodHom
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.FamUnif
open GlobalTheory.AnPer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integrationOverCyclesHom : PHom := by
  first | exact @GlobalTheory.AnPer.pHom | exact GlobalTheory.AnPer.pHom | (intros; apply GlobalTheory.AnPer.pHom <;> assumption)
