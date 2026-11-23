import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAndAwayFormula
import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SizeAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
open GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SumSize
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_and_away_formula : SetAt → FinK → AwayK → FP @Comparison₂ := by
  first | exact @GlobalTheory.Adopt.finite_and_away_formula | exact GlobalTheory.Adopt.finite_and_away_formula | (intros; apply GlobalTheory.Adopt.finite_and_away_formula <;> assumption)
