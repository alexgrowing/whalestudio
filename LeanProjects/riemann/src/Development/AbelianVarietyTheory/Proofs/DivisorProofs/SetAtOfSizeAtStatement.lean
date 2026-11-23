import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetAtOfSizeAt
import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SizeAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.set_at_of_size_at : GlobalTheory.BigTop.Fun.SizeAt → GlobalTheory.BigTop.Fun.SetAt := by
  first | exact @GlobalTheory.BigTop.Fun.setAt_of_sizeAt | exact GlobalTheory.BigTop.Fun.setAt_of_sizeAt | (intros; apply GlobalTheory.BigTop.Fun.setAt_of_sizeAt <;> assumption)
