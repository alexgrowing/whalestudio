import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SizeAtHolds
import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SizeAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.size_at_holds : GlobalTheory.BigTop.Fun.SizeAt := by
  first | exact @GlobalTheory.BigTop.Fun.SizeProof.sizeAt | exact GlobalTheory.BigTop.Fun.SizeProof.sizeAt | (intros; apply GlobalTheory.BigTop.Fun.SizeProof.sizeAt <;> assumption)
