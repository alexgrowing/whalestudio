import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelAtFittedPoints
import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SizeAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_at_fitted_points : GlobalTheory.BigTop.Fun.Bundle → GlobalTheory.BigTop.Fun.SetAt → GlobalTheory.RowClaim.LinK → GlobalTheory.RowClaim.InjK → GlobalTheory.RowClaim.ConstK → GlobalTheory.RowClaim.Formula2K → GlobalTheory.BigTop.Fun.Ker @GlobalTheory.BigTop.Fun.Comparison₂ := by
  first | exact @GlobalTheory.BigTop.Fun.ker_tie | exact GlobalTheory.BigTop.Fun.ker_tie | (intros; apply GlobalTheory.BigTop.Fun.ker_tie <;> assumption)
