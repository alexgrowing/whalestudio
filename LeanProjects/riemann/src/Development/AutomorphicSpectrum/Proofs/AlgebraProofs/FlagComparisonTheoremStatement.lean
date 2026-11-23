import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagComparisonTheorem
import ReciprocityTheory.DualLattices.CotangentSurjective
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.PolarisedFlagStatement
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_comparison_theorem : GlobalTheory.CompanionTheory.Ar.GR.FlagStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.flagStatement_holds | exact GlobalTheory.CompanionTheory.Ar.GR.flagStatement_holds | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.flagStatement_holds <;> assumption)
