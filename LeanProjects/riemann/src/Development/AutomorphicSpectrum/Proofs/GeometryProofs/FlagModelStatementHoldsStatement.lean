import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagModelStatementHolds
import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlagModelStatement
open GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.FlagModelStatement_holds : FlagModelStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagModel.flagModel | exact GlobalTheory.CompanionTheory.Ar.FlagModel.flagModel | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagModel.flagModel <;> assumption)
