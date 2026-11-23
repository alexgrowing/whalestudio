import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ArithmeticRelationsStatementHolds
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.RelationsStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithmetic_relations_statement_holds : GlobalTheory.CompanionTheory.Ar.Num.RelationsStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.TopRel.relations | exact GlobalTheory.CompanionTheory.Ar.Num.TopRel.relations | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.TopRel.relations <;> assumption)
