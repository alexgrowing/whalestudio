import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteConstantHolds
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FinConstFor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_constant_holds : GlobalTheory.CompanionTheory.Ar.Flat.FinConst := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.finConst_of_all_hosts | exact GlobalTheory.CompanionTheory.Ar.Flat.finConst_of_all_hosts | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.finConst_of_all_hosts <;> assumption)
