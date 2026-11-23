import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatDegreeHolds
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.FlatDegree_holds : GlobalTheory.CompanionTheory.Ar.Fl.FlatDegree := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.flatDegree | exact GlobalTheory.CompanionTheory.Ar.Fl.flatDegree | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.flatDegree <;> assumption)
