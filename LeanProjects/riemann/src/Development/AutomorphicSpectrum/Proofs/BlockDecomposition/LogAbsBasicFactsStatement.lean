import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LogAbsBasicFacts
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_abs_basic_facts : LogAbsBasic := by
  first | exact @GlobalTheory.CompanionTheory.LogAbs.logAbsBasic | exact GlobalTheory.CompanionTheory.LogAbs.logAbsBasic | (intros; apply GlobalTheory.CompanionTheory.LogAbs.logAbsBasic <;> assumption)
