import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MahlerBoundOfDegree
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mahler_bound_of_degree : DegBdd → DegRat → MahlerC → Mahler := by
  first | exact @GlobalTheory.CompanionTheory.Cutoff.mahler_of | exact GlobalTheory.CompanionTheory.Cutoff.mahler_of | (intros; apply GlobalTheory.CompanionTheory.Cutoff.mahler_of <;> assumption)
