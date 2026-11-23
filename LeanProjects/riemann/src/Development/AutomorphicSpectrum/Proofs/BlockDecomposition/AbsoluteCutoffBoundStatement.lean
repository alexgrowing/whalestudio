import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsoluteCutoffBound
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absolute_cutoff_bound : PositivityTheory.RgBcC.Fc.AbsCut := by
  first | exact @GlobalTheory.CompanionTheory.FcCut.absCut | exact GlobalTheory.CompanionTheory.FcCut.absCut | (intros; apply GlobalTheory.CompanionTheory.FcCut.absCut <;> assumption)
