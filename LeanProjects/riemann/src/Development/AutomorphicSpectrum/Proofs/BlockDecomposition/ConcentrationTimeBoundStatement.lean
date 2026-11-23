import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConcentrationTimeBound
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.concentration_time_bound : PositivityTheory.RgBcC.Fc.ConcT := by
  first | exact @GlobalTheory.CompanionTheory.FcConcT.concT | exact GlobalTheory.CompanionTheory.FcConcT.concT | (intros; apply GlobalTheory.CompanionTheory.FcConcT.concT <;> assumption)
