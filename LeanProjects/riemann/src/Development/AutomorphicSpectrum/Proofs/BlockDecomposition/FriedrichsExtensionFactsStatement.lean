import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FriedrichsExtensionFacts
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.friedrichs_extension_facts : PositivityTheory.RgBcC.Fc.Friedrichs := by
  first | exact @GlobalTheory.CompanionTheory.FriedrichsFc.friedrichs | exact GlobalTheory.CompanionTheory.FriedrichsFc.friedrichs | (intros; apply GlobalTheory.CompanionTheory.FriedrichsFc.friedrichs <;> assumption)
