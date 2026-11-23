import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SobolevOperatorFacts
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sobolev_operator_facts : PositivityTheory.RgBcC.Fc.SobOps := by
  first | exact @GlobalTheory.CompanionTheory.SobOpsPf.sobOps | exact GlobalTheory.CompanionTheory.SobOpsPf.sobOps | (intros; apply GlobalTheory.CompanionTheory.SobOpsPf.sobOps <;> assumption)
