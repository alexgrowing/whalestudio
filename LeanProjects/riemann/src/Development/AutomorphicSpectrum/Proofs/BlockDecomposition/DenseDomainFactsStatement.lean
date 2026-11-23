import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DenseDomainFacts
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dense_domain_facts : PositivityTheory.RgBcC.Fc.DenseD := by
  first | exact @GlobalTheory.CompanionTheory.DenseCpt.denseD | exact GlobalTheory.CompanionTheory.DenseCpt.denseD | (intros; apply GlobalTheory.CompanionTheory.DenseCpt.denseD <;> assumption)
