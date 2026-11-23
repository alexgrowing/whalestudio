import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraEstimateForRegularity
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebra_estimate_for_regularity : PositivityTheory.RgBcC.AlgEst := by
  first | exact @GlobalTheory.CompanionTheory.SkewWords.algEst | exact GlobalTheory.CompanionTheory.SkewWords.algEst | (intros; apply GlobalTheory.CompanionTheory.SkewWords.algEst <;> assumption)
