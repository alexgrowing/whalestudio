import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveKernelUniqueness
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wave_kernel_uniqueness : PositivityTheory.RgBcC.KerUniq := by
  first | exact @GlobalTheory.CompanionTheory.KerUniq.main | exact GlobalTheory.CompanionTheory.KerUniq.main | (intros; apply GlobalTheory.CompanionTheory.KerUniq.main <;> assumption)
