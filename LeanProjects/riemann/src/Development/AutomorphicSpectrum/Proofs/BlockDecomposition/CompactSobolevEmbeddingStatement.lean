import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactSobolevEmbedding
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_sobolev_embedding : PositivityTheory.RgBcC.Fc.CptSob := by
  first | exact @GlobalTheory.CompanionTheory.CptSobProof.cptSob | exact GlobalTheory.CompanionTheory.CptSobProof.cptSob | (intros; apply GlobalTheory.CompanionTheory.CptSobProof.cptSob <;> assumption)
