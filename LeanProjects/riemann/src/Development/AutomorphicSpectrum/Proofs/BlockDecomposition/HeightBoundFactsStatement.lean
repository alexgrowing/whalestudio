import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightBoundFacts
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.FrameDer

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_bound_facts : PositivityTheory.RgBcC.LfSt.HbFacts := by
  first | exact @GlobalTheory.CompanionTheory.HbBasis.hbFacts | exact GlobalTheory.CompanionTheory.HbBasis.hbFacts | (intros; apply GlobalTheory.CompanionTheory.HbBasis.hbFacts <;> assumption)
