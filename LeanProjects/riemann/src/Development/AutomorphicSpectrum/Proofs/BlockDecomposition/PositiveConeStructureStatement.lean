import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PositiveConeStructure
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.SymZeroCommFrame

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.positive_cone_structure : PositivityTheory.RgBcC.ConeSt := by
  first | exact @GlobalTheory.CompanionTheory.ConeHaar.coneSt | exact GlobalTheory.CompanionTheory.ConeHaar.coneSt | (intros; apply GlobalTheory.CompanionTheory.ConeHaar.coneSt <;> assumption)
