import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorEigen
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.CosetCount
namespace PositivityTheory.Rg.BcB.F.Tail.PExp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_eigen : PositivityTheory.Rg.BcB.F.Tail.PExp.TensEig := by
  first | exact @GlobalTheory.CompanionTheory.TensContr.tensEig | exact GlobalTheory.CompanionTheory.TensContr.tensEig | (intros; apply GlobalTheory.CompanionTheory.TensContr.tensEig <;> assumption)
