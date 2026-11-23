import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExponentToSaturation
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.ExpToSat
namespace PositivityTheory.Rg.BcB.F.Tail.PExp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exponent_to_saturation : PositivityTheory.Rg.BcB.F.Tail.PExp.ExpToSat := by
  first | exact @GlobalTheory.CompanionTheory.ExpProd.expToSat | exact GlobalTheory.CompanionTheory.ExpProd.expToSat | (intros; apply GlobalTheory.CompanionTheory.ExpProd.expToSat <;> assumption)
