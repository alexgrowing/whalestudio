import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardBlocksExponent
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.CosetCount
namespace PositivityTheory.Rg.BcB.F.Tail.PExp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standard_blocks_exponent : PositivityTheory.Rg.BcB.F.Tail.PExp.StdBridge := by
  first | exact @GlobalTheory.CompanionTheory.StandardBlocks.stdBridge | exact GlobalTheory.CompanionTheory.StandardBlocks.stdBridge | (intros; apply GlobalTheory.CompanionTheory.StandardBlocks.stdBridge <;> assumption)
