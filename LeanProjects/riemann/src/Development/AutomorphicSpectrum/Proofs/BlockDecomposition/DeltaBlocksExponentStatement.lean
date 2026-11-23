import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaBlocksExponent
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.ExpToSat
namespace PositivityTheory.Rg.BcB.F.Tail.PExp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.delta_blocks_exponent : PositivityTheory.Rg.BcB.F.Tail.PExp.DlBridge := by
  first | exact @GlobalTheory.CompanionTheory.DlBridgeAt.dlBridge | exact GlobalTheory.CompanionTheory.DlBridgeAt.dlBridge | (intros; apply GlobalTheory.CompanionTheory.DlBridgeAt.dlBridge <;> assumption)
