import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetCountTail
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.CosetCount
namespace PositivityTheory.Rg.BcB.F.Tail.PExp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coset_count_tail : PositivityTheory.Rg.BcB.F.Tail.PExp.CosetCount := by
  first | exact @GlobalTheory.CompanionTheory.IwahoriCount.cosetCount | exact GlobalTheory.CompanionTheory.IwahoriCount.cosetCount | (intros; apply GlobalTheory.CompanionTheory.IwahoriCount.cosetCount <;> assumption)
