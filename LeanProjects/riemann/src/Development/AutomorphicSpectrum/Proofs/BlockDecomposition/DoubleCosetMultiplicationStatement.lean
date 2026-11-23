import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleCosetMultiplication
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.MatchT
open GlobalTheory.BCT GlobalTheory.UnitaryBC PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.BcB.F.MT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.double_coset_multiplication : DcosMul := by
  first | exact @GlobalTheory.CompanionTheory.DcosProduct.dcosMul | exact GlobalTheory.CompanionTheory.DcosProduct.dcosMul | (intros; apply GlobalTheory.CompanionTheory.DcosProduct.dcosMul <;> assumption)
