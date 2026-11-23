import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MacdonaldInverseOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.SplitPlaceGeneratorPowers
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.macdonald_inverse_of : PositivityTheory.Rg.BcB.F.MLM.MacInvOf := by
  first | exact @GlobalTheory.CompanionTheory.MacInvPf.macInvOf | exact GlobalTheory.CompanionTheory.MacInvPf.macInvOf | (intros; apply GlobalTheory.CompanionTheory.MacInvPf.macInvOf <;> assumption)
