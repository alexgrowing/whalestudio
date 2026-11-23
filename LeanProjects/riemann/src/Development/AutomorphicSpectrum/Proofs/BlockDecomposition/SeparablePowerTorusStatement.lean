import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SeparablePowerTorus
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.SplitPlaceGeneratorPowers
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.separable_power_torus : PositivityTheory.Rg.BcB.F.MLM.SepPowT := by
  first | exact @GlobalTheory.CompanionTheory.SepPow.sepPowT | exact GlobalTheory.CompanionTheory.SepPow.sepPowT | (intros; apply GlobalTheory.CompanionTheory.SepPow.sepPowT <;> assumption)
