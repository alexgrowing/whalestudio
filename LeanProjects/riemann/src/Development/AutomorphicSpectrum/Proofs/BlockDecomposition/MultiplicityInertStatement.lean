import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicityInert
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.SplitPlaceGeneratorPowers
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicity_inert : PositivityTheory.Rg.BcB.F.MLM.MuInert := by
  first | exact @GlobalTheory.CompanionTheory.MuInertPlace.muInert | exact GlobalTheory.CompanionTheory.MuInertPlace.muInert | (intros; apply GlobalTheory.CompanionTheory.MuInertPlace.muInert <;> assumption)
