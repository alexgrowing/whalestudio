import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.LocalActionPowers.Psmall
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.LocalActionPowers.Pfmone
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.LocalActionPowers.FmTermZero
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.LocalActionPowers.Pfmpow
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.BlkGrowth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelIndexNeZeroOfOpen
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairMaximalCompactOpenCompact

namespace PositivityTheory.Rg.BcB.F.FA

theorem position_action_algebra : ActAlg := GlobalTheory.CompanionTheory.FactorAction.actAlg

theorem finAct_of (h1 : IntHint) (h2 : Slots) (h3 : FinConv) : FinAct := GlobalTheory.CompanionTheory.FinActS.finActOf h1 h2 h3 position_action_algebra

theorem fmOne_of (h1 : IntHint) (h2 : Slots) (h3 : FinConv) : Tail.FmOne :=
  fmOneOf_holds (fmOff_holds h3 (finAct_of h1 h2 h3)) actIdem_holds

theorem fmPow_of (h1 : IntHint) (h2 : Slots) (h3 : FinConv) (h4 : FmAlg) : Tail.FmPow :=
  fmPowOf_holds h4 (fmAtP_holds h3 (finAct_of h1 h2 h3)) convMul_holds position_action_algebra actIdem_holds

end PositivityTheory.Rg.BcB.F.FA
