import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.SphComm2
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.ImportsAlt
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.IsCompactMaximalPairPlace

theorem UpperTheory.Zero.ConvolutionTheory.EB.sphComm2 :
    UpperTheory.Zero.ConvolutionTheory.EB.SphComm2 := by
  intro E _ _ _ a b w f f' hf hf'
  exact PositivityTheory.Rg.BcB.F.sphComm E a b w f f' hf hf'
