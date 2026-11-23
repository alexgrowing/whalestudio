import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.DescWeakOfGalWeak
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.OrbitalCosetFiniteness.StUnit
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.MuEx
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.StableBlockG
import Development.AutomorphicArithmetic.Foundations.Convolution.WeightRankUnits.USide
import Development.AutomorphicArithmetic.Foundations.Convolution.WeightRankUnits.NeZeroOfFinprod
import Development.AutomorphicArithmetic.Foundations.Convolution.WeightRankUnits.MatchUnit
import Development.AutomorphicArithmetic.Foundations.Convolution.WeightRankUnits.MatchSplit

open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.Zero.ConvolutionTheory.EB

namespace UpperTheory.V.Z.Tf.GaloisFromTraceFormula

theorem runTh_of_pi (h1 : PiTerm) (h2 : PiFin) (h3 : PiAdm) (h4 : TwTrSum) (h5 : PositivityTheory.Rg.BcB.Desc.GrowthPiJ) : RunTh :=
  runTh_of UpperTheory.ConvolutionTheory.G2.uSide UpperTheory.ConvolutionTheory.G2.g2s muEx UpperTheory.ConvolutionTheory.G2.matchUnit UpperTheory.ConvolutionTheory.G2.matchSplit Th.stUnit
    (endoBlockG cuspReadI) (stableBlockG cuspReadI h1 h2 h3 h4 h5)

theorem descWeak_of_pi (hW : GalWeak 4) (h1 : PiTerm) (h2 : PiFin) (h3 : PiAdm) (h4 : TwTrSum)
    (h5 : PositivityTheory.Rg.BcB.Desc.GrowthPiJ) : UpperTheory.V.Z.Desc.DescWeak :=
  descWeak_of_galWeak hW (runTh_of_pi h1 h2 h3 h4 h5)

end UpperTheory.V.Z.Tf.GaloisFromTraceFormula
