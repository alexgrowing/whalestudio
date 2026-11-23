import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.HyperbolicEntryBounds.CasInfOfIm
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.LefschetzHolds
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableHolds
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.EllFormula2J
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterOfFiniteInputs

namespace PositivityTheory.Rg.BcB.F.F0

theorem archimedean_existence_of_compatibility (hC : PositivityTheory.Rg.BcB.CG.CompatEx) (hV : PositivityTheory.Rg.BcB.CG.VCBridge) (hK : PositivityTheory.RgBcC.KerEx) :
    PositivityTheory.Rg.BcB.F.ArchEx :=
  archEx_of (PositivityTheory.Rg.BcB.E1.growthJ_of_ell PositivityTheory.Rg.BcB.CV.ellFormula2J) hC PositivityTheory.RgBcC.lefschetz_holds hV
    PositivityTheory.Rg.BcB.G8.lefschetz_pair_holds hK

end PositivityTheory.Rg.BcB.F.F0
