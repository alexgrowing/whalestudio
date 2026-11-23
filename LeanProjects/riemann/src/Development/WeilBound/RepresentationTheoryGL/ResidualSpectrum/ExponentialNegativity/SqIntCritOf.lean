import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.ExpNegGlue
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.NormalisedExistence.ExistsNormed
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.AutomorphicLipschitz.NiceAut
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.CommonEigenvectors.KillPoly
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.SquareIntegrableCovers.SetLIntegralLeOfCover
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.ExponentialGluing.ExpNegGlueHolds
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.GapPairings.GapGlue
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.ConjugationDifferences.ExpDivExpEq
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.ConstantTermSteps.CtstepglueHolds
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.L2Gluing.IntegralLeToReal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoundOfNatDegree
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UpdateLeUpdate
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SetLIntegralLeOfBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SingleVecMulUnipMatrix
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CountLeOfDvd

namespace PositivityTheory.Rg.Rs

theorem expNeg_of (h : An.Count) : ExpNeg :=
  expNegGlue_holds dict_holds (l2glue_holds h GlobalTheory.CompanionTheory.SiegelEscape.escape)

theorem sqIntCrit_of (h1 : InitBnd) (h2 : FinTr) (h3 : An.BoxVol) : SqIntCrit :=
  sqIntGlue_holds dict_holds niceAut_holds h1 h2 killPoly_holds
    (GlobalTheory.CompanionTheory.AnBoot.bootGlue diffstep_holds (ctstepglue_holds GlobalTheory.CompanionTheory.LinRec.recBound)) (GlobalTheory.CompanionTheory.SlabGlue.slabGlue h3)

theorem gap_of (h1 : LatOf) (h2 : GapOp) : Gap :=
  gapGlue_holds h1 (gapAbs_of h2 GlobalTheory.CompanionTheory.GapPolyProof.gapPoly)

end PositivityTheory.Rg.Rs
