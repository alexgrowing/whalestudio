import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IwahoriTypeSupport.TorusScalar
import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.GlnMixed
import Development.WeilBound.CoreStatements.TotallyDisjointProducts.SLGLProductIrreducibility.TdpFill
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MoyPrasadJacquetIso
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixedNeBotOfIsSubquotient
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ApplyMemTwKerOfNormalizer

namespace UpperTheory.Gal.TypesAndIwahori

theorem loc_holds : Loc := by
  have geo := UpperTheory.Lit.Mix.geometricLemma
  have bz := GlobalTheory.bernsteinZelevinskyFiniteness_holds
  have zel := UpperTheory.Lit.Mix.polynomialRing
  have seg := PositivityTheory.RgGu.segmentRepresentation
  exact
    { bz := bz
      geo := geo
      zel := zel
      disj := PositivityTheory.SlGl.totallyDisjointProductIrreducible_of_parts geo seg
        (PositivityTheory.Groth.grothendieckRingPolynomial_of_seg seg)
      mp := GlobalTheory.CompanionTheory.MoyPrasadTop.moyPrasadJacquetIso
      dzi := GlobalTheory.DepthZeroPass.depthZeroInduction geo bz zel
      dzj := GlobalTheory.DepthZeroJac.depthZeroJacquetInjective }

end UpperTheory.Gal.TypesAndIwahori
