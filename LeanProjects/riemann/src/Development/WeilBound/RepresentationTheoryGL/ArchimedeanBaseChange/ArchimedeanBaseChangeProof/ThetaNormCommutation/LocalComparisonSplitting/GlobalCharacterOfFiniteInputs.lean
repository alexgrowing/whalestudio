import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CountIsInvInvariant
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormaliserUnconj
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLocallyConstantOfRightInv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableUnits
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousCoordinate
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsScalarOfCentral
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsConjEqSign
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapPFinThetaGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NontrivialFiniteAdeles
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsRegEllIffMemEll
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwConjugateEquivalence
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsEigenbasis
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactOfBounded
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitPreimageEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemRatCentTwConj
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOfRightInvariant
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.PWeylAt
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.PTermOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterOfHolds

namespace PositivityTheory.Rg.BcB.G8

open GlobalTheory.CompanionTheory

theorem translation_existence_holds : TranslEx := LocalThetaTranslation.translEx

theorem lefschetz_pair_holds : LefPair := GlobalTheory.CompanionTheory.LefPair.lefPairOf EllipticTwist.ellDiag weylAt_holds LocalThetaTopology.topo

theorem global_character_of_finite_inputs (hK : KfOC) (hL : FinLevel) (hF : FinHalf) : G4 :=
  have hA : AdelEq := AdelEqProof.adelEqOf TranslAdele.translAd
  global_character_of_holds
    (termOf_holds (QSplitPf.qSplitOf QuotNorm.qIndep) HaarProd.haarSplit LocalThetaTopology.topo CompIsoProof.compIso hK hL hF hA
      TwistCent.centEq NormPoly.polEq (EllProp.ellProperOf EllipticTwist.ellDiag DiagProperProof.diagProper LocalThetaTopology.topo))
    (GlobalTheory.CompanionTheory.OrbInv.orbInvOf (QConjug.qConjOf_holds QuotNorm.qIndep) LocalThetaTopology.topo)
    (GlobalTheory.CompanionTheory.AdelCont.adelContOf hA hL CompIsoProof.compIso LocalThetaTopology.topo) GlobalTheory.CompanionTheory.ClassBij.classBij NormPoly.polEq

end PositivityTheory.Rg.BcB.G8
