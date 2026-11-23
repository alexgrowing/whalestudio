import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GeometricLemmaOfFiltration

namespace GlobalTheory.Fc.S0

set_option genInjectivity false in
set_option genSizeOfSpec false in

structure HypothesesU : Prop where
  clozelCohomological : GlobalTheory.Published.ClozelCohomological
  greenCuspidal : GlobalTheory.Published.GreenCuspidal
  cohomologicalCsdTempered : GlobalTheory.Published.CohomologicalCsdTempered
  heckeLAdicCharacter : GlobalTheory.Published.HeckeLAdicCharacter
  chebotarevDegreeOne : GlobalTheory.Published.ChebotarevDegreeOne
  discreteSpectrumGL : GlobalTheory.Published.DiscreteSpectrumGL
  galoisRepOfPolarizedCuspidal : GlobalTheory.Published.GaloisRepOfPolarizedCuspidal
  baseChangeDefiniteUnitary : GlobalTheory.Published.BaseChangeDefiniteUnitary
  bhattScholzeCrystallineLattices : GlobalTheory.Published.BhattScholzeCrystallineLattices
  heckeLAdicCharacterAbove : GlobalTheory.Published.HeckeLAdicCharacterAbove
  cuspRapidDecay : GlobalTheory.Published.CuspRapidDecay
  weilSiegelFormulaUnitary : GlobalTheory.Published.WeilSiegelFormulaUnitary
  siegelWeilUnitaryConvergent : GlobalTheory.Published.SiegelWeilUnitaryConvergent
  doublingMethod : GlobalTheory.Published.DoublingMethod
  unramifiedDoublingGL : GlobalTheory.Published.UnramifiedDoublingGL
  bernsteinZelevinskyFiniteness : GlobalTheory.Published.BernsteinZelevinskyFiniteness
  formalDegreeCompactDual : GlobalTheory.Published.FormalDegreeCompactDual
  bernsteinUnitaryProductIrreducible : GlobalTheory.Published.BernsteinUnitaryProductIrreducible
  geometricLemmaFiltration : GlobalTheory.Published.GeometricLemmaFiltration
  unlinkedProductIrreducible : GlobalTheory.Published.UnlinkedProductIrreducible
  depthZeroJacquetInjective : GlobalTheory.Published.DepthZeroJacquetInjective
  howeDualityGL : GlobalTheory.Published.HoweDualityGL
  jacquetShalika : GlobalTheory.Published.JacquetShalika
  automorphicFormsFiniteGL : GlobalTheory.Published.AutomorphicFormsFiniteGL
  localGlobalAboveL : GlobalTheory.Published.LocalGlobalAboveL
  regularAlgebraicPurity : GlobalTheory.Published.RegularAlgebraicPurity
  globalArtinReciprocity : GlobalTheory.Published.GlobalArtinReciprocity
  heckeLAdicParameterAbove : GlobalTheory.Published.HeckeLAdicParameterAbove
  deRhamPotSemistable : GlobalTheory.Published.DeRhamPotSemistable
  harishChandraFinite : GlobalTheory.Published.HarishChandraFinite
  greenRegularCharacters : GlobalTheory.Published.GreenRegularCharacters
  zelevinskyPolynomialRing : GlobalTheory.Published.ZelevinskyPolynomialRing
  depthZeroInertia : GlobalTheory.Published.DepthZeroInertia
  rayClassFieldSt : GlobalTheory.Published.RayClassFieldSt
  rayCharacterArtin : GlobalTheory.Published.RayCharacterArtin
  genericUnitaryDualGL : GlobalTheory.Published.GenericUnitaryDualGL
  standardCosocleGL : GlobalTheory.Published.StandardCosocleGL
  cheb : GlobalTheory.TwSys.Cheb
  discreteSeriesCover : GlobalTheory.Published.DiscreteSeriesCover
  harishChandraModules : GlobalTheory.Published.HarishChandraModules
  casselmanWallach : GlobalTheory.Published.CasselmanWallach
  weilRepresentationUnitaryPair : GlobalTheory.Published.WeilRepresentationUnitaryPair
  discreteSeriesExists : GlobalTheory.Published.DiscreteSeriesExists
  discreteSeriesClassification : GlobalTheory.Published.DiscreteSeriesClassification
  strongApproxSU : GlobalTheory.Published.StrongApproxSU
  siegelWeilUnitaryConvergent2 : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent
  harishChandraAnalyticity : GlobalTheory.Published.HarishChandraAnalyticity
  cuspTraceClass : GlobalTheory.Published.CuspTraceClass
  dixmierMalliavinFactorisation : GlobalTheory.Published.DixmierMalliavinFactorisation
  flathFactorisation : GlobalTheory.Published.FlathFactorisation
  pseudoCoefficientUpq : GlobalTheory.Published.PseudoCoefficientUpq
  harishChandraCharacters : GlobalTheory.Published.HarishChandraCharacters
  langlandsClassification : GlobalTheory.Published.LanglandsClassification
  labesseWaldspurger : GlobalTheory.Published.LabesseWaldspurger
  cMCurveGoodOutsidePrimeSt : GlobalTheory.Published.CMCurveGoodOutsidePrimeSt
  weberRayFieldSt : GlobalTheory.Published.WeberRayFieldSt
  discreteSeriesCoverExists : GlobalTheory.Published.DiscreteSeriesCoverExists
  besselUniquenessReal : GlobalTheory.Published.BesselUniquenessReal
  siegelWeilUnitarySchrodinger : GlobalTheory.Published.SiegelWeilUnitarySchrodinger
  siegelEisensteinContinuation : GlobalTheory.Published.SiegelEisensteinContinuation
  siegelEisensteinSimplePole : GlobalTheory.Published.SiegelEisensteinSimplePole
  schurOrthogonalitySquareIntegrable : GlobalTheory.Published.SchurOrthogonalitySquareIntegrable
  regularisedSiegelWeilFirstTerm : GlobalTheory.Published.RegularisedSiegelWeilFirstTerm
  litN : GlobalTheory.Mem.LiteralAutomorphy.LitN
  toHypothesesX : GlobalTheory.NRows.HypothesesX
  nLink : GlobalTheory.NLink.Hypotheses₂
  depthZeroWild' : GlobalTheory.Published.DepthZeroWild
  depthZeroSupport' : GlobalTheory.Published.DepthZeroSupport
  localFiniteness : ReciprocityTheory.Gal.LocalFiniteness
  localTateDuality : ReciprocityTheory.Gal.LocalTateDuality
  localEulerChar : ReciprocityTheory.Gal.LocalEulerChar

theorem Hypotheses2.toU (P : Hypotheses2) : HypothesesU :=
  ⟨P.clozelCohomological, P.greenCuspidal, P.cohomologicalCsdTempered, P.heckeLAdicCharacter, P.chebotarevDegreeOne, P.discreteSpectrumGL, P.galoisRepOfPolarizedCuspidal, P.baseChangeDefiniteUnitary, P.bhattScholzeCrystallineLattices, P.heckeLAdicCharacterAbove, P.cuspRapidDecay, P.weilSiegelFormulaUnitary, P.siegelWeilUnitaryConvergent, P.doublingMethod, P.unramifiedDoublingGL, P.bernsteinZelevinskyFiniteness, P.formalDegreeCompactDual, P.bernsteinUnitaryProductIrreducible, P.geometricLemmaFiltration, P.unlinkedProductIrreducible, P.depthZeroJacquetInjective, P.howeDualityGL, P.jacquetShalika, P.automorphicFormsFiniteGL, P.localGlobalAboveL, P.regularAlgebraicPurity, P.globalArtinReciprocity, P.heckeLAdicParameterAbove, P.deRhamPotSemistable, P.harishChandraFinite, P.greenRegularCharacters, P.zelevinskyPolynomialRing, P.depthZeroInertia, P.rayClassFieldSt, P.rayCharacterArtin, P.genericUnitaryDualGL, P.standardCosocleGL, P.cheb, P.discreteSeriesCover, P.harishChandraModules, P.casselmanWallach, P.weilRepresentationUnitaryPair, P.discreteSeriesExists, P.discreteSeriesClassification, P.strongApproxSU, P.siegelWeilUnitaryConvergent2, P.harishChandraAnalyticity, P.cuspTraceClass, P.dixmierMalliavinFactorisation, P.flathFactorisation, P.pseudoCoefficientUpq, P.harishChandraCharacters, P.langlandsClassification, P.labesseWaldspurger, P.cMCurveGoodOutsidePrimeSt, P.weberRayFieldSt, P.discreteSeriesCoverExists, P.besselUniquenessReal, P.siegelWeilUnitarySchrodinger, P.siegelEisensteinContinuation, P.siegelEisensteinSimplePole, P.schurOrthogonalitySquareIntegrable, P.regularisedSiegelWeilFirstTerm, P.litN, P.toHypothesesX, P.nLink, P.depthZeroWild', P.depthZeroSupport', P.localFiniteness, P.localTateDuality, P.localEulerChar⟩

theorem HypothesesU.geometricLemma (P : HypothesesU) : GlobalTheory.Published.GeometricLemma :=
  GlobalTheory.geometricLemma_of_filtration P.bernsteinZelevinskyFiniteness P.geometricLemmaFiltration

example (P : Hypotheses2) : GlobalTheory.Published.GeometricLemmaFiltration := P.toU.geometricLemmaFiltration

example (P : Hypotheses2) : GlobalTheory.Published.SiegelWeilUnitarySchrodinger := P.toU.siegelWeilUnitarySchrodinger

example (P : Hypotheses2) : GlobalTheory.NLink.Hypotheses₂ := P.toU.nLink

example (P : Hypotheses2) : GlobalTheory.Published.GeometricLemma := P.toU.geometricLemma

end GlobalTheory.Fc.S0
