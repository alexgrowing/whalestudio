import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmPeriodStatementOfHyp

namespace GlobalTheory.Mem.LiteralAutomorphy

def JoinOut : Prop :=
  GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator ∧ GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.Transport ∧ GlobalTheory.ToricTransport.TwistedTransport ∧
    GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals.ZetaDenominators ∧ GlobalTheory.SqTop.Refl

theorem joinOut_iff : JoinOut ↔
    GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator ∧ GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.Transport ∧ GlobalTheory.ToricTransport.TwistedTransport ∧
      GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals.ZetaDenominators ∧ GlobalTheory.SqTop.Refl :=
  Iff.rfl

theorem JoinOut.intro (h₁ : GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator) (h₂ : GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.Transport)
    (h₃ : GlobalTheory.ToricTransport.TwistedTransport) (h₄ : GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals.ZetaDenominators) (h₅ : GlobalTheory.SqTop.Refl) :
    JoinOut :=
  ⟨h₁, h₂, h₃, h₄, h₅⟩

theorem JoinOut.transport (J : JoinOut) : GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.Transport := J.2.1

theorem JoinOut.twisted (J : JoinOut) : GlobalTheory.ToricTransport.TwistedTransport := J.2.2.1

theorem JoinOut.zeta (J : JoinOut) : GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals.ZetaDenominators := J.2.2.2.1

theorem LitCM.joinOut (C : LitCM) : JoinOut :=
  GlobalTheory.JoinFun.denominators_transport_reflection C.hb C.gm C.dr C.dual C.per C.gmp C.st C.cm C.hj C.dri C.pz C.fe

structure LitNE : Prop where

  loc : LitLoc

  aut : LitAut

  coh : LitCoh

  join : JoinOut

  fe : GlobalTheory.Published.HeckeTateFunctionalEquation

theorem LitN.toE (H : LitN) : LitNE :=
  ⟨H.loc, H.aut, H.coh, H.cm.joinOut, H.cm.fe⟩

example (H : LitN) : GlobalTheory.ToricTransport.TwistedTransport := H.toE.join.twisted

example (J : JoinOut) : GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals.ZetaDenominators ∧ GlobalTheory.SqTop.Refl := J.2.2.2

end GlobalTheory.Mem.LiteralAutomorphy

namespace GlobalTheory.Fc.S0

set_option genInjectivity false in
set_option genSizeOfSpec false in

structure HypothesesUE : Prop where
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
  litN : GlobalTheory.Mem.LiteralAutomorphy.LitNE
  toHypothesesX : GlobalTheory.NRows.HypothesesX
  nLink : GlobalTheory.NLink.Hypotheses₂
  depthZeroWild' : GlobalTheory.Published.DepthZeroWild
  depthZeroSupport' : GlobalTheory.Published.DepthZeroSupport
  localFiniteness : ReciprocityTheory.Gal.LocalFiniteness
  localTateDuality : ReciprocityTheory.Gal.LocalTateDuality
  localEulerChar : ReciprocityTheory.Gal.LocalEulerChar

theorem HypothesesU.toE (P : HypothesesU) : HypothesesUE :=
  ⟨P.clozelCohomological, P.greenCuspidal, P.cohomologicalCsdTempered, P.heckeLAdicCharacter, P.chebotarevDegreeOne, P.discreteSpectrumGL, P.galoisRepOfPolarizedCuspidal, P.baseChangeDefiniteUnitary, P.bhattScholzeCrystallineLattices, P.heckeLAdicCharacterAbove, P.cuspRapidDecay, P.weilSiegelFormulaUnitary, P.siegelWeilUnitaryConvergent, P.doublingMethod, P.unramifiedDoublingGL, P.bernsteinZelevinskyFiniteness, P.formalDegreeCompactDual, P.bernsteinUnitaryProductIrreducible, P.geometricLemmaFiltration, P.unlinkedProductIrreducible, P.depthZeroJacquetInjective, P.howeDualityGL, P.jacquetShalika, P.automorphicFormsFiniteGL, P.localGlobalAboveL, P.regularAlgebraicPurity, P.globalArtinReciprocity, P.heckeLAdicParameterAbove, P.deRhamPotSemistable, P.harishChandraFinite, P.greenRegularCharacters, P.zelevinskyPolynomialRing, P.depthZeroInertia, P.rayClassFieldSt, P.rayCharacterArtin, P.genericUnitaryDualGL, P.standardCosocleGL, P.cheb, P.discreteSeriesCover, P.harishChandraModules, P.casselmanWallach, P.weilRepresentationUnitaryPair, P.discreteSeriesExists, P.discreteSeriesClassification, P.strongApproxSU, P.siegelWeilUnitaryConvergent2, P.harishChandraAnalyticity, P.cuspTraceClass, P.dixmierMalliavinFactorisation, P.flathFactorisation, P.pseudoCoefficientUpq, P.harishChandraCharacters, P.langlandsClassification, P.labesseWaldspurger, P.cMCurveGoodOutsidePrimeSt, P.weberRayFieldSt, P.discreteSeriesCoverExists, P.besselUniquenessReal, P.siegelWeilUnitarySchrodinger, P.siegelEisensteinContinuation, P.siegelEisensteinSimplePole, P.schurOrthogonalitySquareIntegrable, P.regularisedSiegelWeilFirstTerm, P.litN.toE, P.toHypothesesX, P.nLink, P.depthZeroWild', P.depthZeroSupport', P.localFiniteness, P.localTateDuality, P.localEulerChar⟩

theorem HypothesesUE.toU (P : HypothesesUE) (C : GlobalTheory.Mem.LiteralAutomorphy.LitCM) : HypothesesU :=
  ⟨P.clozelCohomological, P.greenCuspidal, P.cohomologicalCsdTempered, P.heckeLAdicCharacter, P.chebotarevDegreeOne, P.discreteSpectrumGL, P.galoisRepOfPolarizedCuspidal, P.baseChangeDefiniteUnitary, P.bhattScholzeCrystallineLattices, P.heckeLAdicCharacterAbove, P.cuspRapidDecay, P.weilSiegelFormulaUnitary, P.siegelWeilUnitaryConvergent, P.doublingMethod, P.unramifiedDoublingGL, P.bernsteinZelevinskyFiniteness, P.formalDegreeCompactDual, P.bernsteinUnitaryProductIrreducible, P.geometricLemmaFiltration, P.unlinkedProductIrreducible, P.depthZeroJacquetInjective, P.howeDualityGL, P.jacquetShalika, P.automorphicFormsFiniteGL, P.localGlobalAboveL, P.regularAlgebraicPurity, P.globalArtinReciprocity, P.heckeLAdicParameterAbove, P.deRhamPotSemistable, P.harishChandraFinite, P.greenRegularCharacters, P.zelevinskyPolynomialRing, P.depthZeroInertia, P.rayClassFieldSt, P.rayCharacterArtin, P.genericUnitaryDualGL, P.standardCosocleGL, P.cheb, P.discreteSeriesCover, P.harishChandraModules, P.casselmanWallach, P.weilRepresentationUnitaryPair, P.discreteSeriesExists, P.discreteSeriesClassification, P.strongApproxSU, P.siegelWeilUnitaryConvergent2, P.harishChandraAnalyticity, P.cuspTraceClass, P.dixmierMalliavinFactorisation, P.flathFactorisation, P.pseudoCoefficientUpq, P.harishChandraCharacters, P.langlandsClassification, P.labesseWaldspurger, P.cMCurveGoodOutsidePrimeSt, P.weberRayFieldSt, P.discreteSeriesCoverExists, P.besselUniquenessReal, P.siegelWeilUnitarySchrodinger, P.siegelEisensteinContinuation, P.siegelEisensteinSimplePole, P.schurOrthogonalitySquareIntegrable, P.regularisedSiegelWeilFirstTerm, ⟨P.litN.loc, P.litN.aut, P.litN.coh, C⟩, P.toHypothesesX, P.nLink, P.depthZeroWild', P.depthZeroSupport', P.localFiniteness, P.localTateDuality, P.localEulerChar⟩

theorem HypothesesUE.geometricLemma (P : HypothesesUE) : GlobalTheory.Published.GeometricLemma :=
  GlobalTheory.geometricLemma_of_filtration P.bernsteinZelevinskyFiniteness P.geometricLemmaFiltration

example (P : Hypotheses2) : GlobalTheory.Mem.LiteralAutomorphy.JoinOut := P.toU.toE.litN.join

example (P : HypothesesU) : GlobalTheory.NLink.Hypotheses₂ := P.toE.nLink

end GlobalTheory.Fc.S0
