import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.PfQMap
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.LintegralIndicatorNeTop
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.EnormOfRealToRealLe
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.PQProd
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.QuotIntegralMulRight
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.PLocTor
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.POneVanish
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.PTwoVanish
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.CVEmbInfSelf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.PFamAt
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.PAdTop
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.PCutInt
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.ExistsMeasure
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.IsClosedEmbeddingSlice
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.PClassVanish

namespace PositivityTheory.Rg.BcB.CV

theorem classVanish_of_steps (hNormEq : PositivityTheory.Rg.BcB.D4.NormEq) (hQuotProd : PositivityTheory.Rg.BcB.D4.QuotProd) (hChainSum : PositivityTheory.Rg.BcB.ChainSum) (hRatDisc : PositivityTheory.Rg.BcB.D4.RatDisc) (hLocVanish : PositivityTheory.Rg.BcB.LocVanish) (hLocProper : PositivityTheory.Rg.BcB.D4.LocProper) (hLocFlag : PositivityTheory.Rg.BcB.D4.LocFlag) (hDegBdd : PositivityTheory.Rg.BcB.DegBdd) (hKerFin : PositivityTheory.Rg.BcB.D4.KerFin) (hMahler : PositivityTheory.Rg.BcB.Mahler) (hSplitAt : PositivityTheory.Rg.BcB.D4.SplitAt) (hNonEllFlag : PositivityTheory.Rg.BcB.D4.NonEllFlag) (hSplitAt2 : PositivityTheory.Rg.BcB.D4.SplitAt2) (hPairParam : PositivityTheory.Rg.BcB.D4.PairParam) (hTorusChar : PositivityTheory.Rg.BcB.D4.TorusChar) (hChiGam : PositivityTheory.Rg.BcB.D4.ChiGam) (hQuotStage : PositivityTheory.Rg.BcB.D4.QuotStage) (hSizeBasic : PositivityTheory.Rg.BcB.SizeBasic) :
    PositivityTheory.Rg.BcB.ClassVanish :=
  have hQMap : QMap := pf_QMap hNormEq
  have hQInt : QInt := pf_QInt
  have hQAdd : QAdd := pf_QAdd
  have hQProd : QProd := pf_QProd hQuotProd hQMap
  have hVfun : Vfun := pf_Vfun hChainSum hRatDisc hNormEq hQInt hQAdd
  have hLocTor : LocTor := pf_LocTor
  have hOneVanish : OneVanish := pf_OneVanish hLocVanish hLocProper hLocTor hQInt hQAdd
  have hTwoVanish : TwoVanish := pf_TwoVanish hLocVanish hLocProper hLocTor hQInt hQAdd hQProd hOneVanish
  have hPloc : Ploc := pf_Ploc
  have hFamAt : FamAt := pf_FamAt hLocFlag hPloc
  have hAdTop : AdTop := pf_AdTop hDegBdd hRatDisc
  have hCutInt : CutInt := pf_CutInt hKerFin hMahler hQInt hAdTop
  have hGlob1 : Glob1 := pf_Glob1 hSplitAt hNonEllFlag hLocVanish hLocTor hQMap hQProd hPloc hAdTop
  have hGlob2 : Glob2 := pf_Glob2 hSplitAt2 hLocTor hQMap hQProd hTwoVanish hPloc hFamAt hAdTop
  pf_ClassVanish hPairParam hTorusChar hChiGam hQuotStage hRatDisc hSizeBasic hQAdd hVfun hAdTop hCutInt hGlob1 hGlob2

end PositivityTheory.Rg.BcB.CV
