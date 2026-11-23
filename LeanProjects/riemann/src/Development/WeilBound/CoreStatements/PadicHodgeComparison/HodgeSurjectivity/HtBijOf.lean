import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.HtBijOfParts
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapHEmptyBij
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SglMem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CocycleZeroAlt
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.SiteLaws
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.Faithful
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.ZarAbs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OntoFormLaws
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DWedgeExists
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormConsEqSmul
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PiCongrRightSingle
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.FormCup
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.EtaleChartBaseChange.DivisorCoverOfChartLaws
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.EtaleChartBaseChange.ChartLaws
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NullClassVanishing.CupLaws
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.ZarRelOf
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.AffRelOf
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.RelLiftOf
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.EtaleChartBaseChange.RelInjOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemBOfSub
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NullClassVanishing.ClsZeroOfNull
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CupSurjectivity.OntoLow
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CupSurjectivity.Retract
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineFormsOfFormUniqueness
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedLogCocycleD
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelNullCast
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EtaleMapRight
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.OmNatB
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.IsoBij
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartIsLocalizationAway
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CupSurjectivity.OntoOf3Pf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SlantOf
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.TopRes
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CupSurjectivity.HodgeTateDimensionEquality
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.FormUniq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.LiftsNonempty
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsTheta
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechDApply
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneResOfOneLow

namespace CrystallineSemistableComparison.Onto

theorem parts  : Parts where
  mv := GlobalTheory.CompanionTheory.Onto.mvBij
  surj := GlobalTheory.CompanionTheory.OneSurjC.oneSurj
  cov := GlobalTheory.CompanionTheory.CovDescent.covDesc
  site := siteLaws_pf
  on := onIso_pf
  zar := zarAbs_pf
  laws := GlobalTheory.CompanionTheory.OntoForms.formLaws
  dw := GlobalTheory.CompanionTheory.Forms.dWedge_exists
  dl := GlobalTheory.CompanionTheory.OntoDLog.dLog
  kun := GlobalTheory.CompanionTheory.OmKun.omKun
  fc := formCup_pf
  div := divisor_cover_of_chart_laws chartLaws_pf
  chart := chartLaws_pf
  cup := cupLaws_pf
  zarRel := zarRelOf_pf
  affRel := affRelOf_pf
  lift := relLiftOf_pf
  inj := relInjOf_pf topRes_pf
  cone := GlobalTheory.CompanionTheory.ConeKillC.coneKillOf
  killOf := killOf3_pf
  low := ontoLow_pf
  retr := retract_pf
  aff := GlobalTheory.CompanionTheory.AffOmP.affOm formUniq_pf
  c1 := GlobalTheory.CompanionTheory.OntoFirstChernCocycle.main
  kill := GlobalTheory.CompanionTheory.RelKill.relKillOf topRes_pf formUniq_pf omRes_pf
  kunAff := GlobalTheory.CompanionTheory.KunAffP.kunAffOf formUniq_pf
  nat := omNatB_pf
  iso := isoBij_pf
  bij := GlobalTheory.CompanionTheory.ChartBijOf.chartBij_of GlobalTheory.CompanionTheory.SurjectionOntoH4.h4a siteLaws_pf GlobalTheory.CompanionTheory.CechOne.oneLow
    (GlobalTheory.CompanionTheory.OneResProof.oneRes_of_oneLow GlobalTheory.CompanionTheory.CechOne.oneLow) GlobalTheory.CompanionTheory.CovDescent.covDesc (zarRelOf_pf siteLaws_pf onIso_pf zarAbs_pf) (GlobalTheory.CompanionTheory.AffOmP.affOm formUniq_pf)
    omNatB_pf omRes_pf (affRelOf_pf siteLaws_pf onIso_pf (GlobalTheory.CompanionTheory.AffOmP.affOm formUniq_pf) omNatB_pf GlobalTheory.CompanionTheory.OntoForms.formLaws)
    GlobalTheory.CompanionTheory.OntoForms.formLaws chartLaws_pf
  onto := ontoOf3_pf
  slant := GlobalTheory.CompanionTheory.KunGlue.slantOf topRes_pf

theorem htBij_of  (hH : HT.HodgeTateMapExists) (hS : SqEx3) (hD : DiagEt3) (hF : EtFin) : HTBij :=
  htBij_of_parts (parts ) rank_equality hH hS hD hF

end CrystallineSemistableComparison.Onto
