import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.TowerRallisLemma

namespace CrystallineSemistableComparison.Onto

structure Parts : Prop where
  mv : MVBij
  surj : OneSurj
  cov : CovDesc
  site : SiteLaws
  on : OnIso
  zar : ZarAbs
  aff : AffOm
  nat : OmNat
  laws : FormLaws
  dw : DWedge
  dl : DLog
  kun : OmKun
  fc : FormCup
  c1 : FirstChernCoboundary
  div : DivCover
  chart : ChartLaws
  bij : ChartBij
  iso : IsoBij
  cup : CupLaws
  zarRel : ZarRelOf
  affRel : AffRelOf
  lift : RelLiftOf
  inj : RelInjOf
  cone : ConeKillOf
  kill : RelKillOf
  kunAff : KunAffOf
  slant : SlantOf
  killOf : KillOf3
  onto : OntoOf3
  low : OntoLow
  retr : Retract

theorem Parts.hodgeKill (h : Parts) : HodgeKill :=
  have zr := h.zarRel h.site h.on h.zar
  h.killOf h.site h.cup (h.lift h.site h.on) (h.inj h.site h.mv h.cov zr h.chart h.bij h.iso)
    (h.kill h.site h.cov zr h.aff h.nat (h.affRel h.site h.on h.aff h.nat h.laws) h.laws h.dw h.dl h.fc h.c1 h.div (h.cone h.surj))

theorem Parts.slant' (h : Parts) : Slant :=
  h.slant h.site h.mv h.cov h.zar h.aff (h.kunAff h.site h.aff h.nat h.laws h.fc h.kun)

theorem ontoAll_of (h : Parts) (hS : SqEx3) (hD : DiagEt3) (hF : EtFin) : OntoAll :=
  h.low h.cup h.retr (h.onto h.cup h.slant' h.hodgeKill hS hD hF)

end CrystallineSemistableComparison.Onto
