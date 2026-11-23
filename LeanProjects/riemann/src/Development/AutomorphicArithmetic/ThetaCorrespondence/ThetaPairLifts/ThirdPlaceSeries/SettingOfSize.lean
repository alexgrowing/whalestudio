import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetAtOfSizeAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SettingAtPoint
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LeafInfinitePlaceBound

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
namespace GlobalTheory.BigTop.Fun.SetFromSize
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}
set_option maxHeartbeats 1600000 in
theorem setting_of_size_alt (p : PtAt ex Csz) (hp : p.PointConditions') (hs : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows L) (he : GlobalTheory.GLq.ESerTie D) :
    HidaSetting L p.R.toRealDat p.F.lv2 where
  size := hs
  eser := he
  host := p.host
  hF := p.hF
  core := (GlobalTheory.OneMapBridge.heckeChoiceClauses_of_weakCharacterisation_at_face D _ _ _ _ _ _ p.R p.F p.charW hp.exAt).1
  mu_off := p.charW.tup.mu_off
  mu_used := p.charW.tup.mu_used
  mu_ne := p.charW.tup.mu_ne
  mu_conj := p.charW.tup.mu_conj
  mu_on := p.charW.tup.mu_on
  grp := p.charW.base.grp.record
  guard := p.qGuard
  fin := finite_tup p
  fullY := p.charW.fullY
  fullX := p.charW.fullX
  std := p.stdChar
  stdX := p.stdX
  betaX := p.betaStd.2
end GlobalTheory.BigTop.Fun.SetFromSize
namespace GlobalTheory.BigTop.Fun
theorem setAt_of_sizeAt_alt (h : _root_.GlobalTheory.BigTop.Fun.SizeAtAlt) : _root_.GlobalTheory.BigTop.Fun.SettingAtPoint :=
  h.imp fun _ _ _ a => _root_.GlobalTheory.BigTop.Fun.evPt_mono a fun _ _ _ p hp b he => _root_.GlobalTheory.BigTop.Fun.SetFromSize.setting_of_size_alt p hp b he
end GlobalTheory.BigTop.Fun
end
end
