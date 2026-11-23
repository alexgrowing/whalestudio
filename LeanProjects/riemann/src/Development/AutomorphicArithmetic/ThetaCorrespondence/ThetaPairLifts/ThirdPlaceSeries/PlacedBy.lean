import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacedBy
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.STiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ChartZero
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.InverseLevelCardinality
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Placed

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.LevZero
open GlobalTheory.ChainOnto (Com)
variable {D : D7}
section Common
variable {c : Comm D} {v : VCom c}
end Common
variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
abbrev datZero_alt (W : _root_.GlobalTheory.MiS.RealPackAlt ex) : Formalism.L2.DIV.LevDat D.host.E ℂ (Yc D 0).rank :=
  W.Q.Rl.dat0 (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true)
def levelZeroState (W : _root_.GlobalTheory.MiS.RealPackAlt ex) : StAt (Yc D 0) where
  par := (_root_.GlobalTheory.BaseChain.stageOfSpaceY W 0).par
  M := (_root_.GlobalTheory.BaseChain.stageOfSpaceY W 0).M
  Λ := (_root_.GlobalTheory.Fam.pk_z W).ΛY 0
  β := (_root_.GlobalTheory.Fam.pk_z W).βY 0
  L := _root_.GlobalTheory.LevZero.datZero_alt W
  ν := (_root_.GlobalTheory.BaseChain.stageOfSpaceY W 0).ν
  fd := (_root_.GlobalTheory.BaseChain.stageOfSpaceY W 0).fd
variable {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : D.what₂.Word}
structure PlacedByLocalGroups (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0))
    {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
    (v : VCom f.c) (o : TDat f.c k ι) {n : ℕ} (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg) : Prop where
  cis : f.c.Is
  vis : v.Is
  tie : _root_.GlobalTheory.Fam.CommutingVectorTie f v
  shape : ShapeOff v o
  pin : GPin G
  read : _root_.GlobalTheory.Fam.LocalGroupReading f G pl
  bot : _root_.GlobalTheory.MiTop.LocalBottomCompatibility f B v o G
set_option maxHeartbeats 1000000 in
def frameAtTranslate (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (a₀ a : GA D (D.sp.X 0)) :
    GL (Fin (D.sp.Y 0).rank) (Lev.EAf D) :=
  finE (D.sp.Y 0) (_root_.GlobalTheory.MiTop.translationElement f B a₀ a) * (show GL (Fin (D.sp.Y 0).rank) (Lev.EAf D) from (_root_.GlobalTheory.Fam.pk_z W).βY 0)
set_option maxHeartbeats 1000000 in
def StabiliserCondition (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (a₀ a : GA D (D.sp.X 0)) : Prop :=
  ∀ κ : GA D (D.sp.Y 0), (κ ∈ GfC (D.sp.Y 0) ∧ finE (D.sp.Y 0) κ ∈ Formalism.L2.DIV.St (_root_.GlobalTheory.LevZero.frameAtTranslate f B a₀ a)) ↔
    ((iotaX W.S.X W.Q.instEq κ).1 = 1 ∧ (iotaX W.S.X W.Q.instEq κ).2 ∈ W.S.X.B.I.Kset)
end GlobalTheory.LevZero
end
end
