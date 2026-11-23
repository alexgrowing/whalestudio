import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowsMemBaseChainStageZero
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FormsAtZero
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.InverseLevelCardinality
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.BaseChain
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
theorem levS_datYt_base_alt (W : _root_.GlobalTheory.MiS.RealPackAlt ex) :
    levS (Yc D 0) ((_root_.GlobalTheory.Fam.pk_z W).βY 0) ((_root_.GlobalTheory.Fam.pk_z W).datYt W.P.A3.A.μ0 0 (_root_.GlobalTheory.Fam.complexLevelStructure W)) = levS (Yc D 0) ((_root_.GlobalTheory.Fam.pk_z W).βY 0) ((_root_.GlobalTheory.Fam.pk_z W).dat0 (_root_.GlobalTheory.Fam.complexLevelStructure W)) := by
  have e : Formalism.L2.DIV.lev D.sp.cm (Yc D 0).gram ((_root_.GlobalTheory.Fam.pk_z W).βY 0) ((_root_.GlobalTheory.Fam.pk_z W).datYt W.P.A3.A.μ0 0 (_root_.GlobalTheory.Fam.complexLevelStructure W)) =
      Formalism.L2.DIV.lev D.sp.cm (Yc D 0).gram ((_root_.GlobalTheory.Fam.pk_z W).βY 0) ((_root_.GlobalTheory.Fam.pk_z W).dat0 (_root_.GlobalTheory.Fam.complexLevelStructure W)) := by
    refine Subgroup.ext fun x => ?_
    show (x ∈ parLev _ _ _ _ ∧ _) ↔ (x ∈ parLev _ _ _ _ ∧ _)
    unfold LevCh.datYt LevCh.dat0
    rw [Formalism.IndefR.Eqv.Act.mem_parLev_datY_noQ Formalism.IndefR.Eqv.Act.rank_lowerChainSpace_zero_le (r_le_Y 0) D.R.t 0 (_root_.GlobalTheory.Fam.pk_z W).Pg
      ((_root_.GlobalTheory.Fam.pk_z W).Q W.P.A3.A.μ0) (_root_.GlobalTheory.Fam.complexLevelStructure W) (_root_.GlobalTheory.Fam.pk_z W).chi ((_root_.GlobalTheory.Fam.pk_z W).xiR W.P.A3.A.μ0) (fun _ => 1) Lev.Frm.B x]
    rfl
  unfold levS Lev.levG
  rw [e]
theorem levChi_datYt_zero_eq_dat0 (W : _root_.GlobalTheory.MiS.RealPackAlt ex) :
    Lev.levChi (Yc D 0) ((_root_.GlobalTheory.Fam.pk_z W).βY 0) ((_root_.GlobalTheory.Fam.pk_z W).datYt W.P.A3.A.μ0 0 (_root_.GlobalTheory.Fam.complexLevelStructure W)) =
      Lev.levChi (Yc D 0) ((_root_.GlobalTheory.Fam.pk_z W).βY 0) ((_root_.GlobalTheory.Fam.pk_z W).dat0 (_root_.GlobalTheory.Fam.complexLevelStructure W)) := by
  funext k
  unfold Lev.levChi LevCh.datYt LevCh.dat0
  rw [levFn_datY_noQ ((_root_.GlobalTheory.Fam.pk_z W).βY 0) Formalism.IndefR.Eqv.Act.rank_lowerChainSpace_zero_le (r_le_Y 0) D.R.t 0 (_root_.GlobalTheory.Fam.pk_z W).Pg
      ((_root_.GlobalTheory.Fam.pk_z W).Q W.P.A3.A.μ0) (_root_.GlobalTheory.Fam.complexLevelStructure W) (_root_.GlobalTheory.Fam.pk_z W).chi ((_root_.GlobalTheory.Fam.pk_z W).xiR W.P.A3.A.μ0) (fun _ => 1) Lev.Frm.B]
theorem initial_tuples_mem_stageY_zero_CC : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ T ∈ _root_.GlobalTheory.MiTop.BaseRowSpace W, T ∈ (_root_.GlobalTheory.BaseChain.stageOfSpaceY W 0).CC (_root_.GlobalTheory.BaseChain.com_z W) := by
  intro D L hT Gi Gl Kc Yd cX ex W _ T hT0
  show T ∈ MultT (_root_.GlobalTheory.Fam.pk_z W).θ ((_root_.GlobalTheory.Fam.pk_z W).MY 0) (levS (Yc D 0) ((_root_.GlobalTheory.Fam.pk_z W).βY 0) ((_root_.GlobalTheory.Fam.pk_z W).datYt W.P.A3.A.μ0 0 (_root_.GlobalTheory.Fam.complexLevelStructure W)))
    (Lev.levChi (Yc D 0) ((_root_.GlobalTheory.Fam.pk_z W).βY 0) ((_root_.GlobalTheory.Fam.pk_z W).datYt W.P.A3.A.μ0 0 (_root_.GlobalTheory.Fam.complexLevelStructure W)))
  rw [_root_.GlobalTheory.BaseChain.levS_datYt_base_alt W, _root_.GlobalTheory.BaseChain.levChi_datYt_zero_eq_dat0 W]
  exact hT0
end GlobalTheory.BaseChain
end
end
