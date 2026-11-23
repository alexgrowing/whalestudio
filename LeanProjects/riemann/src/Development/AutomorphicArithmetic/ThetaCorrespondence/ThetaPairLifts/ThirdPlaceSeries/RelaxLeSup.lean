import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TupleFreeLevelStep
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.QuadraticExtensionData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TupleFreeLevelLeCompact
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.StepBeforeLastEqSSucc
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CutMemUStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SuppMemLevelStatement

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel
noncomputable section
namespace GlobalTheory.PenLev.CongruenceSubgroupLevelSupport
open GlobalTheory.FinPl GlobalTheory.FinPl.SetCut
variable {D : D7}
end GlobalTheory.PenLev.CongruenceSubgroupLevelSupport
end
noncomputable section
open GlobalTheory.FinPl GlobalTheory.FinPl.SetCut GlobalTheory.PenLev.CongruenceSubgroupLevelSupport in
theorem GlobalTheory.PenLev.relax_le_sup_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 1 = B.R.m), ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (α : J.Ch j) t' (J' : _root_.GlobalTheory.Fam.QuadraticExtensionData a t'), J'.Reads → ∀ (α' : J'.Ch j), ∀ g ∈ _root_.GlobalTheory.PenLev.relaxedLevelSubgroup J j hj α, g ∈ J'.A.U j (J'.ι j α') ⊔ GlobalTheory.FinPl.grpAt _ (_root_.GlobalTheory.PenBridge.finitePlaceCondition J') := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hat j hj t J hJ α t' J' hJ' α' g hg
  classical
  rw [_root_.GlobalTheory.PenLev.mem_relax_iff'] at hg
  obtain ⟨hsup, -, hint⟩ := hg
  let QJ : Finset (Pl (I.rec7 l Z)) := Finset.univ.image fun i => (J.G i).q.v
  let QJ' : Finset (Pl (I.rec7 l Z)) := Finset.univ.image fun i => (J'.G i).q.v
  have hQJ : ∀ p, _root_.GlobalTheory.PenBridge.finitePlaceCondition J p ↔ p ∈ QJ := fun p => by simp [QJ, _root_.GlobalTheory.PenBridge.finitePlaceCondition]
  have hQJ' : ∀ p, _root_.GlobalTheory.PenBridge.finitePlaceCondition J' p ↔ p ∈ QJ' := fun p => by simp [QJ', _root_.GlobalTheory.PenBridge.finitePlaceCondition]
  set Q := QJ ∪ QJ' with hQ
  set P := QJ \ QJ' with hP
  have hN : (grpAt ((I.rec7 l Z).sp.X j) (_root_.GlobalTheory.PenBridge.finitePlaceCondition J)).Normal := by
    unfold grpAt congGrp
    infer_instance
  have hmul := Subgroup.mul_normal (J.A.U j (J.ι j α)) (grpAt ((I.rec7 l Z).sp.X j) (_root_.GlobalTheory.PenBridge.finitePlaceCondition J))
  have hg' : g ∈ ((J.A.U j (J.ι j α) ⊔ grpAt ((I.rec7 l Z).sp.X j) (_root_.GlobalTheory.PenBridge.finitePlaceCondition J) : Subgroup _) : Set (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j))) := hsup
  rw [hmul] at hg'
  obtain ⟨x, hx, n, hn, rfl⟩ := hg'
  beta_reduce at hint ⊢
  have hxf : x ∈ GfC ((I.rec7 l Z).sp.X j) := ((hJ.is.U j (by omega) _ x).1 hx).1
  have huo : cutG ((I.rec7 l Z).sp.X j) _ (one_sub_idemQ_mul_self Q) x ∈ J'.A.U j (J'.ι j α') :=
    _root_.GlobalTheory.T.true_geometry_row_step_value_alt W hW u a ha hat j hj t J hJ α t' J' hJ' α' Q (fun p hp => Finset.mem_union_left _ ((hQJ p).1 hp))
      (fun p hp => Finset.mem_union_right _ ((hQJ' p).1 hp)) x hx
  set uo := cutG ((I.rec7 l Z).sp.X j) _ (one_sub_idemQ_mul_self Q) x
  set uq := cutG ((I.rec7 l Z).sp.X j) _ (idemQ_mul_self Q) x
  have huq : uq ∈ grpAt ((I.rec7 l Z).sp.X j) (· ∈ Q) := cutG_mem_Q ((I.rec7 l Z).sp.X j) Q x
  have huoQ : uo ∈ grpAt ((I.rec7 l Z).sp.X j) (· ∉ Q) := cutG_mem_Qc ((I.rec7 l Z).sp.X j) Q hxf
  have hnQ : n ∈ grpAt ((I.rec7 l Z).sp.X j) (· ∈ Q) := grpAt_mono ((I.rec7 l Z).sp.X j) (fun p hp => Finset.mem_union_left _ ((hQJ p).1 hp)) hn
  set w := uq * n
  have hw : w ∈ grpAt ((I.rec7 l Z).sp.X j) (· ∈ Q) := mul_mem huq hnQ
  have hgw : uq * uo * n = uo * w := by
    rw [comm_Q ((I.rec7 l Z).sp.X j) Q huq huoQ, mul_assoc]
  have hx' : x = uq * uo := (cutG_mul_cutG ((I.rec7 l Z).sp.X j) Q x).symm
  set wp := cutG ((I.rec7 l Z).sp.X j) _ (idemQ_mul_self P) w
  set wr := cutG ((I.rec7 l Z).sp.X j) _ (one_sub_idemQ_mul_self P) w
  have hwp : wp ∈ grpAt ((I.rec7 l Z).sp.X j) (· ∈ P) := cutG_mem_Q ((I.rec7 l Z).sp.X j) P w
  have hwrP : wr ∈ grpAt ((I.rec7 l Z).sp.X j) (· ∉ P) := cutG_mem_Qc ((I.rec7 l Z).sp.X j) P (grpAt_le_GfC ((I.rec7 l Z).sp.X j) _ hw)
  have hwrQ : wr ∈ grpAt ((I.rec7 l Z).sp.X j) (· ∈ Q) := cutG_mem_congGrp ((I.rec7 l Z).sp.X j) _ _ _ hw
  have hwr : wr ∈ grpAt ((I.rec7 l Z).sp.X j) (_root_.GlobalTheory.PenBridge.finitePlaceCondition J') :=
    grpAt_inf_le ((I.rec7 l Z).sp.X j) (· ∈ Q) (· ∈ P) _ (fun p h1 h2 => by
      rw [hQJ']
      rw [hQ, Finset.mem_union] at h1
      rw [hP, Finset.mem_sdiff] at h2
      tauto) hwrQ hwrP
  have hww : w = wp * wr := (cutG_mul_cutG ((I.rec7 l Z).sp.X j) P w).symm
  have hgeq : x * n = uo * wp * wr := by
    rw [hx', hgw, hww, mul_assoc]
  have hwp' : wp ∈ J'.A.U j (J'.ι j α') := by
    refine _root_.GlobalTheory.T.true_geometry_row_step_relation_alt W hW u a ha hat j hj t J hJ t' J' hJ' α' P (fun p hp => ?_) wp hwp (fun i hi => ?_)
    · rw [hP, Finset.mem_sdiff] at hp
      exact ⟨(hQJ p).2 hp.1, fun h => hp.2 ((hQJ' p).1 h)⟩
    · have hiQ : (J.G i).q.v ∈ Q := by
        rw [hP, Finset.mem_sdiff] at hi
        exact Finset.mem_union_left _ hi.1
      have e1 : _root_.GlobalTheory.PenBridge.reductionHomAtLastLevel J j hj uo i = 1 := by
        show _root_.GlobalTheory.PenBridge.reductionHomAtLevel J j i _ uo = 1
        rw [_root_.GlobalTheory.PenBridge.rd_at_apply, locHom_eq_one (J.G i).q ((I.rec7 l Z).sp.X j) _ (P := (· ∈ Q)) hiQ
          (grpAt_le_grpOff ((I.rec7 l Z).sp.X j) (· ∉ Q) (· ∈ Q) (fun p h h' => h h') huoQ), map_one]
      have e2 : _root_.GlobalTheory.PenBridge.reductionHomAtLastLevel J j hj wr i = 1 := by
        show _root_.GlobalTheory.PenBridge.reductionHomAtLevel J j i _ wr = 1
        rw [_root_.GlobalTheory.PenBridge.rd_at_apply, locHom_eq_one (J.G i).q ((I.rec7 l Z).sp.X j) _ (P := (· ∈ P)) hi
          (grpAt_le_grpOff ((I.rec7 l Z).sp.X j) (· ∉ P) (· ∈ P) (fun p h h' => h h') hwrP), map_one]
      have h := hint i
      rw [hgeq, map_mul, map_mul, Pi.mul_apply, Pi.mul_apply, e1, e2, one_mul, mul_one] at h
      exact h
  rw [hgeq]
  exact mul_mem (Subgroup.mem_sup_left (mul_mem huo hwp')) (Subgroup.mem_sup_right hwr)
end
end
