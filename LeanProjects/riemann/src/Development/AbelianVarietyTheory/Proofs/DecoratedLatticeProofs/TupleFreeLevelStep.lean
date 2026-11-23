import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepBeforeLastEqSSucc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TupleFreeLevelLeCompact
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryFiniteAdelicGroupSplitFinitePlaceSet
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsGAtAllPlacesMul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryRowStepValueStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryRowStepRelationStatement
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

theorem cutG_mem_congGrp (V : HSp D) (I : Ideal (AE D)) (ε : AF D.host.F) (hε : ε * ε = ε) {g : GA D V}
    (hg : g ∈ congGrp V I) : cutG V ε hε g ∈ congGrp V I := by
  rw [mem_congGrp_iff] at hg ⊢
  intro i j
  rw [mt_cutG, cut_sub_one, Matrix.smul_apply, smul_eq_mul]
  exact Ideal.mul_mem_left _ _ (hg i j)

theorem grpAt_mono (V : HSp D) {P P' : Pl D → Prop} (h : ∀ p, P p → P' p) : grpAt V P ≤ grpAt V P' := by
  intro g hg
  rw [mem_grpAt_iff_parts] at hg ⊢
  exact fun i j => ⟨(hg i j).1, fun w hw => (hg i j).2 w fun h' => hw (h w h')⟩

theorem grpAt_inf_le (V : HSp D) (Q P R : Pl D → Prop) (h : ∀ p, Q p → ¬ P p → R p) {g : GA D V}
    (h1 : g ∈ grpAt V Q) (h2 : g ∈ grpAt V fun p => ¬ P p) : g ∈ grpAt V R := by
  rw [mem_grpAt_iff_parts] at h1 h2 ⊢
  refine fun i j => ⟨(h1 i j).1, fun w hw => ?_⟩
  by_cases hQ : Q w
  · by_cases hP : P w
    · exact (h2 i j).2 w (not_not.2 hP)
    · exact absurd (h w hQ hP) hw
  · exact (h1 i j).2 w hQ

theorem locHom_eq_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {Y : Type} [Fintype Y] [DecidableEq Y] (q : SplitPt D k) (V : HSp D) (F : GlobalTheory.LocMod.Frame k V.rank Y)
    {P : Pl D → Prop} (hP : P q.v) {g : GA D V} (hg : g ∈ grpOff V P) : GlobalTheory.LevIdx.locHom q V F g = 1 := by
  ext1
  rw [GlobalTheory.LevIdx.locHom_val, GlobalTheory.LocMod.PinInhab.map_mt_eq_one_of_off q hP hg, Matrix.mul_one, F.γβ]
  rfl

end GlobalTheory.PenLev.CongruenceSubgroupLevelSupport
end

noncomputable section
open GlobalTheory.FinPl GlobalTheory.FinPl.SetCut GlobalTheory.PenLev.CongruenceSubgroupLevelSupport in

theorem GlobalTheory.PenLev.relax_le_sup : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ j (hj : j + 1 = B.R.m), ∀ t (J : QJ a t), J.Reads → ∀ (α : J.Ch j) t' (J' : QJ a t'), J'.Reads → ∀ (α' : J'.Ch j), ∀ g ∈ GlobalTheory.PenLev.relax J j hj α, g ∈ J'.A.U j (J'.ι j α') ⊔ GlobalTheory.FinPl.grpAt _ (GlobalTheory.PenBridge.plF J') := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hat j hj t J hJ α t' J' hJ' α' g hg
  classical
  rw [mem_relax_iff] at hg
  obtain ⟨hsup, -, hint⟩ := hg
  let QJ : Finset (Pl (I.rec7 l Z)) := Finset.univ.image fun i => (J.G i).q.v
  let QJ' : Finset (Pl (I.rec7 l Z)) := Finset.univ.image fun i => (J'.G i).q.v
  have hQJ : ∀ p, GlobalTheory.PenBridge.plF J p ↔ p ∈ QJ := fun p => by simp [QJ, GlobalTheory.PenBridge.plF]
  have hQJ' : ∀ p, GlobalTheory.PenBridge.plF J' p ↔ p ∈ QJ' := fun p => by simp [QJ', GlobalTheory.PenBridge.plF]
  set Q := QJ ∪ QJ' with hQ
  set P := QJ \ QJ' with hP
  have hN : (grpAt ((I.rec7 l Z).sp.X j) (GlobalTheory.PenBridge.plF J)).Normal := by
    unfold grpAt congGrp
    infer_instance
  have hmul := Subgroup.mul_normal (J.A.U j (J.ι j α)) (grpAt ((I.rec7 l Z).sp.X j) (GlobalTheory.PenBridge.plF J))
  have hg' : g ∈ ((J.A.U j (J.ι j α) ⊔ grpAt ((I.rec7 l Z).sp.X j) (GlobalTheory.PenBridge.plF J) : Subgroup _) : Set (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j))) := hsup
  rw [hmul] at hg'
  obtain ⟨x, hx, n, hn, rfl⟩ := hg'
  beta_reduce at hint ⊢
  have hxf : x ∈ GfC ((I.rec7 l Z).sp.X j) := ((hJ.is.U j (by omega) _ x).1 hx).1

  have huo : cutG ((I.rec7 l Z).sp.X j) _ (one_sub_idemQ_mul_self Q) x ∈ J'.A.U j (J'.ι j α') :=
    GlobalTheory.T.true_geometry_row_step_value W hW u a ha hat j hj t J hJ α t' J' hJ' α' Q (fun p hp => Finset.mem_union_left _ ((hQJ p).1 hp))
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
  have hwr : wr ∈ grpAt ((I.rec7 l Z).sp.X j) (GlobalTheory.PenBridge.plF J') :=
    grpAt_inf_le ((I.rec7 l Z).sp.X j) (· ∈ Q) (· ∈ P) _ (fun p h1 h2 => by
      rw [hQJ']
      rw [hQ, Finset.mem_union] at h1
      rw [hP, Finset.mem_sdiff] at h2
      tauto) hwrQ hwrP
  have hww : w = wp * wr := (cutG_mul_cutG ((I.rec7 l Z).sp.X j) P w).symm
  have hgeq : x * n = uo * wp * wr := by
    rw [hx', hgw, hww, mul_assoc]

  have hwp' : wp ∈ J'.A.U j (J'.ι j α') := by
    refine GlobalTheory.T.true_geometry_row_step_relation W hW u a ha hat j hj t J hJ t' J' hJ' α' P (fun p hp => ?_) wp hwp (fun i hi => ?_)
    · rw [hP, Finset.mem_sdiff] at hp
      exact ⟨(hQJ p).2 hp.1, fun h => hp.2 ((hQJ' p).1 h)⟩
    · have hiQ : (J.G i).q.v ∈ Q := by
        rw [hP, Finset.mem_sdiff] at hi
        exact Finset.mem_union_left _ hi.1
      have e1 : GlobalTheory.PenBridge.rd J j hj uo i = 1 := by
        show GlobalTheory.PenBridge.rdAt J j i _ uo = 1
        rw [GlobalTheory.PenBridge.rdAt_apply, locHom_eq_one (J.G i).q ((I.rec7 l Z).sp.X j) _ (P := (· ∈ Q)) hiQ
          (grpAt_le_grpOff ((I.rec7 l Z).sp.X j) (· ∉ Q) (· ∈ Q) (fun p h h' => h h') huoQ), map_one]
      have e2 : GlobalTheory.PenBridge.rd J j hj wr i = 1 := by
        show GlobalTheory.PenBridge.rdAt J j i _ wr = 1
        rw [GlobalTheory.PenBridge.rdAt_apply, locHom_eq_one (J.G i).q ((I.rec7 l Z).sp.X j) _ (P := (· ∈ P)) hi
          (grpAt_le_grpOff ((I.rec7 l Z).sp.X j) (· ∉ P) (· ∈ P) (fun p h h' => h h') hwrP), map_one]
      have h := hint i
      rw [hgeq, map_mul, map_mul, Pi.mul_apply, Pi.mul_apply, e1, e2, one_mul, mul_one] at h
      exact h
  rw [hgeq]
  exact mul_mem (Subgroup.mem_sup_left (mul_mem huo hwp')) (Subgroup.mem_sup_right hwr)
end
