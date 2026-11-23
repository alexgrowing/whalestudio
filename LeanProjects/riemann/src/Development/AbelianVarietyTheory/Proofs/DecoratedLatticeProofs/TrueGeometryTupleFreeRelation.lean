import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepBeforeLastEqSSucc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TupleFreeLevelLeCompact
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeClosed
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryFiniteAdelicGroupSplitFinitePlaceSet
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsGAtAllPlacesMul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTupleFreeIndexStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TupleFreeLevelStepStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.PenLev.rd_mem_KO_same : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ j (hj : j + 1 = B.R.m), ∀ t₀ (J₀ : QJ a t₀), J₀.Reads → ∀ t (J : QJ a t), J.Reads → ∀ i₀ i, (J₀.G i₀).q.v = (J.G i).q.v → ∀ g ∈ GfC _, GlobalTheory.PenBridge.rd J₀ j hj g i₀ ∈ KO (J₀.G i₀).k _ → GlobalTheory.PenBridge.rd J j hj g i ∈ KO (J.G i).k _ := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W _ u a ha _ j hj t₀ J₀ _ t J _ i₀ i hv g _ h0
  have hsd : IsSelfDualC ((I.rec7 l Z).sp.X j) (a.g.x j).L :=
    (ha.x j (by have h2 : (I.rec7 l Z).R.m = B.R.m := rfl; omega)).sd
  have h0' : GlobalTheory.LevIdx.locHom (J₀.G i₀).q _ (GlobalTheory.PenBridge.frJ J₀ j i₀ (GlobalTheory.PenBridge.step_before_last_eq_s_succ J₀ hj i₀)) g ∈ KO (J₀.G i₀).k _ :=
    (GlobalTheory.PenBridge.toSum0_mem_KO_iff _).1 h0
  have hm := GlobalTheory.LevProd.SamePlace.moves_of_mem_KO (J₀.G i₀).q _ hsd
    (GlobalTheory.PenBridge.intIn_frJ J₀ j i₀ (GlobalTheory.PenBridge.step_before_last_eq_s_succ J₀ hj i₀)) h0'
  change GlobalTheory.PenBridge.toSum0 _ _ _ ∈ _
  rw [GlobalTheory.PenBridge.toSum0_mem_KO_iff]
  exact GlobalTheory.SplitInt.mem_KO_of_moves (J.G i).q _ (GlobalTheory.PenBridge.frJ J j i (GlobalTheory.PenBridge.step_before_last_eq_s_succ J hj i)) (a.g.x j).L
    (· = (J₀.G i₀).q.v) hv.symm (GlobalTheory.PenBridge.intIn_frJ J j i (GlobalTheory.PenBridge.step_before_last_eq_s_succ J hj i)) g hm _
    ((GlobalTheory.LevIdx.eq_locHom_iff _ _ _ _ _).2 rfl)

theorem GlobalTheory.PenLev.rd_eq_one_of_grpAt {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : B.Word} {a : GeoAll W u} {t : W.P.T}
    (J : QJ a t) {j : ℕ} (hj : j + 1 = B.R.m) (i : Fin J.r) {P : GlobalTheory.FinPl.Pl (I.rec7 l Z) → Prop} (hP : ¬ P (J.G i).q.v)
    {x : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)} (hx : x ∈ GlobalTheory.FinPl.grpAt _ P) : GlobalTheory.PenBridge.rd J j hj x i = 1 := by
  have h1 : x ∈ GlobalTheory.FinPl.grpOff _ (· = (J.G i).q.v) :=
    GlobalTheory.FinPl.SetCut.grpAt_le_grpOff _ P (· = (J.G i).q.v) (fun p hp e => hP (e ▸ hp)) hx
  have h2 := GlobalTheory.LocMod.PinInhab.map_mt_eq_one_of_off (J.G i).q (P := (· = (J.G i).q.v)) rfl h1
  have h3 : GlobalTheory.LevIdx.locHom (J.G i).q _ (GlobalTheory.PenBridge.frJ J j i (GlobalTheory.PenBridge.step_before_last_eq_s_succ J hj i)) x = 1 := by
    symm
    rw [← GlobalTheory.LevIdx.eq_locHom_iff, h2]
    simp [(GlobalTheory.PenBridge.frJ J j i (GlobalTheory.PenBridge.step_before_last_eq_s_succ J hj i)).βγ]
  change GlobalTheory.PenBridge.toSum0 _ _ _ = 1
  rw [h3, map_one]

theorem GlobalTheory.PenLev.relax_rd_mem_KO : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ j (hj : j + 1 = B.R.m), ∀ t (J : QJ a t), J.Reads → ∀ (α : J.Ch j) t' (J' : QJ a t'), J'.Reads → ∀ g ∈ GlobalTheory.PenLev.relax J j hj α, ∀ i, GlobalTheory.PenBridge.rd J' j hj g i ∈ KO (J'.G i).k _ := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hTr j hj t J hJ α t' J' hJ' g hg i
  obtain ⟨hsup, hgf, hrd⟩ := (GlobalTheory.PenLev.mem_relax_iff J j hj α g).1 hg
  by_cases hv : GlobalTheory.PenBridge.plF J (J'.G i).q.v
  · obtain ⟨i₀, hi₀⟩ := hv
    exact GlobalTheory.PenLev.rd_mem_KO_same W hW u a ha hTr j hj t J hJ t' J' hJ' i₀ i hi₀ g hgf (hrd i₀)
  · have hle : J.A.U j (J.ι j α) ⊔ GlobalTheory.FinPl.grpAt _ (GlobalTheory.PenBridge.plF J) ≤
        (KO (J'.G i).k _).comap ((Pi.evalMonoidHom _ i).comp (GlobalTheory.PenBridge.rd J' j hj)) := by
      refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · exact GlobalTheory.T.true_geometry_tuple_free_index W hW u a ha hTr j hj t J hJ α t' J' hJ' i hv x hx
      · rw [Subgroup.mem_comap, MonoidHom.comp_apply, Pi.evalMonoidHom_apply,
          GlobalTheory.PenLev.rd_eq_one_of_grpAt J' hj i hv hx]
        exact one_mem _
    exact hle hsup

theorem GlobalTheory.PenLev.relaxed_level_eq_tuple_free : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ j (hj : j + 1 = B.R.m), ∀ t (J : QJ a t), J.Reads → ∀ α : J.Ch j, GlobalTheory.PenLev.relax J j hj α = GlobalTheory.PenLev.U0 a j hj := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hTr j hj t J hJ α
  have hle : ∀ t (J : QJ a t), J.Reads → ∀ (α : J.Ch j) t' (J' : QJ a t'), J'.Reads → ∀ (α' : J'.Ch j),
      GlobalTheory.PenLev.relax J j hj α ≤ GlobalTheory.PenLev.relax J' j hj α' := by
    intro t J hJ α t' J' hJ' α' x hx
    have hx' := (GlobalTheory.PenLev.mem_relax_iff J j hj α x).1 hx
    exact (GlobalTheory.PenLev.mem_relax_iff J' j hj α' x).2
      ⟨GlobalTheory.T.tuple_free_level_step W hW u a ha hTr j hj t J hJ α t' J' hJ' α' x hx, hx'.2.1,
        GlobalTheory.PenLev.relax_rd_mem_KO W hW u a ha hTr j hj t J hJ α t' J' hJ' x hx⟩
  obtain ⟨t₀, J₀, α₀, hJ₀, h⟩ := GlobalTheory.PenLev.tuple_free_level_eq_relaxed J j hj hJ α
  rw [h]
  exact le_antisymm (hle _ _ hJ α _ _ hJ₀ α₀) (hle _ _ hJ₀ α₀ _ _ hJ α)
