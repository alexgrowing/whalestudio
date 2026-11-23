import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepBeforeLastEqSSucc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TupleFreeLevelLeCompact
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OneSubIdemQMulSelf
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeOpen
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel

noncomputable section
namespace GlobalTheory.PenBridge.SuppLev

set_option maxHeartbeats 1000000 in

theorem bc_prV_eq_one_of_not (D : D7) (S : HSp D) (n : ℕ) (hn : S.rank = n) (κ : GA D S)
    (g : GL (Fin n) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hg : GlobalTheory.AdForm.finM S hn κ = g.1) (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) (w : HeightOneSpectrum (𝓞 D.host.F))
    (hw : ¬ P w) (hκ : κ ∈ GlobalTheory.FinPl.grpAt S P) : Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) w) g = 1 := by
  subst hn
  have h1 : GlobalTheory.AdelicU.proj (Formalism.L2.Forms.sigD D) S.gram w κ = 1 :=
    ((GlobalTheory.FinPl.KOpen.mem_grpAt_iff S _ κ).1 hκ).2 w hw
  have hp := GlobalTheory.AdelicU.matHom_proj (Formalism.L2.Forms.sigD D) S.gram w κ
  have hE : Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) w) g =
      GlobalTheory.StabConjIndex.toGL (Formalism.L2.Forms.sigD D) S.gram w (GlobalTheory.AdelicU.proj _ S.gram w κ) := by
    ext i j
    have hij := congrFun (congrFun hg i) j
    have e1 : (GlobalTheory.StabConjIndex.toGL (Formalism.L2.Forms.sigD D) S.gram w (GlobalTheory.AdelicU.proj _ S.gram w κ)).val i j =
        GlobalTheory.StabConjIndex.swap w ((GlobalTheory.AdelicU.matHom (Fv D.host.F w) (Formalism.L2.Forms.sigD D) S.gram
          (GlobalTheory.AdelicU.proj (Formalism.L2.Forms.sigD D) S.gram w κ)).val i j) := rfl
    rw [e1, hp]
    show Formalism.UG.prV w (g.1 i j) = GlobalTheory.StabConjIndex.swap w (GlobalTheory.AdelicU.compFin _ _ w _)
    rw [← hij]
    exact GlobalTheory.FamTrace.prV_toEAf_eq_swap D w _
  rw [hE, h1, map_one]

set_option maxHeartbeats 1000000 in

theorem exists_mem_level_set (D : D7) (S : HSp D) (n : ℕ) (hn : S.rank = n) {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
    (K : StepLevel D.host.F D.host.E (sigD D) (S.gram.reindex (finCongr hn) (finCongr hn)) T f bad)
    (t : 𝓞 D.host.E) (ht : t ∣ (T : 𝓞 D.host.E))
    (hLb : ∀ x, x ∈ K.Lb ↔ ∀ j : Fin n, ∃ r : 𝓞 D.host.E, x j = (r : D.host.E) ∧ (j.1 + 1 = n → t ∣ r))
    (L : GlobalTheory.FinPl.Lat S) (hfg : L.FG) (hL : ∀ x, x ∈ L ↔ ∀ j, ∃ r : 𝓞 D.host.E, x j = (r : D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) (κ : GA D S) (hκ : κ ∈ GlobalTheory.FinPl.grpAt S P)
    (hP : ∀ v, P v → v ∉ bad ∧ (T : 𝓞 D.host.F) ∉ v.asIdeal ∧ GlobalTheory.FinPl.Moves S κ L L (· = v)) :
    ∃ x : K.U, x.1.1 = GlobalTheory.AdForm.finM S hn κ := by
  obtain ⟨g, hgU, hg⟩ : ∃ g ∈ Formalism.UG.UPts (sigD D) (S.gram.reindex (finCongr hn) (finCongr hn))
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F), GlobalTheory.AdForm.finM S hn κ = g.1 := by
    obtain ⟨e, he⟩ := GlobalTheory.FinPartIso.exists_finIso D S n hn
    have hf := GlobalTheory.FinPl.SetCut.grpAt_le_GfC S _ hκ
    exact ⟨(e ⟨κ, hf⟩).1, (e ⟨κ, hf⟩).2, (he ⟨κ, hf⟩).symm⟩
  refine ⟨⟨g, (K.U_eq _).2 ⟨hgU, fun w => ?_⟩⟩, hg.symm⟩
  by_cases hw : P w
  · obtain ⟨hb, hT, hm⟩ := hP w hw
    subst hn
    have key : ∀ j i : Fin S.rank, ∃ r : 𝓞 D.host.E,
        (Pi.single j (T : D.host.E) : Fin S.rank → D.host.E) i = (r : D.host.E) ∧ t ∣ r := fun j i => by
      rw [Pi.single_apply]
      split_ifs
      · exact ⟨T, (map_natCast (algebraMap (𝓞 D.host.E) D.host.E) T).symm, ht⟩
      · exact ⟨0, rfl, dvd_zero _⟩
    have e := GlobalTheory.FamTrace.levelVL_eq_of_std (sigD D) (S.gram.reindex (finCongr rfl) (finCongr rfl)) (Lb := K.Lb) (Λ := L) hT
      (fun x hx j => let ⟨r, hr, _⟩ := (hLb x).1 hx j; ⟨r, hr⟩)
      (fun j => (hLb _).2 fun i => let ⟨r, hr, hd⟩ := key j i; ⟨r, hr, fun _ => hd⟩)
      (fun x hx => (hL x).1 hx) (fun j => (hL _).2 fun i => let ⟨r, hr, _⟩ := key j i; ⟨r, hr⟩)
    rw [K.Uloc_hyp w hb hT, e]
    exact GlobalTheory.FamTrace.bc_prV_mem_levelVL_of_moves D S _ rfl L L hfg (fun _ => Iff.rfl) κ g hg w hm
  · rw [bc_prV_eq_one_of_not D S n hn κ g hg P w hw hκ]
    exact one_mem _

end GlobalTheory.PenBridge.SuppLev

open GlobalTheory.PenBridge in
set_option maxHeartbeats 2000000 in

theorem GlobalTheory.PenBridge.supp_mem_level : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ j (hj : j + 1 = B.R.m), ∀ t (J : QJ a t), J.Reads → ∀ t' (J' : QJ a t'), J'.Reads → ∀ (α' : J'.Ch j) (P : Finset (GlobalTheory.FinPl.Pl (I.rec7 l Z))), (∀ p ∈ P, GlobalTheory.PenBridge.plF J p ∧ ¬ GlobalTheory.PenBridge.plF J' p) → ∀ x ∈ GlobalTheory.FinPl.grpAt _ (· ∈ P), (∀ i, (J.G i).q.v ∈ P → GlobalTheory.PenBridge.rd J j hj x i ∈ KO (J.G i).k _) → x ∈ J'.A.U j (J'.ι j α') := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hat j hj t J hJ t' J' hJ' α' P hP x hx hrd
  have hjm : j ≤ B.R.m := by omega
  have hok : I.Ok := hW.tr.ok
  have hsd : IsSelfDualC ((I.rec7 l Z).sp.X j) (a.g.x j).L := (ha.x j hjm).sd
  haveI : Submodule.IsLattice (I.rec7 l Z).host.E (a.g.x j).L := hsd.1
  have hfg : (a.g.x j).L.FG := Submodule.IsLattice.fg (A := (I.rec7 l Z).host.E)
  have hlb := (hJ'.is.reads j hjm).lb (J'.ι j α')
  refine (hJ'.is.U j hjm _ _).2 ⟨GlobalTheory.FinPl.SetCut.grpAt_le_GfC _ _ hx, ?_⟩
  obtain ⟨-, hPr, -⟩ := GlobalTheory.Mem.Col2.base_fields_primes_ok B X
  have hd : X.piT u ∣ ((B.T u : ℕ) : 𝓞 B.host.E) := ⟨_, (hPr.piT_norm u).symm⟩
  refine GlobalTheory.PenBridge.SuppLev.exists_mem_level_set (I.rec7 l Z) _ _ _ (J'.A.K j hjm (J'.ι j α')).lev (X.piT u) hd hlb
    (a.g.x j).L hfg
    (fun y => ((hat.pinX.xs j hjm).2.2 y).trans
      (forall_congr' fun r => ⟨fun h => ⟨⟨y r, h⟩, rfl⟩, fun ⟨s, hs⟩ => hs ▸ s.2⟩)) (· ∈ P) x hx ?_
  intro v hvP
  obtain ⟨⟨i, hi⟩, hn'⟩ := hP v hvP
  subst hi
  have hu : I.UnderQ (W.P.I.tup t) (J.G i).q.v :=
    ⟨J.pl i, (hW.tq.Q t (J.pl i)).1 (J.mem i), ((GlobalTheory.Fam.QJPlaces.places_under W hW u a ha hat t J hJ).2 i).symm⟩
  obtain ⟨hTv, hgv⟩ := GlobalTheory.Mem.Col2.TC.underQ_notMem I hok l u _ _ hu
  refine ⟨fun h => ?_, hTv, ?_⟩
  · rcases hJ'.is.bad_le j hjm _ h with (h0 | h0) | ⟨Q, hQ, e⟩
    · exact hgv 0 h0
    · exact hgv 1 h0
    · obtain ⟨i', hi'⟩ := hJ'.surj Q ((hW.tq.Q t' Q).2 hQ)
      refine hn' ⟨i', ?_⟩
      rw [(GlobalTheory.Fam.QJPlaces.places_under W hW u a ha hat t' J' hJ').2 i', hi']
      exact e
  · have h1 := hrd i hvP
    rw [rd, MonoidHom.pi_apply, rdAt_apply, toSum0_mem_KO_iff] at h1
    exact GlobalTheory.LevProd.SamePlace.moves_of_mem_KO (J.G i).q _ hsd (intIn_frJ J j i (step_before_last_eq_s_succ J hj i)) h1

end
