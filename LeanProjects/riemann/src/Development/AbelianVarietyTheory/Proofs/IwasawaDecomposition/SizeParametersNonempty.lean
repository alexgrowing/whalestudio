import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TiesBOfExplicit
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsExplicitParameters
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowNumAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ForcedContentEqOverSameChoices
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResCharConj
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IndicesPairingLengthsVanishOffTwistedPlacesStatement

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Col2
open Formalism.MainNotions.Inhab Formalism.BasicNotions.TH Formalism.L2.GlobalTheoryTheory IsDedekindDomain NumberField GlobalTheory.EX GlobalTheory.EX.OB

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HeightCounting.Up.SizePar

theorem exists_params_atMem (hL : GlobalTheory.Published.LocalLanglandsGL) :
    AtMem hL fun _ _ _ _ w Z _ _ _ _ _ _ => ∃ L : SizeData₂ (w.D Z), Nonempty (ParameterChoice' (w.D Z) L) := by
  refine (evG_of_ev GlobalTheory.PrimIn.AtData.ev_params).imp fun K _ _ _ _ hK => ?_
  refine ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, by simp, by simp,
    fun B f T hO _ _ _ _ w Z Wt p0 t nch n xd c _ _ _ => ?_⟩
  obtain ⟨L, -, -, hp, -⟩ := hK (w.st Z) hO t.etaF fun v hv j h1 h2 => by
    have key : ∀ v', (w.D Z).what₂.muAt v' = (w.D Z).what₂.mu0 → v' ∉ Wt := by
      intro v' he hw
      have he' : (w.st Z).W.muAt v' = (w.st Z).C.mu0 := he
      rw [t.mu.on v' hw] at he'
      have h1 := t.mu.tw v'
      rw [he', t.mu.mu0] at h1
      exact (TwFin.tw_fin B f T).2.1 v' h1.symm
    change (w.D Z).what₂.Aj j v = 0
    replace hv : (w.D Z).what₂.muAt v = (w.D Z).what₂.mu0 := hv
    have a := t.untw v (key v hv) j h1 h2
    have b := t.untw _ (key _ (((w.D Z).what₂.muAt_conj v).trans hv)) j h1 h2
    unfold Formalism.BasicNotions.Rows.Data.Aj
    rw [hv, a.1, a.2, b.1]
    rfl
  exact ⟨L, hp⟩

end GlobalTheory.HeightCounting.Up.SizePar

namespace GlobalTheory.HeightCounting.Up.SizePar

set_option maxHeartbeats 2000000 in

theorem ev_params_withLoc : Ev fun K => ∀ X : Stages, K.Over X.B.toPre → X.V.div.etaF = 6 * K.s.x ^ (-K.C.P.CF) →
    (∀ w, X.toD7.what₂.muAt w = X.toD7.what₂.mu0 → ∀ j, 1 ≤ j → j ≤ X.toD7.R.m → X.toD7.what₂.Aj j w = 0) →
    (∃ L : SizeData₂ X.toD7, Nonempty (ParameterChoice' X.toD7 L)) ∧
      ∀ Lc : LocAll (lay0 X.toD7), ∃ L : SizeData₂ (withLoc Lc), Nonempty (ParameterChoice' (withLoc Lc) L) := by
  refine ⟨1, one_pos, fun eps C8 h0 _ h1 _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C hC _ _ => ?_⟩⟩
  obtain ⟨c1, hN⟩ := GlobalTheory.EX.szRow_numAt eps h0 h1 C hC
  refine ⟨max c1 0, fun cD hcD => ?_⟩
  obtain ⟨c2, hN⟩ := hN cD ((le_max_left _ _).trans hcD)
  refine ⟨max c2 402, fun ch hch => ?_⟩
  obtain ⟨x1, hN⟩ := hN ch ((le_max_left _ _).trans hch)
  obtain ⟨x0, hx0⟩ := GlobalTheory.EX.exists_sizeData_explicit eps C cD ch h0 h1 hC ((le_max_right _ _).trans hcD) ((le_max_right _ _).trans hch)
  refine ⟨max x0 x1, ?_⟩
  rintro K rfl rfl rfl hs hx X hO heta hA
  have hP := K.ok
  obtain ⟨sp, hT, hY, hA', hV, hz, hB, -⟩ := hO
  obtain ⟨B, Cc, W, V, S, N, Gj⟩ := X
  cases B
  dsimp only at hB
  subst hB
  set D := Stages.toD7 _ with hD
  have hlev : ∀ p ∈ K.Lv.host.levelPrimes, K.Lv.host.cls p = .splitK := (Pre.ofCh K.P K.Lv sp hT hY hA' hV hz).level_split
  have hdel : D.s.Del = (Delv K.s K.cD : ℚ) := by
    have τ : Tau K.P.R := tauPl D (false, 0)
    have hk := K.P.R.m_add_three_le_k
    have hm := K.P.R.two_le_m
    have hl : 0 + 1 < K.P.R.k - 1 := by omega
    have a1 := D.s.cloud_gap K.P.u₀ τ 0 hl
    have a2 := congrArg₂ (· - ·) ((hP.hc K.P.u₀).1 τ ⟨0, by omega⟩) ((hP.hc K.P.u₀).1 τ ⟨0 + 1, hl⟩)
    have a3 := a1.symm.trans a2
    have e : K.P.R.k - 2 - 0 = K.P.R.k - 2 - (0 + 1) + 1 := by omega
    dsimp only at a3
    rw [e] at a3
    push_cast at a3
    linarith
  have hGam : ∀ u, Real.log (D.mem u).A.GamP = K.C.CGam * (D.R.m : ℝ) ^ 5 * D.R.f * K.s.L := fun u => by
    have e : (D.mem u).A.GamP = K.Lv.GamP := Cc.A_GamP u
    rw [e, K.Gam_eq, GamS, Real.log_exp]; rfl
  refine ⟨?_, fun Lc => ?_⟩
  · obtain ⟨L, e1, -, -, e4⟩ := hx0 K.s D (fun t => K.a t.1) (fun t => K.b t.1) hs ((le_max_left _ _).trans hx) hP.rank hP.val
      (hP.hc K.P.u₀) hP.dlog hdel hP.ct2 hP.card heta hGam
      (fun t => hP.win t.1 t.2) (fun τ t h ht => hP.top K.P.u₀ τ t h ht) hA
    obtain ⟨⟨M⟩, -, -⟩ := hN D L (by rw [e1]; exact hs) (by rw [e1]; exact (le_max_right _ _).trans hx) e4
      ⟨hP.arith.1, hP.arith.2.1, hP.arith.2.2.1, hlev⟩
    exact ⟨L, ⟨M.params⟩⟩
  · obtain ⟨L, e1, -, -, e4⟩ := hx0 K.s (withLoc Lc) (fun t => K.a t.1) (fun t => K.b t.1) hs ((le_max_left _ _).trans hx)
      hP.rank hP.val (hP.hc K.P.u₀) hP.dlog hdel hP.ct2 hP.card heta hGam
      (fun t => hP.win t.1 t.2) (fun τ t h ht => hP.top K.P.u₀ τ t h ht) hA
    obtain ⟨⟨M⟩, -, -⟩ := hN (withLoc Lc) L (by rw [e1]; exact hs) (by rw [e1]; exact (le_max_right _ _).trans hx) e4
      ⟨hP.arith.1, hP.arith.2.1, hP.arith.2.2.1, hlev⟩
    exact ⟨L, ⟨M.params⟩⟩

end GlobalTheory.HeightCounting.Up.SizePar

namespace GlobalTheory.HeightCounting.Up.SizePar

theorem stepW_start_ev {Q : Ctx → Prop} (h : Ev Q) : StepW Start fun K _ _ _ _ => Q K :=
  Step.of_evG ((evG_of_ev h).imp fun _ _ _ _ _ H _ _ _ _ _ _ _ _ _ => H)

theorem aj_zero_at_state : StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P),
    ∀ v, (Dof x).what₂.muAt v = (Dof x).what₂.mu0 → ∀ j, 1 ≤ j → j ≤ (Dof x).R.m → (Dof x).what₂.Aj j v = 0 := by
  refine StepW.of_all fun K B f T w hO hF hS P x v hv j h1 h2 => ?_
  have hex : P.Wt = x.m.z.W1 (F0K K.s (w.D x.o.Z)) := by
    have e1 := x.m.W1 (F0K K.s (w.D x.o.Z))
    refine Eq.trans ?_ e1.symm
    refine P.exact.trans ?_
    rw [GlobalTheory.Mem.Top.Bl.RowWt.forcedContent_eq_over_same_choices K B f T w P.Z₀ x.o.Z P.kap (P.q.kap x.o.η x.o.hη x.o.V x.o.S x.o.N x.o.G)]
  have H := GlobalTheory.T.indices_pairingLengths_vanish_off_twistedPlaces K B f T w hO hF ⟨hS.1, ⟨P⟩⟩ P x hex
  have key : ∀ v', (w.D x.o.Z).what₂.muAt v' = (w.D x.o.Z).what₂.mu0 → v' ∉ P.Wt := by
    intro v' he hw
    have he' : P.q.W₀.muAt v' = w.C.mu0 := he
    rw [P.q.mu.on v' hw] at he'
    have e2 := P.q.mu.tw v'
    rw [he'] at e2
    exact (TwFin.tw_fin B f T).2.1 v' (e2.symm.trans (show w.I.xi w.C.mu0 = 1 from w.l.xi0))
  change (w.D x.o.Z).what₂.Aj j v = 0
  replace hv : (w.D x.o.Z).what₂.muAt v = (w.D x.o.Z).what₂.mu0 := hv
  have a := H v (key v hv) j h1 h2
  have b := H _ (key _ (((w.D x.o.Z).what₂.muAt_conj v).trans hv)) j h1 h2
  unfold Formalism.BasicNotions.Rows.Data.Aj
  rw [hv, a.1, a.2, b.1]
  rfl

theorem exists_params_allSt : AllSt fun _ _ _ _ _ _ x => (∃ L : SizeData₂ (Dof x), Nonempty (ParameterChoice' (Dof x) L)) ∧
    ∀ Lc : LocAll (lay0 (Dof x)), ∃ L : SizeData₂ (withLoc Lc), Nonempty (ParameterChoice' (withLoc Lc) L) :=
  ((stepW_start_ev ev_params_withLoc).and aj_zero_at_state).trans
    (StepW.of_all fun _ _ _ _ w hO _ H P x => H.1 (w.st x.o.Z) hO x.etaF (H.2 P x))

theorem exists_params :
    (∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ _ w Z _ _ _ _ _ _ => ∃ L : SizeData₂ (w.D Z), Nonempty (ParameterChoice' (w.D Z) L)) ∧
      AllSt fun _ _ _ _ _ _ x => (∃ L : SizeData₂ (Dof x), Nonempty (ParameterChoice' (Dof x) L)) ∧
        ∀ Lc : LocAll (lay0 (Dof x)), ∃ L : SizeData₂ (withLoc Lc), Nonempty (ParameterChoice' (withLoc Lc) L) :=
  ⟨exists_params_atMem, exists_params_allSt⟩

end GlobalTheory.HeightCounting.Up.SizePar

end
