import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RationalRootsDef
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsMuIsRamified
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.NotMtStableOfFree
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoordMapBasisFun
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsProvisionalDivX
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsParametersOver
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulMemOfSpan
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FourMulRootLt

noncomputable section

namespace GlobalTheory.Mem.Top.V4.Model

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.FrobeniusOrbits Formalism.L2.Host Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField IsDedekindDomain

theorem ev_and {p q : Ctx → Prop} (hp : Ev p) (hq : Ev q) : Ev fun K => p K ∧ q K := by
  have L : ∀ {C : FC} {K K' : TransportedAlt} {CH : ℝ}, C.Large (K.sup K') CH → C.Large K CH ∧ C.Large K' CH := fun h =>
    ⟨⟨fun c hc => (le_max_left _ _).trans (h.1 c hc), trivial, fun c hc => (le_max_left _ _).trans (h.2.2.1 c hc),
      fun c hc => (le_max_left _ _).trans (h.2.2.2 c hc)⟩,
    ⟨fun c hc => (le_max_right _ _).trans (h.1 c hc), trivial, fun c hc => (le_max_right _ _).trans (h.2.2.1 c hc),
      fun c hc => (le_max_right _ _).trans (h.2.2.2 c hc)⟩⟩
  obtain ⟨a, ha, hp⟩ := hp
  obtain ⟨b, hb, hq⟩ := hq
  refine ⟨min a b, lt_min ha hb, fun e C8 he hle h52 h8 => ?_⟩
  obtain ⟨K, hK⟩ := hp e C8 he (hle.trans (min_le_left _ _)) h52 h8
  obtain ⟨K', hK'⟩ := hq e C8 he (hle.trans (min_le_right _ _)) h52 h8
  refine ⟨K.sup K', fun C hC hC8 hL => ?_⟩
  obtain ⟨a1, ha1⟩ := hK C hC hC8 (L hL).1
  obtain ⟨b1, hb1⟩ := hK' C hC hC8 (L hL).2
  refine ⟨max a1 b1, fun cD hcD => ?_⟩
  obtain ⟨a2, ha2⟩ := ha1 cD (le_trans (le_max_left _ _) hcD)
  obtain ⟨b2, hb2⟩ := hb1 cD (le_trans (le_max_right _ _) hcD)
  refine ⟨max a2 b2, fun ch hch => ?_⟩
  obtain ⟨a3, ha3⟩ := ha2 ch (le_trans (le_max_left _ _) hch)
  obtain ⟨b3, hb3⟩ := hb2 ch (le_trans (le_max_right _ _) hch)
  exact ⟨max a3 b3, fun X h1 h2 h3 h4 hx =>
    ⟨ha3 X h1 h2 h3 h4 (le_trans (le_max_left _ _) hx), hb3 X h1 h2 h3 h4 (le_trans (le_max_right _ _) hx)⟩⟩

theorem ev_imp {p q : Ctx → Prop} (hp : Ev p) (h : ∀ K, p K → q K) : Ev q := by
  obtain ⟨ε0, h0, H⟩ := hp
  refine ⟨ε0, h0, fun eps C8 a1 a2 a3 a4 => ?_⟩
  obtain ⟨K0, H⟩ := H eps C8 a1 a2 a3 a4
  refine ⟨K0, fun C b1 b2 b3 => ?_⟩
  obtain ⟨c1, H⟩ := H C b1 b2 b3
  refine ⟨c1, fun cD hcD => ?_⟩
  obtain ⟨c2, H⟩ := H cD hcD
  refine ⟨c2, fun ch hch => ?_⟩
  obtain ⟨x0, H⟩ := H ch hch
  exact ⟨x0, fun K d1 d2 d3 d4 d5 => h K (H K d1 d2 d3 d4 d5)⟩

theorem ev_all {p : Ctx → Prop} (h : ∀ K, p K) : Ev p :=
  ⟨1, one_pos, fun _ _ _ _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ => ⟨0, fun _ _ => ⟨0, fun _ _ => ⟨0,
    fun K _ _ _ _ _ => h K⟩⟩⟩⟩⟩

theorem rowLay_iff {D : D7} (Y : Lay D) : RowLay D Y.p0 Y.X ↔ ∀ w, D.what₂.muAt w = D.what₂.mu0 → ∀ j, 1 ≤ j → j ≤ D.R.m →
    D.what₂.Ij D.what₂.mu0 j w = 0 ∧ D.what₂.jw D.what₂.mu0 j w = 0 :=
  ⟨fun h => h.untw, fun h => ⟨Y.rrDef, Y.rationalRoots_def, Y.kap_def, Y.lam_def, Y.ties.bu_def, Y.ties.ft_occ, h, Y.idx, Y.kapR_def⟩⟩

def coreOfLay {K : Ctx} {X : Stages} {f : Fr X.B.toPre} {T : TwDat X.B} (Y : Lay X.toD7) (hO : K.Over X.B.toPre)
    (hR : RecOK K.s K.C K.cD X.toD7) (hL : LedOK K.s K.C K.cD K.ch Y K.a K.b)
    (xi : X.C.Tup → HChar X.B.host.E) (Wt : Set X.B.places.Pl) (mu : MuIsW X f T Wt xi)
    (forced : ∀ p : ℕ, p.Prime → ((∃ i, p = X.B.host.g i) ∨ p = X.B.host.d ∨ (p : ℝ) ≤ K.s.X'' X.B.R.n) → p ∈ T.pl)
    (gatNum : GatNum K.s X.toD7)
    (untw : ∀ w, X.toD7.what₂.muAt w = X.toD7.what₂.mu0 → ∀ j, 1 ≤ j → j ≤ X.toD7.R.m →
      X.toD7.what₂.Ij X.toD7.what₂.mu0 j w = 0 ∧ X.toD7.what₂.jw X.toD7.what₂.mu0 j w = 0)
    (mt : DQ.MtStableAt X.toD7) (real : Formalism.L2.Theta.RealTied X.toD7)
    (dsig_eq : ∀ τ, X.S.dsig τ = Vol.trueDsig X.B.R (X.B.hc τ))
    (chiT : ∀ (k : Fin 2) (v : X.N.nd.PlG k), ∃ w : (ZMod (X.B.host.g k))ˣ, orderOf w = X.B.host.g k - 1 ∧
      ∀ j : Fin X.B.R.m, X.N.nd.chiT k v j = w ^ (2 * (j.1 + 1)))
    (nch_Q : ∀ w ∈ Wt, Y.nch.Q w = T.Q w ∧ Y.nch.k' w = T.k w) : Core K X f T where
  isOver := hO
  xi := xi
  Wt := Wt
  mu := mu
  forced := forced
  fval := fun L a b c w hw => (hL L a b c).1 w (mu.off w hw)
  O := layObj Y
  col := ⟨Y.piG_lev, Y.piT_lev, Y.seen, Y.tauOf, fun u μ => (Y.dgam u μ).2, hR.mink, hR.atT⟩
  gatNum := gatNum
  gy := ⟨Y.vram, Y.fills_all, fun L a b c I d e g h => ((hL L a b c).2 I d e g h).1⟩
  row := (rowLay_iff Y).2 untw
  mtStable := mt
  th_io := Y.th_io
  gauge_def := Y.gauge_def
  real := real
  dsig_eq := dsig_eq
  del := hR.del
  etaF := hR.etaF
  chiT := chiT
  nch_tie := Y.nch_tie
  nch_Q := nch_Q

theorem del_of_over (K : Ctx) (X : Stages) (hO : K.Over X.B.toPre) : X.S.s.Del = (Delv K.s K.cD : ℚ) := by
  have hk : 0 + 1 < X.B.R.k - 1 := by have := X.B.R.m_add_three_le_k; have := X.B.R.two_le_m; omega
  have hne : Nonempty (Tau X.B.R) := Fintype.card_pos_iff.1 (by rw [card_Tau X.B.host]; unfold Ranks.f Ranks.n; positivity)
  obtain ⟨τ⟩ := hne
  have h1 := X.S.s.cloud_gap X.B.u₀ τ 0 hk
  have key : ∀ (P : Pre), K.Over P → ∀ (τ : Tau P.R) (h : 0 + 1 < P.R.k - 1),
      (P.hcW P.u₀ τ).v ⟨0, by omega⟩ - (P.hcW P.u₀ τ).v ⟨0 + 1, h⟩ = 4 * (Delv K.s K.cD : ℚ) := by
    rintro _ ⟨sp, hT, hY, hA, hV, hz, rfl, -⟩ τ h
    have a := (K.ok.hc K.P.u₀).1 τ ⟨0, by exact lt_of_le_of_lt (Nat.zero_le _) h⟩
    have b := (K.ok.hc K.P.u₀).1 τ ⟨0 + 1, h⟩
    have h' : 0 + 1 < K.P.R.k - 1 := h
    have e : ((K.P.R.k - 2 - 0 : ℕ) : ℚ) = ((K.P.R.k - 2 - (0 + 1) : ℕ) : ℚ) + 1 := by
      exact_mod_cast (by omega : K.P.R.k - 2 - 0 = K.P.R.k - 2 - (0 + 1) + 1)
    refine (congrArg₂ (· - ·) a b).trans ?_
    simp only [e]
    ring
  have h2 := key _ hO τ hk
  rw [h2] at h1
  linarith

theorem exists_generator (B : Base) (k : Fin 2) : ∃ w : (ZMod (B.host.g k))ˣ, orderOf w = B.host.g k - 1 := by
  haveI : Fact (B.host.g k).Prime := ⟨B.host.g_prime k⟩
  obtain ⟨w, hw⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod (B.host.g k))ˣ)
  exact ⟨w, by rw [hw, Nat.card_eq_fintype_card, ZMod.card_units]⟩

theorem exists_forced (K : Ctx) (P : Pre) : ∃ S : Finset ℕ,
    ∀ p : ℕ, p.Prime → ((∃ i, p = P.host.g i) ∨ p = P.host.d ∨ (p : ℝ) ≤ K.s.X'' P.R.n) → p ∈ S := by
  refine ⟨{P.host.g 0, P.host.g 1, P.host.d} ∪ Finset.range (⌊K.s.X'' P.R.n⌋₊ + 1), ?_⟩
  rintro p - (⟨i, rfl⟩ | rfl | h)
  · fin_cases i <;> simp
  · simp
  · exact Finset.mem_union_right _ (Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.le_floor h)))

theorem lg_forced (K : Ctx) : large₂ K fun B _ T =>
    ∀ p : ℕ, p.Prime → ((∃ i, p = B.host.g i) ∨ p = B.host.d ∨ (p : ℝ) ≤ K.s.X'' B.R.n) → p ∈ T.pl := by
  choose S hS using exists_forced K
  exact ⟨fun _ _ _ => ∅, fun P _ _ _ => S P, fun _ _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, by simp, by simp,
    fun B _ _ _ _ h _ p hp h' => h (hS _ p hp h')⟩

theorem isEmpty_core_untw (K : Ctx) (X : Stages) (f : Fr X.B.toPre) : IsEmpty (Core K X f (TwDat.untw X.B ∅)) :=
  ⟨fun c => Finset.notMem_empty _ (c.forced _ (X.B.host.g_prime 0) (.inl ⟨0, rfl⟩))⟩

theorem mem_iff {X : Stages} {f : Fr X.B.toPre} {T : TwDat X.B} {Wt : Set X.B.places.Pl} {xi : X.C.Tup → HChar X.B.host.E}
    (h : MuIsW X f T Wt xi) (w : X.B.places.Pl) : w ∈ Wt ↔ X.W.muAt w ≠ X.C.mu0 := by
  refine ⟨fun hw he => ?_, fun hw => by_contra fun hn => hw (h.off w hn)⟩
  have h1 := h.tw w
  rw [← h.on w hw, he, h.mu0] at h1
  exact (TwFin.tw_fin X.B f T).2.1 w h1.symm

theorem conj_mem {X : Stages} {f : Fr X.B.toPre} {T : TwDat X.B} {Wt : Set X.B.places.Pl} {xi : X.C.Tup → HChar X.B.host.E}
    (h : MuIsW X f T Wt xi) {w : X.B.places.Pl} (hw : w ∈ Wt) : X.B.places.conj w ∈ Wt := by
  rw [mem_iff h, X.W.muAt_conj]
  exact (mem_iff h w).1 hw

theorem Q_off {X : Stages} {f : Fr X.B.toPre} {T : TwDat X.B} {Wt : Set X.B.places.Pl} {xi : X.C.Tup → HChar X.B.host.E}
    (h : MuIsW X f T Wt xi) {w : X.B.places.Pl} (hw : w ∉ Wt) : T.Q w = ∅ :=
  Finset.eq_empty_of_forall_notMem fun v => ((T.psi_is w).ram v).1 (h.supp w hw ▸ isClsF_one.unr v)

theorem tup_cases {X : Stages} {f : Fr X.B.toPre} {T : TwDat X.B} {Wt : Set X.B.places.Pl} {xi : X.C.Tup → HChar X.B.host.E}
    (h : MuIsW X f T Wt xi) (μ : X.C.Tup) : μ = X.C.mu0 ∨ μ = X.C.muStar ∨ μ = X.C.muStar' ∨ ∃ w ∈ Wt, μ = X.W.muAt w := by
  have hμ : xi μ ∈ T.set f := h.range ▸ Set.mem_range_self μ
  rcases hμ with (e | e | e) | ⟨w, e⟩
  · exact .inl (h.inj (e.trans h.mu0.symm))
  · exact .inr (.inl (h.inj (e.trans h.star.symm)))
  · exact .inr (.inr (.inl (h.inj (e.trans h.star'.symm))))
  · by_cases hw : w ∈ Wt
    · exact .inr (.inr (.inr ⟨w, hw, (h.inj (e.symm.trans (h.tw w).symm)).trans (h.on w hw).symm⟩))
    · unfold TwDat.xiTw at e
      rw [h.supp w hw, mul_one] at e
      split_ifs at e
      · exact .inr (.inr (.inl (h.inj (e.symm.trans h.star'.symm))))
      · exact .inr (.inl (h.inj (e.symm.trans h.star.symm)))

theorem fval_untw {K : Ctx} {X : Stages} {f : Fr X.B.toPre} {T : TwDat X.B} (c : Core K X f T) (L : SizeData₂ X.toD7) (a : L.sc = K.s)
    (b : WtEq L K.a K.b) (d : Val K.C K.cD K.ch L) (w : X.B.places.Pl) (hw : X.W.muAt w = X.C.mu0) :
    ∀ j ∈ SizeData₂.lifts X.toD7, Fval L j w = 0 :=
  c.fval L a b d w fun h => (mem_iff c.mu w).1 h hw

theorem wj_pos {D : D7} (L : SizeData₂ D) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (τ : D.what₂.Tau) : 0 < wj D j τ := by
  have hxp : 0 < L.sc.x := by linarith [L.sc.one_lt_alt]
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hb' : 0 < L.sc.b' := div_pos (mul_pos hxp hb) (Real.exp_pos _)
  by_cases c1 : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces
  · exact hb.trans_le (L.win_thick j h1 h2 _ c1).1
  by_cases c2 : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
  · obtain ⟨t, ht, e⟩ := Finset.mem_image.mp c2
    have a1 := (L.win_top j h1 h2 τ ⟨t, ht⟩ e.symm).1
    have a2 := L.bT_ge ⟨t, ht⟩
    have a3 := div_pos hb' hxp
    linarith
  · refine lt_of_lt_of_le ?_ (L.win_thin j h1 h2 _ ⟨(D.eTau _).2, c2, c1⟩).1
    have hn : (0 : ℝ) < D.R.n := by unfold Ranks.n; positivity
    unfold Scale.w''
    positivity

theorem framD_neg {D : D7} (L : SizeData₂ D) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) : FRamD D j < 0 := by
  have hk : (1 : ℝ) < D.R.k := by have := D.R.m_add_three_le_k; exact_mod_cast (by omega : 1 < D.R.k)
  unfold FRamD
  refine mul_neg_of_neg_of_pos (by linarith) (Finset.sum_pos (fun t _ => lt_min (wj_pos L j h1 h2 _) (wj_pos L j h1 h2 _)) ?_)
  exact ⟨0, Finset.mem_univ _⟩

theorem mem_of_ramD {K : Ctx} {X : Stages} {f : Fr X.B.toPre} {T : TwDat X.B} (c : Core K X f T) (L : SizeData₂ X.toD7) (a : L.sc = K.s)
    (b : WtEq L K.a K.b) (d : Val K.C K.cD K.ch L) (w : X.B.places.Pl)
    (hg : X.B.places.resChar w ∉ L.gTypes) (hw : X.toD7.host.cls (X.B.places.resChar w) = PrimeClass.ramD) : w ∈ c.Wt := by
  by_contra hn
  have hm : 1 ≤ X.toD7.R.m := by have := X.toD7.R.two_le_m; omega
  have h := c.fval L a b d w hn 1 (Finset.mem_Icc.2 ⟨le_rfl, hm⟩)
  have e : Fval L 1 w = FRamD X.toD7 1 := FvalP_d L 1 hg hw
  exact (framD_neg L 1 le_rfl hm).ne (e.symm.trans h)

theorem ev_recOK : Ev fun K => ∀ (X : Stages) (f : Fr X.B.toPre) (T : TwDat X.B) (_ : Core K X f T), RecOK K.s K.C K.cD X.toD7 :=
  ev_imp TamePow.tame_of_pow fun _ hK X _ T c =>
    ⟨c.del, c.etaF, fun w hw j h1 h2 => by
        have a := c.row.untw w hw j h1 h2
        have b := c.row.untw (X.toD7.what₂.places.conj w) ((X.toD7.what₂.muAt_conj w).trans hw) j h1 h2
        unfold Rows.Data.Aj
        rw [hw, a.1, a.2, b.1]
        rfl,
      (TwFin.finite_pl X.B T.pl).subset fun w hw => c.mu.sub w ((mem_iff c.mu w).2 hw),
      (Full.dgam_pos_and_full X.toD7).1, (Full.dgam_pos_and_full X.toD7).2, hK X c.isOver c.chiT, c.col.mink, c.col.atT⟩

theorem ev_exists_sizeData : Ev fun K => ∀ (X : Stages) (f : Fr X.B.toPre) (T : TwDat X.B) (_ : Core K X f T),
    ∃ L : SizeData₂ X.toD7, L.sc = K.s ∧ WtEq L K.a K.b ∧ Val K.C K.cD K.ch L := by
  have h : Ev fun K => ∀ D : D7, Over D K.P K.Lv → RecOK K.s K.C K.cD D →
      ∃ L : SizeData₂ D, L.sc = K.s ∧ WtEq L K.a K.b ∧ Val K.C K.cD K.ch L := by
    refine ⟨1, one_pos, fun eps _ a1 _ a3 _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C b1 _ _ => ⟨0, fun cD hcD =>
      ⟨402, fun ch hch => ?_⟩⟩⟩⟩
    obtain ⟨x0, h⟩ := exists_sizeData_over eps cD ch C a1 a3 b1 hcD hch
    refine ⟨x0, ?_⟩
    rintro K rfl rfl rfl d4 d5 D hO hR
    exact (h K.s K.P K.q1 K.a K.b K.c K.Lv D d4 d5 K.ok K.Gam_eq hO hR).2.1
  refine ev_imp (ev_and h ev_recOK) fun K H X f T c => H.1 _ ?_ (H.2 X f T c)
  obtain ⟨sp, hT, hY, hA, hV, hz, h, -⟩ := c.isOver
  exact ⟨sp, hT, hY, hA, hV, hz, X, h, rfl⟩

theorem ev_ramD_mem : Ev fun K => ∀ (X : Stages) (f : Fr X.B.toPre) (T : TwDat X.B) (c : Core K X f T) (w : X.B.places.Pl),
    X.B.places.resChar w = X.B.host.d → w ∈ c.Wt :=
  ev_imp ev_exists_sizeData fun K H X f T c w hw => by
    obtain ⟨L, a, b, d⟩ := H X f T c
    have hd : X.B.host.cls X.B.host.d = PrimeClass.ramD := primeClass_d X.B.host.toHostRaw
    have hg : ∀ i, X.B.host.d ≠ X.B.host.g i := fun i e => by
      have h := X.B.toPre.level_split _ (X.B.host.g_level i)
      rw [← e, hd] at h
      exact absurd h (by decide)
    refine mem_of_ramD c L a b d w ?_ (by rw [hw]; exact hd)
    rw [hw]
    intro h
    rcases Finset.mem_insert.1 h with h | h
    · exact hg 0 h
    · exact hg 1 (Finset.mem_singleton.1 h)

theorem core_ext {K : Ctx} {X : Stages} {f : Fr X.B.toPre} {T : TwDat X.B} (c c' : Core K X f T) (h : c.O = c'.O) : c = c' := by
  have hx : c.xi = c'.xi := by
    funext μ
    have hm : c.xi μ ∈ T.set f := c.mu.range ▸ Set.mem_range_self μ
    rcases hm with (e | e | e) | ⟨w, e⟩
    · rw [c.mu.inj (e.trans c.mu.mu0.symm), c.mu.mu0, c'.mu.mu0]
    · rw [c.mu.inj (e.trans c.mu.star.symm), c.mu.star, c'.mu.star]
    · rw [c.mu.inj (e.trans c.mu.star'.symm), c.mu.star', c'.mu.star']
    · rw [c.mu.inj (e.symm.trans (c.mu.tw w).symm), c.mu.tw, c'.mu.tw]
  have hW : c.Wt = c'.Wt := Set.ext fun w => (mem_iff c.mu w).trans (mem_iff c'.mu w).symm
  cases c; cases c'
  cases h; cases hx; cases hW
  rfl

def someBase (P : Pre) : Base := (BaseExt.exists_base P ∅ ∅ ∅ (by simp) (by simp) (by simp)).choose

theorem someBase_pre (P : Pre) : (someBase P).toPre = P :=
  (BaseExt.exists_base P ∅ ∅ ∅ (by simp) (by simp) (by simp)).choose_spec.1

theorem ksCond_fixed : KsCond fun B _ => B.KsC = (someBase B.toPre).KsC := by
  refine ⟨ev_all fun K B₀ f₀ S₁ S₂ _ h₁ h₂ => ?_, fun B B' f f' e _ h => by rw [e.KsC_eq, e.1, h]⟩
  obtain ⟨B₁, e₁, k₁, l₁⟩ := Inh.exists_fixed (someBase B₀.toPre) (S₁ (someBase B₀.toPre).KsC) (h₁ _)
  obtain ⟨B, e, l₂⟩ := BaseEnl.exists_enl B₁ (S₂ (someBase B₀.toPre).KsC B₁.fixedCoefficientFieldInComplex) (h₂ _ _)
  have hk : B.KsC = (someBase B₀.toPre).KsC := e.KsC_eq.trans k₁
  have e' : B.toPre = B₀.toPre := (e.1.trans e₁).trans (someBase_pre _)
  refine ⟨B, e' ▸ f₀, e', by simp, by rw [hk, e'], ?_⟩
  rw [hk, Has₂, e.fixedCoefficientField_eq]
  exact ⟨l₁, l₂⟩

variable (hH : DC.HostExQ) (hLP : LevelPrime) (hSP : SmallPrimeOne) (h2b : StandardLattice.SiegelMassRatioCM)

include hH hLP hSP h2b in

theorem not_exTrue_false {KP : ∀ B : Base, Fr B.toPre → Prop} (hK : KsCond KP) : ¬ ExTrue KP fun _ _ _ _ _ => False := fun hE => by
  refine Inh.not_ev_false hH hLP hSP h2b ?_
  refine ev_imp (ev_and (ev_and (ev_preX_frame h2b) hK.ex) hE) ?_
  rintro K ⟨⟨hfr, hks⟩, S₁, P₁, A, S₂, a₁, a₂, hlg⟩
  obtain ⟨P, hP⟩ := Inh.exists_over K
  obtain ⟨B₀, rfl, -⟩ := BaseExt.exists_base P ∅ ∅ ∅ (by simp) (by simp) (by simp)
  obtain ⟨f₀⟩ := (hfr _ hP).2
  obtain ⟨B, f, hB, hf, hKP, hH₁, hH₂⟩ := hks B₀ f₀ (S₁ B₀.toPre f₀)
    (fun F F₀ => S₂ B₀.toPre f₀ F F₀ {1, f₀.del, f₀.del'}) hP (a₁ _ _) (fun F F₀ => a₂ _ _ F F₀ _)
  generalize B₀.toPre = P₀ at *
  subst hB
  obtain rfl := eq_of_heq hf
  have hs : (TwDat.untw B (P₁ B.toPre f B.KsC B.fixedCoefficientFieldInComplex)).set f = {1, f.del, f.del'} := by
    refine Set.union_eq_left.2 ?_
    rintro _ ⟨w, rfl⟩
    change (if _ then f.del' else f.del) * 1 ∈ _
    rw [mul_one]
    split_ifs
    · exact .inr (.inr rfl)
    · exact .inr (.inl rfl)
  obtain ⟨_, _, _, _, _, _, _, h⟩ := hlg B f (TwDat.untw B (P₁ B.toPre f B.KsC B.fixedCoefficientFieldInComplex)) hP
    ⟨hH₁, by rw [hs]; exact hH₂⟩ (Finset.Subset.refl _) (fun w v hv => absurd hv (Finset.notMem_empty _)) hKP
  exact h

include hH hLP hSP h2b in

theorem not_ksCond_false : ¬ KsCond fun _ _ => False := fun hK =>
  not_exTrue_false hH hLP hSP h2b hK (ev_all fun _ => ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun _ _ _ _ _ => ∅,
    by simp, by simp, fun _ _ _ _ _ _ _ h => h.elim⟩)

include hH hLP hSP h2b in

theorem not_exTrue_confined {KP : ∀ B : Base, Fr B.toPre → Prop} (hK : KsCond KP) {Q : Slot}
    (g : Ctx → ∀ P : Pre, Fr P → IntermediateField ℚ ℂ → IntermediateField ℚ ℂ → Finset ℕ)
    (hQ : ∀ K X f T c, Q K X f T c → ∀ w ∈ c.Wt, X.B.places.resChar w ∈ g K X.B.toPre f X.B.KsC X.B.fixedCoefficientFieldInComplex) : ¬ ExTrue KP Q := fun hE => by
  classical
  refine Inh.not_ev_false hH hLP hSP h2b ?_
  refine ev_imp (ev_and (ev_and (ev_preX_frame h2b) hK.ex) hE) ?_
  rintro K ⟨⟨hfr, hks⟩, S₁, P₁, A, S₂, a₁, a₂, hlg⟩
  obtain ⟨P, hP⟩ := Inh.exists_over K
  obtain ⟨B₀, rfl, -⟩ := BaseExt.exists_base P ∅ ∅ ∅ (by simp) (by simp) (by simp)
  obtain ⟨f₀⟩ := (hfr _ hP).2
  have hl : ∀ F F₀, ∃ l : ℕ, l.Prime ∧ l ∉ g K B₀.toPre f₀ F F₀ := fun F F₀ =>
    let ⟨l, h1, h2⟩ := Nat.infinite_setOf_prime.exists_notMem_finset (g K B₀.toPre f₀ F F₀); ⟨l, h1, h2⟩
  choose l hl hl' using hl
  choose Ξ hΞ using fun F F₀ => Inh.exists_family B₀.toPre f₀ (insert (l F F₀) (P₁ B₀.toPre f₀ F F₀)) (A B₀.toPre f₀ F F₀)
  obtain ⟨B, f, hB, hf, hKP, hH₁, hH₂⟩ := hks B₀ f₀ (S₁ B₀.toPre f₀)
    (fun F F₀ => S₂ B₀.toPre f₀ F F₀ (Ξ F F₀)) hP (a₁ _ _) (fun F F₀ => a₂ _ _ F F₀ _)
  obtain ⟨T, t1, t2, t3, t4⟩ := hΞ B.KsC B.fixedCoefficientFieldInComplex B hB
  clear hΞ hks
  generalize B₀.toPre = P₀ at *
  subst hB
  obtain rfl := eq_of_heq hf
  obtain ⟨C, W, V, S, N, G, c, h⟩ := hlg B f T hP ⟨hH₁, by rw [t4]; exact hH₂⟩ (t1 ▸ Finset.subset_insert _ _) t2 hKP
  obtain ⟨w, hw⟩ := GlobalTheory.Mem.PsiExist.exists_place_over B.LL (hl B.KsC B.fixedCoefficientFieldInComplex)
  have e : B.places.resChar w = l B.KsC B.fixedCoefficientFieldInComplex :=
    Examples₂.PlacesToy.prime_mem_unique w (Examples₂.PlacesToy.resCharW_prime _) (hl _ _) (Examples₂.PlacesToy.resCharW_mem w) hw
  have hw' : w ∈ c.Wt := by_contra fun hn => t3 w (e ▸ Finset.mem_insert_self _ _) (c.mu.supp w hn)
  exact hl' _ _ (e ▸ hQ _ _ _ _ c h w hw')

theorem exTrue_mono {KP : ∀ B : Base, Fr B.toPre → Prop} {Q Q' : Slot} (h : ∀ K X f T c, Q K X f T c → Q' K X f T c)
    (hE : ExTrue KP Q) : ExTrue KP Q' :=
  ev_imp hE fun _ hK => hK.imp fun _ _ _ _ H hp =>
    let ⟨C, W, V, S, N, G, c, q⟩ := H hp
    ⟨C, W, V, S, N, G, c, h _ _ _ _ _ q⟩

theorem export_anti {Q Q' : Slot} (h : ∀ K X f T c, Q' K X f T c → Q K X f T c) (hE : Export Q) : Export Q' :=
  ev_imp hE fun _ H X f T c q => H X f T c (h _ _ _ _ _ q)

theorem retwist_mono {Q Q' Q'' : Slot} (h : ∀ K X f T c, Q' K X f T c → Q'' K X f T c) (hR : Retwist Q Q') : Retwist Q Q'' :=
  ev_imp hR fun _ H X f T c q e A S₂ hS =>
    let ⟨B', f', T', a1, a2, a3, a4, a5, a6⟩ := H X f T c q e A S₂ hS
    ⟨B', f', T', a1, a2, a3, a4, a5, fun C W V S N G c' q' => (a6 C W V S N G c' q').imp_right (h _ _ _ _ _)⟩

theorem retwist_and {Q Q' : Slot} {p : Ctx → Prop} (hp : Ev p) (hR : Retwist Q Q') :
    Retwist Q fun K X f T c => Q' K X f T c ∧ Q K X f T c ∧ p K :=
  ev_imp (ev_and hp hR) fun _ H X f T c q e A S₂ hS =>
    let ⟨B', f', T', a1, a2, a3, a4, a5, a6⟩ := H.2 X f T c q e A S₂ hS
    ⟨B', f', T', a1, a2, a3, a4, a5, fun C W V S N G c' q' => (a6 C W V S N G c' q').imp_right fun h => ⟨h, q', H.1⟩⟩

theorem FromCore.elim {Q : Slot} {D : D7} {Y : Lay D} (h : FromCore Q D Y) :
    ∃ (K : Ctx) (X : Stages) (f : Fr X.B.toPre) (T : TwDat X.B) (c : Core K X f T) (e : D = X.toD7), Q K X f T c ∧
      layObj (e ▸ Y) = c.O := by
  obtain ⟨K, X, f, T, c, q, e⟩ := h
  obtain ⟨rfl, e2⟩ := Sigma.mk.inj_iff.1 e
  exact ⟨K, X, f, T, c, rfl, q, eq_of_heq e2⟩

open RowsModel in

def plainRows {B : Base} {C : Cols B} (W : RowsRest B C) (kb : ∀ j, Tau B.R → Fin (B.R.sigW j).1 → ℤ)
    (ks : ∀ j, Tau B.R → Fin (B.R.sigW j).2 → ℤ) : RowsRest B C :=
  { GaloisStage.adapt W with
    Mtilde := fun μ => DQ.Model.sat B.embLL (W.Mtilde μ)
    FT := {_x : Unit // 0 < W.Drows ∨ 0 < W.D0}
    instFT := inferInstance
    instFTd := inferInstance
    ft := fun i => ⟨(), .inl i.pos⟩
    ft0 := fun i => ⟨(), .inr i.pos⟩
    Bu := fun _ _ _ => 0
    Bu_linL := fun _ _ => ⟨by simp, by simp⟩
    Bu_linR := fun _ _ => ⟨by simp, by simp⟩
    Mj := fun _ => Euc 0
    instMj := fun _ => inferInstance
    instMji := fun _ => inferInstance
    instMjf := fun _ => inferInstance
    MjLat := fun _ => stdOLat _ _ 0
    kaBig := kb
    kaSmall := ks
    Mt := fun _ _ => Euc 0
    instMt := fun _ _ => inferInstance
    instMti := fun _ _ => inferInstance
    instMtf := fun _ _ => inferInstance
    MtLat := fun _ _ => stdOLat _ _ 0
    MtL := fun _ _ => Fin 0 → B.LL
    instMtL := fun _ _ => inferInstance
    instMtLm := fun _ _ => inferInstance
    jMt := fun _ _ => coordEmb B.embLL 0
    jMt_basis := fun _ _ b => coordEmb_basis B.embLL 0 b
    MtLat_sub := fun _ _ x hx => by
      obtain ⟨i, rfl⟩ := mem_stdOLat hx
      exact ⟨_, coordEmb_single _ _ i⟩
    eMt := fun _ _ => 0
    eMt_idem := fun _ _ => LinearMap.zero_comp _
    eMt_sa := fun _ _ => LinearMap.IsSymmetric.zero
    eMt_LL := fun _ _ _ => ⟨0, map_zero _⟩
    thetaP := fun _ _ => 0
    isot := fun _ _ => ⊥
    lamP := fun _ _ _ => 1
    Ij := fun _ _ _ => 0
    jw := fun _ _ _ => 0 }

def glue {L : Type} [Field L] [NumberField L] {V : Type} [AddCommGroup V] [Module (𝓞 L) V]
    (A : HeightOneSpectrum (𝓞 L) → Submodule (𝓞 L) V) : Submodule (𝓞 L) V where
  carrier := {x | ∀ w, ∃ d : 𝓞 L, d ∉ w.asIdeal ∧ d • x ∈ A w}
  add_mem' := fun {x y} hx hy w => by
    obtain ⟨d, h1, h2⟩ := hx w
    obtain ⟨e, h3, h4⟩ := hy w
    refine ⟨d * e, fun h => (w.isPrime.mem_or_mem h).elim h1 h3, ?_⟩
    rw [smul_add]
    exact add_mem (by rw [mul_comm, mul_smul]; exact Submodule.smul_mem _ _ h2) (by rw [mul_smul]; exact Submodule.smul_mem _ _ h4)
  zero_mem' := fun w => ⟨1, fun h => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by simp⟩
  smul_mem' := fun a x hx w => by
    obtain ⟨d, h1, h2⟩ := hx w
    exact ⟨d, h1, by rw [smul_comm]; exact Submodule.smul_mem _ _ h2⟩

def setRR {B : Base} {C : Cols B} {W : RowsRest B C} (V : DivStage B C W) (η : ℝ) : DivStage B C W :=
  let R : HLat B.LL := { V.div.RR with
    L := glue fun w => Submodule.span (𝓞 B.LL) {y | V.jEE y ∈ W.what₂.RRset (W.muAt w)} }
  { V with
    div := { V.div with
      RR := R
      etaF := η
      HH := sFrame V.div.Nu V.div.h + R.muMax
      HH_ge := le_rfl } }

theorem lidx_zero {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] [Subsingleton V] (p : Ideal R) [p.IsPrime]
    (A B : Submodule R V) : Formalism.HermitianLatticesTheory.lidx p A B = 0 := by
  rw [Subsingleton.elim A B]
  unfold Formalism.HermitianLatticesTheory.lidx
  exact sub_self _

set_option maxHeartbeats 1000000 in

theorem exists_rowLay_of (X : Stages) (η : ℝ) :
    ∃ (W : RowsRest X.B X.C) (V : DivStage X.B X.C W) (S : SStage X.B X.C W) (N : NStage X.B X.C W),
      W.muAt = X.W.muAt ∧ W.muTw = X.W.muTw ∧ W.Drows = X.W.Drows ∧ V.div.etaF = η ∧ DQ.MtStableAt (assemble X.B X.C W V S N X.G) ∧
      ∃ p0 Z, RowLay (assemble X.B X.C W V S N X.G) p0 Z := by
  obtain ⟨kb, ks, hk⟩ := DV.exists_blocks X.toD7
  let W := plainRows X.W kb ks
  obtain ⟨N, -⟩ := GaloisStage.exists_nStage_of_rows X.B X.C W X.N.toLocStage (fun _ _ => rfl) (fun _ _ _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl)
  let V₀ : DivStage X.B X.C W := { X.V with }
  let S : SStage X.B X.C W := { X.S with }
  let D := assemble X.B X.C W (setRR V₀ η) S N X.G
  obtain ⟨p0, hp, -⟩ := GlobalTheory.ProvRowSide.exists_p0Side D
  haveI i1 : ∀ j, Subsingleton (D.what₂.Mj j) := fun _ => inferInstanceAs (Subsingleton (RowsModel.Euc 0))
  haveI i2 : ∀ μ j, Subsingleton (D.what₂.MtL μ j) := fun _ _ => inferInstanceAs (Subsingleton (Fin 0 → X.B.LL))
  obtain ⟨Z, hZ⟩ := GlobalTheory.exists_provisionalDivX D fun j _ _ =>
    ⟨0, Module.Basis.empty _, fun _ _ i => i.elim0⟩
  refine ⟨W, setRR V₀ η, S, N, rfl, rfl, rfl, rfl,
    fun (μ : X.C.Tup) a y hy => DQ.Model.sat_stable X.B.embLL (X.W.Mtilde μ) a y hy, p0, Z, fun _ => Iff.rfl, hp, fun j _ _ τ => hk j τ,
    fun _ _ _ _ _ h => absurd rfl h, fun u φ x => ?_, fun π => π.2.imp (fun h => ⟨⟨0, h⟩, rfl⟩) (fun h => ⟨⟨0, h⟩, rfl⟩), fun _ _ _ _ _ => ⟨rfl, rfl⟩,
    ⟨fun μ j w _ _ => ?_, fun μ j w _ _ => (lidx_zero _ _ _).symm⟩, hZ⟩
  · have h0 : D.what₂.sec D.what₂.mu0 x = 0 := by
      have : D.what₂.sec D.what₂.mu0 x ∈ D.what₂.Qsp D.what₂.mu0 := Subtype.property _
      obtain ⟨y, hy⟩ := this.1
      exact hy.symm
    exact (h0 ▸ D.perCol_zero u φ).symm
  · haveI : Subsingleton (Z.MjH j).V := (Idx.jM_inj Z j).subsingleton
    exact (lidx_zero _ _ _).symm

theorem exists_rowLay : ∃ (D : D7) (p0 : BaseLevelRowSide D) (Z : DivX D), 0 < D.what₂.Drows ∧ RowLay D p0 Z := by
  obtain ⟨X, h, -⟩ := exists_stages
  obtain ⟨W, V, S, N, -, -, h3, -, -, p0, Z, hR⟩ := exists_rowLay_of X 0
  exact ⟨_, p0, Z, h.trans_eq h3.symm, hR⟩

theorem hasLetters_of_over (K : Ctx) (P : Pre) (hO : K.Over P) : StagesInhab.HasLetters P := by
  obtain ⟨sp, hT, hY, hA, hV, hz, rfl, -⟩ := hO
  have hx : 0 < K.s.x := by linarith [K.s.one_lt_alt]
  refine ⟨(Delv K.s K.cD : ℚ), K.c, ?_, K.ok.inj, fun u τ l h => ?_, K.ok.code⟩
  · exact_mod_cast Nat.ceil_pos.2 (Real.rpow_pos_of_pos hx _)
  · have a := (K.ok.hc u).1 τ ⟨l, by exact lt_of_le_of_lt (Nat.le_succ _) h⟩
    have b := (K.ok.hc u).1 τ ⟨l + 1, h⟩
    have h' : l + 1 < K.P.R.k - 1 := h
    have e : ((K.P.R.k - 2 - l : ℕ) : ℚ) = ((K.P.R.k - 2 - (l + 1) : ℕ) : ℚ) + 1 := by
      exact_mod_cast (by omega : K.P.R.k - 2 - l = K.P.R.k - 2 - (l + 1) + 1)
    refine (congrArg₂ (· - ·) a b).trans ?_
    simp only [e]
    ring

theorem exists_muIsW (B : Base) (hB : StagesInhab.HasLetters B.toPre) (f : Fr B.toPre) (T : TwDat B) (Wt : Set B.places.Pl)
    (hc : ∀ w, B.places.conj w ∈ Wt ↔ w ∈ Wt) (hs : ∀ w ∈ Wt, B.places.resChar w ∈ T.pl) (hu : ∀ w, w ∉ Wt → T.psi w = 1) :
    ∃ (C : Cols B) (W : _) (V : _) (S : _) (N : _) (G : _) (xi : C.Tup → HChar B.host.E), MuIsW ⟨B, C, W, V, S, N, G⟩ f T Wt xi := by
  classical
  obtain ⟨C, W₀, V₀, S₀, N₀, G, xi, h⟩ := Inh.exists_muIs B hB f T
  let W : RowsRest B C :=
    { W₀ with
      muAt := fun w => if w ∈ Wt then W₀.muTw w else C.mu0
      muAt_conj := fun w => by simp only [hc, W₀.muTw_conj]
      muAt_or := fun w => by split_ifs <;> simp }
  obtain ⟨N, -⟩ := GaloisStage.exists_nStage_adapt B _ W N₀.toLocStage
  exact ⟨C, GaloisStage.adapt W, { V₀ with }, { S₀ with }, N, G, xi, h.inj, h.range, h.mu0, h.star, h.star', h.tw,
    fun w hw => if_pos hw, fun w hw => if_neg hw, hs, hu⟩

theorem exists_muIsW_proper : ∃ (X : Stages) (f : Fr X.B.toPre) (T : TwDat X.B) (Wt : Set X.B.places.Pl) (xi : X.C.Tup → HChar X.B.host.E),
    MuIsW X f T Wt xi ∧ (∃ w ∈ Wt, T.psi w ≠ 1) ∧ ∃ w, w ∉ Wt ∧ X.B.places.resChar w ∈ T.pl := by
  classical
  obtain ⟨P, hP, ⟨Y⟩, -⟩ := StagesInhab.exists_pre_hasLetters
  obtain ⟨f⟩ := P.nonempty_hframe Y.e_even
  obtain ⟨B, rfl, -⟩ := BaseExt.exists_base P ∅ ∅ ∅ (by simp) (by simp) (by simp)
  obtain ⟨Ξ, hΞ⟩ := Inh.exists_family _ f {2} fun _ => ∅
  obtain ⟨T, t1, -, t3, -⟩ := hΞ B rfl
  let T' : TwDat B := { T with pl := {2, 3}, off := fun w hw => T.off w (by rw [t1]; intro h; exact hw (by simp_all)) }
  have pl : ∀ l : ℕ, l.Prime → ∃ w : B.places.Pl, B.places.resChar w = l := fun l hl =>
    let ⟨w, hw⟩ := GlobalTheory.Mem.PsiExist.exists_place_over B.LL hl
    ⟨w, Examples₂.PlacesToy.prime_mem_unique w (Examples₂.PlacesToy.resCharW_prime _) hl (Examples₂.PlacesToy.resCharW_mem w) hw⟩
  obtain ⟨C, W, V, S, N, G, xi, h⟩ := exists_muIsW B hP f T' {w | B.places.resChar w = 2}
    (fun w => by simp only [Set.mem_setOf_eq, TwFin.resChar_conj]) (fun w hw => by simp_all [T'])
    (fun w hw => (T.off w (by rw [t1]; simpa using hw)).1)
  obtain ⟨w2, h2⟩ := pl 2 Nat.prime_two
  obtain ⟨w3, h3⟩ := pl 3 Nat.prime_three
  exact ⟨⟨B, C, W, V, S, N, G⟩, f, T', _, xi, h, ⟨w2, h2, t3 w2 (by simp [h2])⟩, w3, by simp [h3], by simp [T', h3]⟩

theorem exists_stages_clauses (K : Ctx) (B : Base) (hO : K.Over B.toPre) (f : Fr B.toPre) (T : TwDat B) (Wt : Set B.places.Pl)
    (hc : ∀ w, B.places.conj w ∈ Wt ↔ w ∈ Wt) (hs : ∀ w ∈ Wt, B.places.resChar w ∈ T.pl) (hu : ∀ w, w ∉ Wt → T.psi w = 1) :
    ∃ (C : Cols B) (W : RowsRest B C) (V : DivStage B C W) (S : SStage B C W) (N : NStage B C W) (G : GJStage B C)
      (xi : C.Tup → HChar B.host.E), MuIsW ⟨B, C, W, V, S, N, G⟩ f T Wt xi ∧ DQ.MtStableAt (assemble B C W V S N G) ∧
      S.s.Del = (Delv K.s K.cD : ℚ) ∧ V.div.etaF = 6 * K.s.x ^ (-K.C.P.CF) ∧
      ∃ p0 Z, RowLay (assemble B C W V S N G) p0 Z := by
  obtain ⟨C, W₀, V₀, S₀, N₀, G, xi, h⟩ := exists_muIsW B (hasLetters_of_over K _ hO) f T Wt hc hs hu
  obtain ⟨W, V, S, N, h1, h2, -, h4, h5, h6⟩ := exists_rowLay_of ⟨B, C, W₀, V₀, S₀, N₀, G⟩ (6 * K.s.x ^ (-K.C.P.CF))
  refine ⟨C, W, V, S, N, G, xi, ⟨h.inj, h.range, h.mu0, h.star, h.star', fun w => ?_, fun w hw => ?_, fun w hw => ?_, hs, hu⟩, h5,
    del_of_over K ⟨B, C, W, V, S, N, G⟩ hO, h4, h6⟩
  · exact (congrArg xi (congrFun h2 w)).trans (h.tw w)
  · exact (congrFun h1 w).trans ((h.on w hw).trans (congrFun h2 w).symm)
  · exact (congrFun h1 w).trans (h.off w hw)

def setData {K : Ctx} {X : Stages} {f : Fr X.B.toPre} {T : TwDat X.B} (c : Core K X f T) (y : ThData X.toD7) : Core K X f T :=
  { c with O := { c.O with xd := y } }

theorem loc_Q {K : Ctx} {X : Stages} {f : Fr X.B.toPre} {T : TwDat X.B} (c : Core K X f T) (a : X.N.nd.Loc) :
    X.N.nd.Q a = T.Q (X.N.nd.w a) :=
  (c.nch_tie.Q_eq a).trans (c.nch_Q _ (by_contra fun h => X.N.nd.w_tw a (c.mu.off _ h))).1

end GlobalTheory.Mem.Top.V4.Model

end
