import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SameSetup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsClassSystem
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSameData
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwInputs.Move
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwInputs.Move

variable {D D' : D7}

scoped macro "set_cases " h1:ident h2:ident N:ident N':ident X:ident X':ident : tactic =>
  `(tactic| (
    obtain ⟨-, -, -, nOm, ninstOm, nalgOm, -, nPlG⟩ := $h1
    obtain ⟨-, xTw, -, fixedFieldTransport_baseIntegerRing_heq, fixedFieldTransport_baseIntegerCommRing_heq, -, -, xO, xcrO, xalgO, xOk, xcrOk, xalgOk, -, xpD, -, -, -, -, -, -, fixedFieldTransport_initialPlaceSet_heq, -⟩ := $h2
    cases $N:ident; cases $N':ident
    dsimp only at nOm ninstOm nalgOm nPlG
    subst nOm; subst ninstOm; subst nalgOm; subst nPlG
    cases $X:ident; cases $X':ident
    dsimp only at xTw fixedFieldTransport_baseIntegerRing_heq fixedFieldTransport_baseIntegerCommRing_heq xO xcrO xalgO xOk xcrOk xalgOk xpD fixedFieldTransport_initialPlaceSet_heq
    subst xTw; subst fixedFieldTransport_baseIntegerRing_heq; subst fixedFieldTransport_baseIntegerCommRing_heq; subst xO; subst xcrO; subst xalgO; subst xOk; subst xcrOk; subst xalgOk; subst xpD
    subst fixedFieldTransport_initialPlaceSet_heq))

theorem exists_setupRel (h : SameGeo D D') {N : NData D.R D.host D.what₂} {N' : NData D'.R D'.host D'.what₂}
    {X : NTw D.R D.host D.what₂ D.LL0 N} {X' : NTw D'.R D'.host D'.what₂ D'.LL0 N'}
    (h1 : GlobalTheory.TwistChoice.SameGalois N N') (h2 : GlobalTheory.TwistChoice.TwistDataAgreeAcrossCoefficients X X') (ρ : Setup X) :
    ∃ ρ' : Setup X', SetupRel ρ ρ' := by
  geo_cases h D D'
  set_cases h1 h2 N N' X X'
  obtain ⟨rc, ch, bad, e, ek, B, om, Cl, rep, β, eG⟩ := ρ
  rename_i fin
  refine ⟨@Setup.mk _ _ _ ⟨rc.κ, rc.art⟩ ch bad e ek
    (fun i j b => ⟨(B i j b).hr, ⟨(B i j b).F.ψ, (B i j b).F.θ, (B i j b).F.sT, (B i j b).F.BS, (B i j b).F.BT, (B i j b).F.ΛS,
      (B i j b).F.ΛT, (B i j b).F.βS, (B i j b).F.βT, (B i j b).F.f₀⟩, ⟨(B i j b).G.Pg, (B i j b).G.P, (B i j b).G.mu⟩,
      ⟨(B i j b).de.Q, (B i j b).de.chi, (B i j b).de.res⟩,
      ⟨(B i j b).w.p, (B i j b).w.q, (B i j b).w.ap, (B i j b).w.am, (B i j b).w.c, (B i j b).w.lam⟩, (B i j b).mu0, (B i j b).eta⟩)
    om (fun i j b t => Cl i j b ⟨t.Q, t.chi, t.res⟩) (fun i j b t => fin i j b ⟨t.Q, t.chi, t.res⟩)
    (fun i j b t => rep i j b ⟨t.Q, t.chi, t.res⟩) β eG,
    ⟨.rfl, .rfl⟩, .rfl, .rfl, .rfl, .rfl, ?_, .rfl, ?_, ?_, .rfl, ?_⟩
  · intro i i' hi j j' hj b
    cases hi; cases Fin.ext hj
    exact ⟨⟨.rfl, .rfl, .rfl, .rfl, .rfl, .rfl, .rfl, .rfl, .rfl, .rfl⟩, ⟨.rfl, .rfl, .rfl⟩, ⟨.rfl, .rfl, .rfl⟩,
      ⟨.rfl, .rfl, .rfl, .rfl, .rfl, .rfl⟩, .rfl, .rfl⟩
  · rintro i i' hi j j' hj b ⟨_, _, _⟩ ⟨_, _, _⟩ ⟨r1, r2, r3⟩
    cases hi; cases Fin.ext hj; cases r1; cases r2; cases r3
    rfl
  · rintro i i' hi j j' hj b ⟨_, _, _⟩ ⟨_, _, _⟩ ⟨r1, r2, r3⟩
    cases hi; cases Fin.ext hj; cases r1; cases r2; cases r3
    exact HEq.rfl
  · intro i i' hi j j' hj b
    cases hi; cases Fin.ext hj
    exact HEq.rfl

theorem RecipRel.good (h : SameGeo D D') {Ω Ω' : Type} [i1 : Field Ω] [i2 : Algebra D.host.E Ω] [i1' : Field Ω']
    [i2' : Algebra D'.host.E Ω'] (hΩ : Ω = Ω') (h1 : HEq i1 i1') (h2 : HEq i2 i2') {a : Recip D Ω} {a' : Recip D' Ω'}
    (r : RecipRel a a') (g : a.Good) : a'.Good := by
  geo_cases h D D'
  subst hΩ; subst h1; subst h2
  obtain ⟨κ, art⟩ := a
  obtain ⟨κ', art'⟩ := a'
  obtain ⟨r1, r2⟩ := r
  cases r1; cases r2
  exact ⟨g.1, g.2, g.3, g.4⟩

theorem SetupRel.good_of (h : SameGeo D D') {N : NData D.R D.host D.what₂} {N' : NData D'.R D'.host D'.what₂}
    {X : NTw D.R D.host D.what₂ D.LL0 N} {X' : NTw D'.R D'.host D'.what₂ D'.LL0 N'}
    (h1 : GlobalTheory.TwistChoice.SameGalois N N') (h2 : GlobalTheory.TwistChoice.TwistDataAgreeAcrossCoefficients X X') (hδ : HEq X.delta X'.delta)
    (he : ∀ i i', HEq i i' → ∀ b x', ∃ x, HEq (sideEmb X i b x) (sideEmb X' i' b x') ∧ embLL0 D x = embLL0 D' x')
    {ρ : Setup X} {ρ' : Setup X'} (r : SetupRel ρ ρ') (g : ρ.Good) : ρ'.Good := by
  have grc := r.rc.good h (eq_of_heq h1.Om) h1.instOm h1.algOm g.rc
  have h0 := h
  geo_cases h D D'
  set_cases h1 h2 N N' X X'
  dsimp only at hδ
  subst hδ
  obtain ⟨⟨κ, art⟩, ch, bad, e, ek, B, om, Cl, rep, β, eG⟩ := ρ
  obtain ⟨⟨κ', art'⟩, ch', bad', e', ek', B', om', Cl', rep', β', eG'⟩ := ρ'
  obtain ⟨⟨r1, r2⟩, r3, r4, r5, r6, r7, r8, r9, r10, -, -⟩ := r
  dsimp only at r1 r2 r3 r4 r5 r6 r8
  subst r1 r2 r3 r4 r5 r6 r8
  refine ⟨grc, fun i => ⟨(g.ch i).1, (g.ch i).2⟩, g.bad_ne, g.goodSetup_bad_mem_badPlaces, g.goodSetup_badPlaces_conj, g.goodSetup_placesOverTwo_subset, g.goodSetup_count_eq_zero_off_badPlaces, fun i b x' => ?_, g.ek_e,
    fun i j b => (r7 i i .rfl j j rfl b).good h0 .rfl .rfl (g.base i j b),
    fun i j b => ((r7 i i .rfl j j rfl b).isBaseFrame h0 .rfl .rfl).1 (g.latS i j b),
    fun i j b => ((r7 i i .rfl j j rfl b).isBaseFrame h0 .rfl .rfl).2.1 (g.latT i j b),
    fun i j b => ((r7 i i .rfl j j rfl b).isBaseFrame h0 .rfl .rfl).2.2 (g.Pg i j b), fun i j b => ?_, fun i j b t ht => ?_,
    fun i j b t ht ha => ?_⟩
  · obtain ⟨x, h3, h4⟩ := he i i .rfl b x'
    exact (congrArg (e i b) (eq_of_heq h3).symm).trans ((g.e_LL0 i b x).trans h4)
  · have t := (r7 i i .rfl j j rfl b).de
    rw [g.delta i j b] at t
    exact TwistRel.eq ⟨t.1.symm, t.2.symm, t.3.symm⟩
  · exact (r7 i i .rfl j j rfl b).isWeil h0 .rfl .rfl .rfl .rfl
      (g.weil i j b ⟨t.Q, t.chi, t.res⟩ (TwistRel.good h0.symm ⟨.rfl, .rfl, .rfl⟩ ht))
  · exact (r7 i i .rfl j j rfl b).isClassSystem h0 .rfl .rfl (t := ⟨t.Q, t.chi, t.res⟩) ⟨.rfl, .rfl, .rfl⟩
      (r9 i i .rfl j j rfl b _ t ⟨.rfl, .rfl, .rfl⟩) (r10 i i .rfl j j rfl b _ t ⟨.rfl, .rfl, .rfl⟩)
      (g.classes i j b ⟨t.Q, t.chi, t.res⟩ (TwistRel.good h0.symm ⟨.rfl, .rfl, .rfl⟩ ht)
        ((r7 i i .rfl j j rfl b).adm h0 .rfl .rfl .rfl ha))

theorem val_move {T T' : Type} {n n' : ℕ} (hT : T = T') (hn : n = n') {a : T → GL (Fin n) ℂ} {a' : T' → GL (Fin n') ℂ}
    {c : T → Matrix (Fin n) (Fin n) ℂ} {c' : T' → Matrix (Fin n') (Fin n') ℂ} (ha : HEq a a') (hc : HEq c c')
    (g : ∀ τ, (a τ).val = c τ) (τ : T') : (a' τ).val = c' τ := by
  subst hT hn ha hc
  exact g τ

theorem mem_move {R R' : Ranks} {H : Host R} {H' : Host R'} (hR : R = R') (hH : HEq H H') {T T' : Type} (hT : T = T')
    {p : T → Finset (Pl H.E)} {p' : T' → Finset (Pl H'.E)} {c : T → Set (Pl H.E)} {c' : T' → Set (Pl H'.E)} (hp : HEq p p')
    (hc : HEq c c') {i : T} {i' : T'} (hi : HEq i i') {P : Pl H.E} {P' : Pl H'.E} (hP : HEq P P') (g : P ∈ p i → P ∈ c i) :
    P' ∈ p' i' → P' ∈ c' i' := by
  subst hR; subst hH; subst hT hp hc hi hP
  exact g

theorem grp_move {R R' : Ranks} {H : Host R} {H' : Host R'} {L L' : Fin 2 → Type} (hR : R = R') (hH : HEq H H') (hL : L = L')
    {r r' : ℕ} (e : r = R.r) (e' : r' = R'.r) {A B : Finset (Pl H.E)} {A' B' : Finset (Pl H'.E)} (hA : HEq A A') (hB : HEq B B')
    {u : (∀ kv : (Σ k : Fin 2, L k), GL (Fin R.r) (ZMod (H.g kv.1))) ≃* G0 A r}
    {u' : (∀ kv : (Σ k : Fin 2, L' k), GL (Fin R'.r) (ZMod (H'.g kv.1))) ≃* G0 A' r'} (hu : HEq u u')
    {c : G0 B R.r ≃* ∀ kv : (Σ k : Fin 2, L k), GL (Fin R.r) (ZMod (H.g kv.1))}
    {c' : G0 B' R'.r ≃* ∀ kv : (Σ k : Fin 2, L' k), GL (Fin R'.r) (ZMod (H'.g kv.1))} (hc : HEq c c')
    (g : ∀ x P (h : P ∈ A) (h' : P ∈ B) (a b : Fin r), (u x ⟨P, h⟩).val a b = (c.symm x ⟨P, h'⟩).val (Fin.cast e a) (Fin.cast e b)) :
    ∀ x P (h : P ∈ A') (h' : P ∈ B') (a b : Fin r'),
      (u' x ⟨P, h⟩).val a b = (c'.symm x ⟨P, h'⟩).val (Fin.cast e' a) (Fin.cast e' b) := by
  subst hR; subst hH; subst hL e e' hA hB hu hc
  exact g

theorem heq_app {T T' A : Type} (hT : T = T') {f : T → A} {f' : T' → A} (hf : HEq f f') {i : T} {i' : T'} (hi : HEq i i') :
    f i = f' i' := by
  subst hT hf hi
  rfl

variable {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0}

theorem SetupRel.good (h : CopyTw D D' ι e) {ρ : Setup D.ntw} {ρ' : Setup D'.ntw} (r : SetupRel ρ ρ') (g : ρ.Good) : ρ'.Good :=
  r.good_of h.sameGeo h.gal h.set h.delta (fun _ _ hi b x => ⟨e x, h.sideEmb_heq hi b x, h.embLL0_eq x⟩) g

theorem SetupRel.realPin (h : CopyTw D D' ι e) {X : RealSide D} {X' : RealSide D'} (m : RealMove X X' ι) {ρ : Setup D.ntw}
    {ρ' : Setup D'.ntw} (r : SetupRel ρ ρ') (p : RealPin X.R X.cG ρ) : RealPin X'.R X'.cG ρ' := by
  have G := h.sameGeo
  have back : ∀ (i' : D'.ntw.Tw) (j' : Fin D'.R.m), ∃ i : D.ntw.Tw, ∃ j : Fin D.R.m, HEq i i' ∧ (j : ℕ) = j' :=
    fun i' j' => ⟨cast h.Tw_eq.symm i', Fin.cast (congrArg Ranks.m h.gal.R).symm j', cast_heq _ _, rfl⟩
  have chain : ∀ {A A' : Type} {a c : A} {a' c' : A'}, HEq a a' → a = c → HEq c c' → a' = c' :=
    fun h1 h2 h3 => eq_of_heq (h1.symm.trans ((heq_of_eq h2).trans h3))
  constructor
  case deltaPl =>
    intro i' t' P' h1 h2
    obtain ⟨t, P, h3, h4⟩ := m.Q i' t' P' h1 h2
    exact mem_move h.gal.R h.gal.host h.Tw_eq h.set.pD r.ch (cast_heq h.Tw_eq.symm i') h4 (p.deltaPl _ t P h3) h2
  all_goals
    intro i' j' b
    obtain ⟨i, j, hi, hj⟩ := back i' j'
    have q := r.B i i' hi j j' hj b
    obtain ⟨hV, hW, rV, rW, hp, hm⟩ := G.spaces hj
  · exact chain q.F.ψ (p.psi i j b) m.ψ
  · exact chain q.F.θ (p.inf i j b) m.θ
  · exact chain q.F.sT (p.cartT i j b) ((m.MW j j' hj).cart_onb G hW).1
  · exact val_move h.Tau rV q.F.BS (m.BV j j' hj) (p.onbS i j b)
  · exact chain q.F.BT (p.onbT i j b) ((m.MW j j' hj).cart_onb G hW).2
  · exact chain q.F.ΛS (p.latS i j b) (m.ΛV j j' hj)
  · exact chain q.F.ΛT (p.latT i j b) (m.ΛW j j' hj)
  · exact chain q.F.βS (p.frS i j b) (m.βV j j' hj)
  · exact chain q.F.βT (p.frT i j b) (m.βW j j' hj)
  · exact chain q.F.f₀ (p.vac i j b) (m.vacP j j' hj)
  · exact chain q.G.Pg (p.Pg i j b) m.Pg
  · exact grp_move h.gal.R h.gal.host (eq_of_heq h.gal.PlG) (FWT.rank_Wc j) (FWT.rank_Wc j') q.G.Pg m.Pg
      (r.eG i i' hi j j' hj b) m.cG (p.grp i j b)
  · exact chain q.mu0 (p.mu0 i j b) (hj ▸ m.mu0 j)
  · exact chain q.eta (p.eta i j b) m.eta
  · exact G.chrEq q.de.chi (heq_app h.Tw_eq h.set.l hi ▸ m.delAt _) (p.delta i j b)
  · exact congrFun (chain q.w.ap (funext (p.ap i j b)) hp)
  · exact congrFun (chain q.w.am (funext (p.am i j b)) hm)

theorem BaseRel.sameBase {S T : HSp D} {S' T' : HSp D'} {B : Base S T} {B' : Base S' T'} (r : BaseRel B B') : SameBase B B' :=
  ⟨r.F.1, r.F.2, r.F.3, r.F.4, r.F.5, r.F.6, r.F.7, r.F.8, r.F.9, r.F.10, r.G.1, r.G.2, r.G.3, ⟨r.de.1, r.de.2, r.de.3⟩,
    r.w.1, r.w.2, r.w.3, r.w.4, r.w.5, r.w.6, r.mu0, r.eta⟩

theorem SameBase.baseRel {S T : HSp D} {S' T' : HSp D'} {B : Base S T} {B' : Base S' T'} (r : SameBase B B') : BaseRel B B' :=
  ⟨⟨r.ψ, r.θ, r.sT, r.BS, r.BT, r.ΛS, r.ΛT, r.βS, r.βT, r.f₀⟩, ⟨r.Pg, r.P, r.mu⟩, ⟨r.de.1, r.de.2, r.de.3⟩,
    ⟨r.p, r.q, r.ap, r.am, r.c, r.lam⟩, r.mu0, r.eta⟩

theorem setupRel_iff_sameData {ρ : Setup D.ntw} {ρ' : Setup D'.ntw} : SetupRel ρ ρ' ↔ SameData ρ ρ' :=
  ⟨fun r => ⟨r.rc.1, r.rc.2, r.ch, r.bad, r.e, r.ek, fun i i' hi j j' hj b => (r.B i i' hi j j' hj b).sameBase, r.om,
      fun i i' hi j j' hj b t t' ht => ⟨r.Cl i i' hi j j' hj b t t' ⟨ht.1, ht.2, ht.3⟩, r.rep i i' hi j j' hj b t t' ⟨ht.1, ht.2, ht.3⟩⟩,
      r.β, r.eG⟩,
    fun r => ⟨⟨r.κ, r.art⟩, r.ch, r.bad, r.e, r.ek, fun i i' hi j j' hj b => (r.B i i' hi j j' hj b).baseRel, r.om,
      fun i i' hi j j' hj b t t' ht => (r.Cl i i' hi j j' hj b t t' ⟨ht.1, ht.2, ht.3⟩).1,
      fun i i' hi j j' hj b t t' ht => (r.Cl i i' hi j j' hj b t t' ⟨ht.1, ht.2, ht.3⟩).2, r.β, r.eG⟩⟩

theorem setup_move_data : ∀ {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0} (h : CopyTw D D' ι e) {X : RealSide D} {X' : RealSide D'} (m : RealMove X X' ι) (ρ : Setup D.ntw), ρ.Good → RealPin X.R X.cG ρ →
    ∃ ρ' : Setup D'.ntw, SameData ρ ρ' ∧ ρ'.Good ∧ RealPin X'.R X'.cG ρ' := by
  intro D D' ι e h X X' m ρ g p
  obtain ⟨ρ', r⟩ := exists_setupRel h.sameGeo h.gal h.set ρ
  exact ⟨ρ', setupRel_iff_sameData.1 r, r.good h g, r.realPin h m p⟩

end GlobalTheory.TwInputs.Move

end
