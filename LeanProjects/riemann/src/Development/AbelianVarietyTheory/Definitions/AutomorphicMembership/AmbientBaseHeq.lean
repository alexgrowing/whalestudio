import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PointPropertyEqSizeFree
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FamilyClassSevenDutiesAndStableLattices
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleIndexBoundAllPowers
import Formalism.LocalToGlobal.BesselHermitianTheta.MinfDensity

noncomputable section

namespace GlobalTheory.Mem.Top

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField IsDedekindDomain

structure ColLay (D : D7) (lev : LevelData D) (eX : ErrX D) : Prop where
  piG_lev : PiGLevel D lev eX
  piT_lev : PiTLevel D lev eX
  seen : SeenDef D eX
  tauOf : TauOfDef D eX
  one : ∀ u μ, (D.chTw u μ).DGam = (D.mem D.u₀).C.DGam
  mink : DGamChoice_at D
  atT : ∀ u (w : D.what₂.places.Pl), D.what₂.places.resChar w = (D.mem u).A.T → ∃ n : ℕ, n ≠ 0 ∧
    (∀ x ∈ DV.MramL D u, D.nuIn u (n • x) ∈ LT.Nlam D u w) ∧
    ∀ x, D.nuIn u x ∈ LT.Nlam D u w → InLoc (D.plEq w) (DV.MramL D u) (n • x)

def GatNum (s : Scale) (D : D7) : Prop :=
  ∀ u w hg, (D.gat u w hg).P.r = (if (D.what₂.places.resChar w : ℝ) < s.p0 D.R.k then G.rG s else 1) ∧
    (D.gat u w hg).e = ⌈(1 : ℝ) * (D.R.f : ℝ) * (D.R.k : ℝ) ^ 2 * Real.logb (D.what₂.places.resChar w) s.a⌉₊

structure GyLay (K : Ctx) (D : D7) (Gt : GatTies D) (cmp : LatCmp D) (Gy : G.LatInst D) : Prop where
  vram : cmp.VramDef Gy
  fills : FillsAll Gt Gy
  led : ∀ L : SizeData₂ D, L.sc = K.s → WtEq L K.a K.b → Val K.C K.cD K.ch L → ∀ X : G.Inst D L, CanonInst X → G.EpDef X K.C.cX.Ce →
    G.KapIDef X K.C.GK → (∀ w, G.ParametersFill X K.C.GK w) → G.LatTied Gt X Gy

def ExportAt (D : D7) (nch : NChoice D) (xd : ThData D) : Prop :=
  ∃ (N0 : D.ntw.Tw → ℕ) (S : ∀ (i : D.ntw.Tw) (j : ℕ) (b : Bool), Finset (D.nexp.Dat i j b)),
    (∀ i, D.ntw.NonzeroIndexPlace i → GlobalTheory.TwAll.goodTwistExistsAllCoprimePowers D.nexp (BlochKatoReduction.pin (BlochKatoReduction.bk0 D)) (twEOf xd) N0 i) ∧
    ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 →
      BlochKatoReduction.Gen.SetHyp (BlochKatoReduction.bk0 D) (nch.twI w) ∧ TwIn.Ok (⟨twEOf xd, N0, S⟩ : TwIn D) (nch.twI w)

section Lemmas

variable {D : D7}

theorem ColLay.dGamDef {lev : LevelData D} {eX : ErrX D} (h : ColLay D lev eX) : DGamDef D := fun u μ =>
  ⟨fun u' μ' i hi x => by
    rw [h.one u μ, ← h.one u' μ']
    exact (D.chTw u' μ').dvd_DGam i hi x, h.one u μ⟩

theorem ColLay.ofLay {s : Scale} {C : FC} {cD : ℝ} (Y : Lay D) (hR : RecOK s C cD D) : ColLay D Y.lev Y.errX :=
  ⟨Y.piG_lev, Y.piT_lev, Y.seen, Y.tauOf, fun u μ => (Y.dgam u μ).2, hR.mink, hR.atT⟩

theorem ColLay.iff_lay (Y : Lay D) : ColLay D Y.lev Y.errX ↔ DGamChoice_at D ∧
    ∀ u (w : D.what₂.places.Pl), D.what₂.places.resChar w = (D.mem u).A.T → ∃ n : ℕ, n ≠ 0 ∧
      (∀ x ∈ DV.MramL D u, D.nuIn u (n • x) ∈ LT.Nlam D u w) ∧
      ∀ x, D.nuIn u x ∈ LT.Nlam D u w → InLoc (D.plEq w) (DV.MramL D u) (n • x) :=
  ⟨fun h => ⟨h.mink, h.atT⟩, fun h => ⟨Y.piG_lev, Y.piT_lev, Y.seen, Y.tauOf, fun u μ => (Y.dgam u μ).2, h.1, h.2⟩⟩

theorem GyLay.ofLay {K : Ctx} (Y : Lay D) (hL : LedOK K.s K.C K.cD K.ch Y K.a K.b) : GyLay K D Y.gatT Y.cmp Y.Gy :=
  ⟨Y.vram, Y.fills_all, fun L a b c X d e g h => ((hL L a b c).2 X d e g h).1⟩

theorem GatNum.epTie {L : SizeData₂ D} {X : G.Inst D L} (h : GatNum L.sc D) (he : G.EpDef X 1) : EpTie X := fun u w hg =>
  (h u w hg).2.trans (he _).symm

theorem GatNum.ofTied {L : SizeData₂ D} {X : G.Inst D L} {Gt : GatTies D} {Gy : G.LatInst D} (hl : G.LatTied Gt X Gy)
    (ht : EpTie X) (he : G.EpDef X 1) : GatNum L.sc D := fun u w hg =>
  ⟨(hl u w hg).2.2.2.1, (ht u w hg).trans (he _)⟩

theorem GatNum.ofPt {C : FC} (hC : C.cX.Ce = 1) (p : Pt C) : GatNum p.L.sc p.D :=
  GatNum.ofTied p.ta.latTied p.xa.ex.ep_tie (hC ▸ p.xa.ex.ep_def)

theorem Ctx.Ce_eq_one (K : Ctx) : K.C.cX.Ce = 1 := by
  have := K.std.1
  unfold FC.Fixed at this
  tauto

theorem GatNum.ofLay {K : Ctx} (Y : Lay D) (hL : LedOK K.s K.C K.cD K.ch Y K.a K.b) {L : SizeData₂ D} (hs : L.sc = K.s)
    (hW : WtEq L K.a K.b) (hV : Val K.C K.cD K.ch L) {X : G.Inst D L} (hX : CanonInst X) (he : G.EpDef X K.C.cX.Ce)
    (hk : G.KapIDef X K.C.GK) (hf : ∀ w, G.ParametersFill X K.C.GK w) : GatNum K.s D :=
  have h := (hL L hs hW hV).2 X hX he hk hf
  hs ▸ GatNum.ofTied h.1 h.2.1 (K.Ce_eq_one ▸ he)

open Classical in

theorem ExportAt.exists_good {nch : NChoice D} {xd : ThData D} (h : ExportAt D nch xd)
    (hW : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → D.ntw.NonzeroIndexPlace (nch.twI w)) (A : D.ntw.Tw → Finset (PlE D.host)) :
    ∃ (N0 : D.ntw.Tw → ℕ) (S : ∀ (i : D.ntw.Tw) (j : ℕ) (b : Bool), Finset (D.nexp.Dat i j b))
      (Q : D.ntw.Tw → Finset (PlE D.host)) (k : D.ntw.Tw → ℕ) (ψ : ∀ i, D.ntw.RCG i (Q i) →* (D.ntw.Ok i (k i))ˣ),
      ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → TwIn.Ok (⟨twEOf xd, N0, S⟩ : TwIn D) (nch.twI w) ∧
        ∀ a : ℤ, IsCoprime a (D.ntw.l (nch.twI w) : ℤ) →
          IntegralHeckeForms.GoodTw D.nexp (BlochKatoReduction.bk0 D) (twEOf xd) N0 (nch.twI w) (twEps D (nch.twI w)) (S (nch.twI w)) (A (nch.twI w))
            (Q (nch.twI w)) (k (nch.twI w)) (ψ (nch.twI w) ^ a) := by
  obtain ⟨N0, S, hp, hs⟩ := h
  have key : ∀ i : D.ntw.Tw, ∃ (Q : Finset (PlE D.host)) (k : ℕ) (ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ),
      (D.ntw.NonzeroIndexPlace i ∧ BlochKatoReduction.Gen.SetHyp (BlochKatoReduction.bk0 D) i ∧ TwIn.Ok (⟨twEOf xd, N0, S⟩ : TwIn D) i) →
      ∀ a : ℤ, IsCoprime a (D.ntw.l i : ℤ) →
        IntegralHeckeForms.GoodTw D.nexp (BlochKatoReduction.bk0 D) (twEOf xd) N0 i (twEps D i) (S i) (A i) Q k (ψ ^ a) := by
    intro i
    by_cases hi : D.ntw.NonzeroIndexPlace i ∧ BlochKatoReduction.Gen.SetHyp (BlochKatoReduction.bk0 D) i ∧ TwIn.Ok (⟨twEOf xd, N0, S⟩ : TwIn D) i
    · obtain ⟨Q, k, ψ, hG⟩ := hp i hi.1 hi.2.1 _ (twEps_pos D i) hi.2.2.1 _ hi.2.2.2 (A i)
      exact ⟨Q, k, ψ, fun _ => hG⟩
    · exact ⟨∅, 0, 1, fun h => absurd h hi⟩
  choose Q k ψ hG using key
  exact ⟨N0, S, Q, k, ψ, fun w hw => ⟨(hs w hw).2, hG _ ⟨hW w hw, hs w hw⟩⟩⟩

theorem ExportAt.congr {nch nch' : NChoice D} {xd : ThData D} (e : nch'.twI = nch.twI) (h : ExportAt D nch xd) :
    ExportAt D nch' xd := by
  unfold ExportAt at h ⊢
  rw [e]
  exact h

example (nch : NChoice D) (xd : ThData D) (h1 : ∀ i, ¬ D.ntw.NonzeroIndexPlace i) (h2 : ∀ w, D.what₂.muAt w = D.what₂.mu0) : ExportAt D nch xd :=
  ⟨fun _ => 0, fun _ _ _ => ∅, fun i hi => absurd hi (h1 i), fun w hw => absurd (h2 w) hw⟩

example {s : Scale} (h : GatNum s D) (u u') (w w') (hg hg') (e : D.what₂.places.resChar w' = D.what₂.places.resChar w)
    (hp : s.p0 D.R.k ≤ (D.what₂.places.resChar w : ℝ)) :
    (D.gat u w hg).P.r = 1 ∧ (D.gat u' w' hg').e = (D.gat u w hg).e :=
  ⟨(h u w hg).1.trans (if_neg (not_lt.2 hp)), by rw [(h u w hg).2, (h u' w' hg').2, e]⟩

example (lev : LevelData D) (eX : ErrX D) (u μ u' μ') (h : (D.chTw u μ).DGam ≠ (D.chTw u' μ').DGam) : ¬ ColLay D lev eX :=
  fun H => h ((H.one u μ).trans (H.one u' μ').symm)

end Lemmas

structure Core (K : Ctx) (X : Stages) (f : Fr X.B.toPre) (T : TwDat X.B) : Type 1 where
  isOver : K.Over X.B.toPre
  xi : X.C.Tup → HChar X.B.host.E
  mu : MuIs X f T xi
  forced : ∀ p : ℕ, p.Prime → ((∃ i, p = X.B.host.g i) ∨ p = X.B.host.d ∨ (p : ℝ) ≤ K.s.X'' X.B.R.n) → p ∈ T.pl
  O : Obj2 X.toD7
  col : ColLay X.toD7 O.lev O.errX
  gatNum : GatNum K.s X.toD7
  gy : GyLay K X.toD7 O.gatT O.cmp O.Gy
  r : RowT X.toD7 (Fr.at X f) xi
  p0_eq : O.p0 = r.p0
  X_eq : O.X = r.X
  amb_eq : O.amb = r.amb
  ambientBase_heq : HEq O.amb0 r.amb0
  mtStable : DQ.MtStableAt X.toD7
  th_io : O.th.TieIo
  gauge_def : letI := X.toD7.host.cmStar; O.gauge.IsGauge
  real : Formalism.L2.Theta.RealTied X.toD7
  dsig_eq : ∀ τ, X.S.dsig τ = Vol.trueDsig X.B.R (X.B.hc τ)
  del : X.S.s.Del = (Delv K.s K.cD : ℚ)
  etaF : X.V.div.etaF = 6 * K.s.x ^ (-K.C.P.CF)
  chiT : ∀ (k : Fin 2) (v : X.N.nd.PlG k), ∃ w : (ZMod (X.B.host.g k))ˣ, orderOf w = X.B.host.g k - 1 ∧
    ∀ j : Fin X.B.R.m, X.N.nd.chiT k v j = w ^ (2 * (j.1 + 1))
  nch_tie : NChTie X.toD7 O.nch
  nch_Q : ∀ w, X.B.places.resChar w ∈ T.pl → O.nch.Q w = T.Q w ∧ O.nch.k' w = T.k w

end GlobalTheory.Mem.Top

end
