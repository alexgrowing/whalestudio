import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RationalRootsDef
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FamilyClassSevenDutiesAndStableLattices
import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth
import Development.AutomorphicArithmetic.PrimeDiscriminants.Scales

noncomputable section

namespace GlobalTheory.Fc

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top

def EvGd (p : Ctx → Prop) : Prop :=
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ eps C8 C5 c6 Cb : ℝ, 0 < eps → eps ≤ ε0 → eps < 1 / 52 → 1 ≤ C8 → ∃ K0 : TransportedAlt,
    ∀ C : FC, Std C → C.P.Cpde = C8 → C.Large K0 C.P.CF → ∃ c1 : ℝ, ∀ cD ≥ c1, ∃ c2 : ℝ, ∀ ch ≥ c2, ∃ x0 : ℝ,
      ∀ K : Ctx, K.C = C → K.cD = cD → K.ch = ch → K.s.eps = eps → x0 ≤ K.s.x →
        ChGood K.s K.C C5 c6 Cb K.cD K.ch K.P K.a K.b K.c → p K

theorem evGd_of_ev {p : Ctx → Prop} (hp : Ev p) : EvGd p := by
  obtain ⟨a, ha, hp⟩ := hp
  refine ⟨a, ha, fun e C8 _ _ _ he hle h52 h8 => ?_⟩
  obtain ⟨K, hK⟩ := hp e C8 he hle h52 h8
  refine ⟨K, fun C hC hC8 hL => ?_⟩
  obtain ⟨a1, ha1⟩ := hK C hC hC8 hL
  refine ⟨a1, fun cD hcD => ?_⟩
  obtain ⟨a2, ha2⟩ := ha1 cD hcD
  refine ⟨a2, fun ch hch => ?_⟩
  obtain ⟨a3, ha3⟩ := ha2 ch hch
  exact ⟨a3, fun X h1 h2 h3 h4 hx _ => ha3 X h1 h2 h3 h4 hx⟩

theorem large_of_sup {C : FC} {K K' : TransportedAlt} {CH : ℝ} (h : C.Large (K.sup K') CH) : C.Large K CH ∧ C.Large K' CH :=
  ⟨⟨fun c hc => (le_max_left _ _).trans (h.1 c hc), trivial, fun c hc => (le_max_left _ _).trans (h.2.2.1 c hc),
      fun c hc => (le_max_left _ _).trans (h.2.2.2 c hc)⟩,
    ⟨fun c hc => (le_max_right _ _).trans (h.1 c hc), trivial, fun c hc => (le_max_right _ _).trans (h.2.2.1 c hc),
      fun c hc => (le_max_right _ _).trans (h.2.2.2 c hc)⟩⟩

theorem ev_and {p q : Ctx → Prop} (hp : EvGd p) (hq : EvGd q) : EvGd fun K => p K ∧ q K := by
  obtain ⟨a, ha, hp⟩ := hp
  obtain ⟨b, hb, hq⟩ := hq
  refine ⟨min a b, lt_min ha hb, fun e C8 C5 c6 Cb he hle h52 h8 => ?_⟩
  obtain ⟨K, hK⟩ := hp e C8 C5 c6 Cb he (hle.trans (min_le_left _ _)) h52 h8
  obtain ⟨K', hK'⟩ := hq e C8 C5 c6 Cb he (hle.trans (min_le_right _ _)) h52 h8
  refine ⟨K.sup K', fun C hC hC8 hL => ?_⟩
  obtain ⟨a1, ha1⟩ := hK C hC hC8 (large_of_sup hL).1
  obtain ⟨b1, hb1⟩ := hK' C hC hC8 (large_of_sup hL).2
  refine ⟨max a1 b1, fun cD hcD => ?_⟩
  obtain ⟨a2, ha2⟩ := ha1 cD (le_trans (le_max_left _ _) hcD)
  obtain ⟨b2, hb2⟩ := hb1 cD (le_trans (le_max_right _ _) hcD)
  refine ⟨max a2 b2, fun ch hch => ?_⟩
  obtain ⟨a3, ha3⟩ := ha2 ch (le_trans (le_max_left _ _) hch)
  obtain ⟨b3, hb3⟩ := hb2 ch (le_trans (le_max_right _ _) hch)
  exact ⟨max a3 b3, fun X h1 h2 h3 h4 hx hg =>
    ⟨ha3 X h1 h2 h3 h4 (le_trans (le_max_left _ _) hx) hg, hb3 X h1 h2 h3 h4 (le_trans (le_max_right _ _) hx) hg⟩⟩

theorem ev_mono {p q : Ctx → Prop} (h : ∀ K, p K → q K) (hp : EvGd p) : EvGd q := by
  obtain ⟨a, ha, hp⟩ := hp
  refine ⟨a, ha, fun e C8 C5 c6 Cb he hle h52 h8 => ?_⟩
  obtain ⟨K, hK⟩ := hp e C8 C5 c6 Cb he hle h52 h8
  refine ⟨K, fun C hC hC8 hL => ?_⟩
  obtain ⟨a1, ha1⟩ := hK C hC hC8 hL
  refine ⟨a1, fun cD hcD => ?_⟩
  obtain ⟨a2, ha2⟩ := ha1 cD hcD
  refine ⟨a2, fun ch hch => ?_⟩
  obtain ⟨a3, ha3⟩ := ha2 ch hch
  exact ⟨a3, fun X h1 h2 h3 h4 hx hg => h X (ha3 X h1 h2 h3 h4 hx hg)⟩

structure BPt (K : Ctx) : Type 1 where
  X : Stages
  f : Fr X.B.toPre
  T : TwDat X.B
  c : V4.Core K X f T
  Y : Lay X.toD7
  hY : layObj Y = c.O
  p : LedPart K.C Y
  sc : p.L.sc = K.s
  wt : WtEq p.L K.a K.b
  val : Val K.C K.cD K.ch p.L
  canon : CanonInst p.ta.Gx
  good : ∃ C5 c6 Cb : ℝ, ChGood K.s K.C C5 c6 Cb K.cD K.ch K.P K.a K.b K.c
  recOK : RecOK K.s K.C K.cD X.toD7
  ledOK : LedOK K.s K.C K.cD K.ch Y K.a K.b
  used : DQ.TupUsedAt X.toD7
  twAll : DQ.TwAllAt X.toD7 Y.nch Y.xd

abbrev BPt.D {K : Ctx} (β : BPt K) : D7 := β.p.pt.D

abbrev BPt.O {K : Ctx} (β : BPt K) : Obj β.D := Obj.ofPt β.p.pt

abbrev BPt.Is {K : Ctx} (β : BPt K) (Q : V4.Slot) : Prop := Q K β.X β.f β.T β.c

def RecAtK (QL : Ctx → ∀ D : D7, Lay D → Prop) : Prop :=
  Ev fun K => ∃ (D : D7) (Y : Lay D), Over D K.P K.Lv ∧ RecOK K.s K.C K.cD D ∧ LedOK K.s K.C K.cD K.ch Y K.a K.b ∧
    LocalQuadraticParts.TWAt D Y.nch Y.xd ∧ QL K D Y

def FromCoreK (Q : V4.Slot) (K : Ctx) (D : D7) (Y : Lay D) : Prop :=
  ∃ (X : Stages) (f : Fr X.B.toPre) (T : TwDat X.B) (c : V4.Core K X f T), Q K X f T c ∧
    (⟨D, layObj Y⟩ : Σ D : D7, Obj2 D) = ⟨X.toD7, c.O⟩

abbrev objAt {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) : Obj (Fm.D x i) :=
  ⟨Fm.L x i, Fm.gatT x i, Fm.Gx x i, Fm.Gy x i, Fm.GK, Fm.X x i, Fm.cX, Fm.ex x hx i⟩

abbrev BdT : Type 2 := ∀ D : D7, Obj D → ℝ → Type 1

abbrev BdP (Bd : BdT) : Type 1 := ∀ (D : D7) (O : Obj D) (c : ℝ), Bd D O c → Prop

abbrev LkT (Bd : BdT) : Type 1 := ∀ (K : Ctx) (β : BPt K) (c : ℝ), Bd β.D β.O c → Prop

abbrev RawSel (Bd : BdT) (𝒜 : FamClass) : Type 1 :=
  ∀ {eps : ℝ} (Fm : FamP eps) (_ : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), Bd (Fm.D x i) (objAt Fm x hx i) Fm.Csz

structure Par where
  eps : ℝ
  C : FC
  cD : ℝ
  ch : ℝ
  C5 : ℝ
  c6 : ℝ
  Cb : ℝ

def Par.Pos (κ : Par) : Prop := 0 < κ.C5 ∧ 0 < κ.c6 ∧ 0 < κ.Cb

def ParEv (q : Par → Prop) : Prop :=
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ eps C8 C5 c6 Cb : ℝ, 0 < eps → eps ≤ ε0 → eps < 1 / 52 → 1 ≤ C8 → ∃ K0 : TransportedAlt,
    ∀ C : FC, Std C → C.P.Cpde = C8 → C.Large K0 C.P.CF → ∃ c1 : ℝ, ∀ cD ≥ c1, ∃ c2 : ℝ, ∀ ch ≥ c2,
      q ⟨eps, C, cD, ch, C5, c6, Cb⟩

def Par.Of (κ : Par) (K : Ctx) : Prop :=
  K.C = κ.C ∧ K.cD = κ.cD ∧ K.ch = κ.ch ∧ K.s.eps = κ.eps ∧ ChGood K.s K.C κ.C5 κ.c6 κ.Cb K.cD K.ch K.P K.a K.b K.c

def EvP (p : Par → Ctx → Prop) : Prop :=
  ParEv fun κ => κ.Pos → ∃ x0 : ℝ, ∀ K : Ctx, κ.Of K → x0 ≤ K.s.x → p κ K

theorem ParEv.and {p q : Par → Prop} (hp : ParEv p) (hq : ParEv q) : ParEv fun κ => p κ ∧ q κ := by
  obtain ⟨a, ha, hp⟩ := hp
  obtain ⟨b, hb, hq⟩ := hq
  refine ⟨min a b, lt_min ha hb, fun e C8 C5 c6 Cb he hle h52 h8 => ?_⟩
  obtain ⟨K, hK⟩ := hp e C8 C5 c6 Cb he (hle.trans (min_le_left _ _)) h52 h8
  obtain ⟨K', hK'⟩ := hq e C8 C5 c6 Cb he (hle.trans (min_le_right _ _)) h52 h8
  refine ⟨K.sup K', fun C hC hC8 hL => ?_⟩
  obtain ⟨a1, ha1⟩ := hK C hC hC8 (large_of_sup hL).1
  obtain ⟨b1, hb1⟩ := hK' C hC hC8 (large_of_sup hL).2
  refine ⟨max a1 b1, fun cD hcD => ?_⟩
  obtain ⟨a2, ha2⟩ := ha1 cD (le_trans (le_max_left _ _) hcD)
  obtain ⟨b2, hb2⟩ := hb1 cD (le_trans (le_max_right _ _) hcD)
  exact ⟨max a2 b2, fun ch hch => ⟨ha2 ch (le_trans (le_max_left _ _) hch), hb2 ch (le_trans (le_max_right _ _) hch)⟩⟩

theorem ParEv.mono {p q : Par → Prop} (h : ∀ κ, p κ → q κ) (hp : ParEv p) : ParEv q := by
  obtain ⟨a, ha, hp⟩ := hp
  refine ⟨a, ha, fun e C8 C5 c6 Cb he hle h52 h8 => ?_⟩
  obtain ⟨K, hK⟩ := hp e C8 C5 c6 Cb he hle h52 h8
  refine ⟨K, fun C hC hC8 hL => ?_⟩
  obtain ⟨a1, ha1⟩ := hK C hC hC8 hL
  refine ⟨a1, fun cD hcD => ?_⟩
  obtain ⟨a2, ha2⟩ := ha1 cD hcD
  exact ⟨a2, fun ch hch => h _ (ha2 ch hch)⟩

theorem ParEv.of_all {p : Par → Prop} (h : ∀ κ, p κ) : ParEv p :=
  ⟨1, one_pos, fun _ _ _ _ _ _ _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ => ⟨0, fun _ _ => ⟨0, fun _ _ => h _⟩⟩⟩⟩

theorem ParEv.choose {α : Type} [Nonempty α] {r : Par → α → Prop} (h : ParEv fun κ => ∃ a, r κ a) :
    ∃ f : Par → α, ParEv fun κ => r κ (f κ) :=
  ⟨fun κ => Classical.epsilon (r κ), h.mono fun _ H => Classical.epsilon_spec H⟩

theorem EvP.and {p q : Par → Ctx → Prop} (hp : EvP p) (hq : EvP q) : EvP fun κ K => p κ K ∧ q κ K :=
  (ParEv.and hp hq).mono fun _ H h0 =>
    let ⟨a, ha⟩ := H.1 h0
    let ⟨b, hb⟩ := H.2 h0
    ⟨max a b, fun K h hx => ⟨ha K h (le_trans (le_max_left _ _) hx), hb K h (le_trans (le_max_right _ _) hx)⟩⟩

theorem EvP.mono {p q : Par → Ctx → Prop} (h : ∀ κ K, κ.Of K → p κ K → q κ K) (hp : EvP p) : EvP q :=
  ParEv.mono (fun κ H h0 => let ⟨a, ha⟩ := H h0; ⟨a, fun K hk hx => h κ K hk (ha K hk hx)⟩) hp

theorem EvP.of_all {p : Par → Ctx → Prop} (h : ∀ κ K, κ.Of K → p κ K) : EvP p :=
  ParEv.of_all fun κ _ => ⟨0, fun K hk _ => h κ K hk⟩

theorem EvP.of_evGd {p : Ctx → Prop} (hp : EvGd p) : EvP fun _ K => p K := by
  obtain ⟨a, ha, hp⟩ := hp
  refine ⟨a, ha, fun e C8 C5 c6 Cb he hle h52 h8 => ?_⟩
  obtain ⟨K, hK⟩ := hp e C8 C5 c6 Cb he hle h52 h8
  refine ⟨K, fun C hC hC8 hL => ?_⟩
  obtain ⟨a1, ha1⟩ := hK C hC hC8 hL
  refine ⟨a1, fun cD hcD => ?_⟩
  obtain ⟨a2, ha2⟩ := ha1 cD hcD
  refine ⟨a2, fun ch hch _ => ?_⟩
  obtain ⟨a3, ha3⟩ := ha2 ch hch
  exact ⟨a3, fun X h hx => ha3 X h.1 h.2.1 h.2.2.1 h.2.2.2.1 hx h.2.2.2.2⟩

theorem EvP.of_ev {p : Ctx → Prop} (hp : Ev p) : EvP fun _ K => p K := EvP.of_evGd (evGd_of_ev hp)

def RecExP (QO : Par → ∀ D : D7, Obj D → Prop) : Prop :=
  ParEv fun κ => ∃ cs x0 : ℝ, 0 < cs ∧
    ∀ (s : Scale) (P : PreCh) (a b : P.R.A → ℤ) (c : P.Word → Fin (P.R.k - 2) → Bool),
      s.eps = κ.eps → x0 ≤ s.x → ChGood s κ.C κ.C5 κ.c6 κ.Cb κ.cD κ.ch P a b c →
      ∃ (du : P.Word → ℕ) (Ds : ℝ), (∀ u, 0 < du u) ∧ 0 < Ds ∧
        (∀ u, cs * P.R.m * s.L ≤ Real.log ((Ds / du u) ^ ((1 : ℝ) / (P.R.f * P.R.k)) *
          GamS κ.C s P.R ^ (-(2 : ℝ) / (P.R.f * P.R.k)))) ∧
        ∀ Lv : LevCh P, Lv.duStar = du → Lv.Dstar = Ds → Lv.GamP = GamS κ.C s P.R →
          ∃ (D : D7) (Y : Lay D), Over D P Lv ∧ RecOK s κ.C κ.cD D ∧ LedOK s κ.C κ.cD κ.ch Y a b ∧ LocalQuadraticParts.TWAt D Y.nch Y.xd ∧
            ∀ p : LedPart κ.C Y, p.L.sc = s → WtEq p.L a b → Val κ.C κ.cD κ.ch p.L → CanonInst p.ta.Gx →
              QO κ p.pt.D (Obj.ofPt p.pt)

theorem recExP_const_iff (QO : ∀ D : D7, Obj D → Prop) : (RecExP fun _ => QO) ↔ RecEx QO := Iff.rfl

def ObjCP (Q : Par → PtProp) : Prop :=
  ParEv fun κ => ∃ x0 : ℝ,
    ∀ (s : Scale) (R : Ranks) (H : Host R) (q0 : ℕ) (a b : R.A → ℤ) (M : ℕ)
      (c : Fin M → Fin (R.k - 2) → Bool) (u0 : ℕ), s.eps = κ.eps → x0 ≤ s.x → RankVal s R → H.CT2 = κ.C.CT2 →
      HostGood s κ.C.P.Cpde κ.C5 κ.c6 κ.Cb H q0 → q0 = DC.q0H H → WinOK s κ.C.GK H a b →
      M = ⌈3 * Real.exp (κ.C.CGam * (R.m : ℝ) ^ 5 * R.f * s.L) ^ 2 * s.x ^ κ.C.P.CF⌉₊ → Function.Injective c → u0 < R.n →
      ∃ p : Pt κ.C, p.L.sc = s ∧ Val κ.C κ.cD κ.ch p.L ∧ HostArith p.D.host ∧ p.From H a b c u0 ∧ CanonInst p.ta.Gx ∧ p.Has (Q κ)

def KitCPW (la : ℝ) (Q : Par → PtProp) : Prop :=
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ eps : ℝ, 0 < eps → eps ≤ ε0 → eps < 1 / 52 → ∃ (CT2 C8 C5 c6 Cb : ℝ) (K0 : TransportedAlt),
    1 ≤ C8 ∧ 0 < C5 ∧ 0 < c6 ∧ 0 < Cb ∧
    ∀ C : FC, Std C → C.CT2 = CT2 → C.P.Cpde = C8 → C.Large K0 C.P.CF → ∃ c1 : ℝ, ∀ cD ≥ c1, ∃ c2 : ℝ, ∀ ch ≥ c2,
      ∃ x0 : ℝ, ∃ S : Scales la, ∀ s : Scale, s.eps = eps → x0 ≤ s.x → S.Mem s →
        ∃ k : Kit C cD ch s, ∀ i, (k.pt i).Has (Q ⟨eps, C, cD, ch, C5, c6, Cb⟩) ∧ ThickSetLowerBound (k.pt i).L ∧ ChBad_at (k.pt i).ta.Gx Cb ∧
          ChQD_at (k.pt i).D (k.pt i).L.sc.x (k.pt i).L.sc.eps C5

def KitCP (Q : Par → PtProp) : Prop := ∃ la : ℝ, 1 < la ∧ KitCPW la Q

structure Link (κ : Par) {eps : ℝ} (Fm : FamP eps) : Prop where
  eps_eq : κ.eps = eps
  pos : κ.Pos
  std : Std κ.C
  pre : Fm.cPre = κ.C.cPre
  out : (DC.setTu Fm κ.C.CTu).cOut = κ.C.cOut
  mid : Fm.cMid = κ.C.cMid
  last : Fm.cLast = κ.C.cLast

theorem Link.csz {κ : Par} {eps : ℝ} {Fm : FamP eps} (h : Link κ Fm) : Fm.Csz = κ.C.Csz := by
  have := congrArg (fun f : ℝ → List ℝ => (f 0).getD 2 0) h.mid
  simpa [FamP.cMid, FC.cMid] using this

theorem Link.host {κ : Par} {eps : ℝ} {Fm : FamP eps} (h : Link κ Fm) : max Fm.Co Fm.J = κ.C.P.Cpde :=
  congrArg (fun l : List ℝ => l.getD 15 0) h.out

def clsP (QO : Par → ∀ D : D7, Obj D → Prop) : FamClass := fun Fm => ∃ κ : Par, Link κ Fm ∧ DQ.cls7 (QO κ) Fm

theorem familyClassWithFurtherProperties_mono {QO QO' : ∀ D : D7, Obj D → Prop} (h : ∀ D O, QO D O → QO' D O) {eps : ℝ} (Fm : FamP eps)
    (hc : DQ.cls7 QO Fm) : DQ.cls7 QO' Fm :=
  ⟨fun x hx i => let t := hc.1 x hx i
    ⟨⟨⟨⟨⟨h _ _ t.1.1.1.1.1, t.1.1.1.1.2⟩, t.1.1.1.2⟩, t.1.1.2⟩, t.1.2⟩, t.2⟩, hc.2⟩

theorem sevenDuties_of_class {QO : Par → ∀ D : D7, Obj D → Prop} {eps : ℝ} {Fm : FamP eps} (h : clsP QO Fm) :
    DQ.Duty7 Fm ∧ DQ.MtStableF Fm := let ⟨_, _, h⟩ := h; DQ.familyClass_sevenDuties_and_stableLattices _ Fm h

variable {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd)

def Built (κ : Par) : BdP Bd := fun D O c b =>
  ∃ (K : Ctx) (β : BPt K) (b' : Bd β.D β.O c), κ.Of K ∧ β.Is Q ∧ Lk K β c b' ∧
    (⟨D, O, b⟩ : Σ (D : D7) (O : Obj D), Bd D O c) = ⟨β.D, β.O, b'⟩

def QOf (E : Par → BdP Bd) (κ : Par) : ∀ D : D7, Obj D → Prop := fun D O =>
  κ.Pos → ∀ c : ℝ, ∃ b : Bd D O c, Built Q Lk κ D O c b ∧ E κ D O c b

def cls (E : Par → BdP Bd) : FamClass := clsP (QOf Q Lk E)

def ExB : Prop := EvP fun _ K => ∀ β : BPt K, β.Is Q → ∀ c : ℝ, ∃ b : Bd β.D β.O c, Lk K β c b

def RowE (E : Par → BdP Bd) : Prop :=
  EvP fun κ K => ∀ β : BPt K, β.Is Q → ∀ (c : ℝ) (b : Bd β.D β.O c), Lk K β c b → E κ β.D β.O c b

def IsSel (E : Par → BdP Bd) (𝒜 : FamClass) (σ : RawSel Bd 𝒜) : Prop :=
  ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm), ∃ κ : Par, Link κ Fm ∧ DQ.cls7 (fun _ _ => True) Fm ∧
    ∀ (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), Built Q Lk κ _ _ _ (σ Fm hc x hx i) ∧ E κ _ _ _ (σ Fm hc x hx i)

def Row (H : ∀ 𝒜 : FamClass, RawSel Bd 𝒜 → Prop) : Prop :=
  ∃ E : Par → BdP Bd, RowE Q Lk E ∧ ∀ (𝒜 : FamClass) (σ : RawSel Bd 𝒜), IsSel Q Lk E 𝒜 σ → H 𝒜 σ

def AtAll (R : BdP Bd) : ∀ 𝒜 : FamClass, RawSel Bd 𝒜 → Prop := fun 𝒜 σ =>
  ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), R _ _ _ (σ Fm hc x hx i)

theorem cls_at {E : Par → BdP Bd} {eps : ℝ} (Fm : FamP eps) (hc : cls Q Lk E Fm) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) :
    ∃ b : Bd (Fm.D x i) (objAt Fm x hx i) Fm.Csz, Built Q Lk (Classical.choose hc) _ _ _ b ∧ E (Classical.choose hc) _ _ _ b :=
  DQ.familyClass_points_satisfy_objectProperty _ Fm (Classical.choose_spec hc).2 x hx i (Classical.choose_spec hc).1.pos Fm.Csz

def pick (E : Par → BdP Bd) : RawSel Bd (cls Q Lk E) := fun Fm hc x hx i => Classical.choose (cls_at Q Lk Fm hc x hx i)

theorem pick_isSel (E : Par → BdP Bd) : IsSel Q Lk E (cls Q Lk E) (pick Q Lk E) := fun Fm hc =>
  ⟨Classical.choose hc, (Classical.choose_spec hc).1, familyClassWithFurtherProperties_mono (fun _ _ _ => trivial) Fm (Classical.choose_spec hc).2,
    fun x hx i => Classical.choose_spec (cls_at Q Lk Fm hc x hx i)⟩

variable {Q Lk}

theorem Built.ind {κ : Par} {R : BdP Bd}
    (h : ∀ (K : Ctx) (β : BPt K) (c : ℝ) (b : Bd β.D β.O c), κ.Of K → β.Is Q → Lk K β c b → R β.D β.O c b)
    {D : D7} {O : Obj D} {c : ℝ} {b : Bd D O c} (hb : Built Q Lk κ D O c b) : R D O c b := by
  obtain ⟨K, β, b', h0, h1, h2, h3⟩ := hb
  cases h3
  exact h K β c _ h0 h1 h2

theorem Built.intro {κ : Par} {K : Ctx} {β : BPt K} {c : ℝ} {b : Bd β.D β.O c} (h0 : κ.Of K) (h1 : β.Is Q) (h2 : Lk K β c b) :
    Built Q Lk κ β.D β.O c b := ⟨K, β, b, h0, h1, h2, rfl⟩

theorem RowE.and {E E' : Par → BdP Bd} (h : RowE Q Lk E) (h' : RowE Q Lk E') :
    RowE Q Lk fun κ D O c b => E κ D O c b ∧ E' κ D O c b :=
  (EvP.and h h').mono fun _ _ _ H β hq c b hl => ⟨H.1 β hq c b hl, H.2 β hq c b hl⟩

theorem RowE.imp {E E' : Par → BdP Bd} (h : RowE Q Lk E)
    (hi : ∀ (κ : Par) (K : Ctx) (β : BPt K) (c : ℝ) (b : Bd β.D β.O c), κ.Of K → β.Is Q → Lk K β c b → E κ _ _ c b → E' κ _ _ c b) :
    RowE Q Lk E' := EvP.mono (fun κ K hk H β hq c b hl => hi κ K β c b hk hq hl (H β hq c b hl)) h

theorem RowE.of_all {E : Par → BdP Bd}
    (h : ∀ (κ : Par) (K : Ctx) (β : BPt K) (c : ℝ) (b : Bd β.D β.O c), κ.Of K → β.Is Q → Lk K β c b → E κ _ _ c b) :
    RowE Q Lk E := EvP.of_all fun κ K hk β hq c b hl => h κ K β c b hk hq hl

theorem IsSel.mono {E E' : Par → BdP Bd} (h : ∀ κ D O c b, E κ D O c b → E' κ D O c b) {𝒜 : FamClass} {σ : RawSel Bd 𝒜}
    (s : IsSel Q Lk E 𝒜 σ) : IsSel Q Lk E' 𝒜 σ := fun Fm hc =>
  let ⟨κ, h1, h2, h3⟩ := s Fm hc
  ⟨κ, h1, h2, fun x hx i => ⟨(h3 x hx i).1, h _ _ _ _ _ (h3 x hx i).2⟩⟩

theorem Row.and {H H' : ∀ 𝒜 : FamClass, RawSel Bd 𝒜 → Prop} (h : Row Q Lk H) (h' : Row Q Lk H') :
    Row Q Lk fun 𝒜 σ => H 𝒜 σ ∧ H' 𝒜 σ := by
  obtain ⟨E, e, h⟩ := h
  obtain ⟨E', e', h'⟩ := h'
  exact ⟨_, e.and e', fun 𝒜 σ s => ⟨h 𝒜 σ (s.mono fun _ _ _ _ _ t => t.1), h' 𝒜 σ (s.mono fun _ _ _ _ _ t => t.2)⟩⟩

theorem Row.imp {H H' : ∀ 𝒜 : FamClass, RawSel Bd 𝒜 → Prop} (h : Row Q Lk H)
    (hi : ∀ (𝒜 : FamClass) (σ : RawSel Bd 𝒜), IsSel Q Lk (fun _ _ _ _ _ => True) 𝒜 σ → H 𝒜 σ → H' 𝒜 σ) : Row Q Lk H' := by
  obtain ⟨E, e, h⟩ := h
  exact ⟨E, e, fun 𝒜 σ s => hi 𝒜 σ (s.mono fun _ _ _ _ _ _ => trivial) (h 𝒜 σ s)⟩

theorem Row.of_sel {H : ∀ 𝒜 : FamClass, RawSel Bd 𝒜 → Prop}
    (h : ∀ (𝒜 : FamClass) (σ : RawSel Bd 𝒜), IsSel Q Lk (fun _ _ _ _ _ => True) 𝒜 σ → H 𝒜 σ) : Row Q Lk H :=
  ⟨_, RowE.of_all fun _ _ _ _ _ _ _ _ => trivial, h⟩

theorem RowE.row {R : BdP Bd} (h : RowE Q Lk fun _ => R) : Row Q Lk (AtAll R) :=
  ⟨_, h, fun _ _ s _ Fm hc x hx i => let ⟨_, _, _, t⟩ := s Fm hc; (t x hx i).2⟩

section Map

variable {Bd' : BdT} {Q' : V4.Slot} {Lk' : LkT Bd'} (π : ∀ D O c, Bd D O c → Bd' D O c)

def RawSel.map {𝒜 : FamClass} (σ : RawSel Bd 𝒜) : RawSel Bd' 𝒜 := fun Fm hc x hx i => π _ _ _ (σ Fm hc x hx i)

theorem Row.map (hQ : ∀ K X f T c, Q K X f T c → Q' K X f T c)
    (hL : ∀ (K : Ctx) (β : BPt K) (c : ℝ) (b : Bd β.D β.O c), β.Is Q → Lk K β c b → Lk' K β c (π _ _ c b))
    {H : ∀ 𝒜 : FamClass, RawSel Bd' 𝒜 → Prop} (h : Row Q' Lk' H) : Row Q Lk fun 𝒜 σ => H 𝒜 (RawSel.map π σ) := by
  obtain ⟨E, e, h⟩ := h
  have hb : ∀ κ D O c (b : Bd D O c), Built Q Lk κ D O c b → Built Q' Lk' κ D O c (π D O c b) := fun κ D O c b hb =>
    Built.ind (R := fun D O c b => Built Q' Lk' κ D O c (π D O c b))
      (fun K β c b h0 h1 h2 => Built.intro h0 (hQ _ _ _ _ _ h1) (hL K β c b h1 h2)) hb
  refine ⟨fun κ D O c b => E κ D O c (π D O c b),
    EvP.mono (fun _ K _ H β hq c b hl => H β (hQ _ _ _ _ _ hq) c _ (hL K β c b hq hl)) e, fun 𝒜 σ s => h 𝒜 _ fun Fm hc => ?_⟩
  obtain ⟨κ, h1, h2, h3⟩ := s Fm hc
  exact ⟨κ, h1, h2, fun x hx i => ⟨hb _ _ _ _ _ (h3 x hx i).1, (h3 x hx i).2⟩⟩

end Map

abbrev Bd0 : BdT := fun _ _ _ => PUnit

def Row0 (Q : V4.Slot) (H : FamClass → Prop) : Prop := Row (Bd := Bd0) Q (fun _ _ _ _ => True) fun 𝒜 _ => H 𝒜

theorem Row0.row {H : FamClass → Prop} (h : Row0 Q H) (Lk : LkT Bd) : Row Q Lk fun 𝒜 _ => H 𝒜 :=
  Row.map (Bd' := Bd0) (fun _ _ _ _ => PUnit.unit) (fun _ _ _ _ _ t => t) (fun _ _ _ _ _ _ => trivial) h

theorem Row0.of_all {H : FamClass → Prop} (h : ∀ 𝒜 : FamClass, H 𝒜) : Row0 Q H := Row.of_sel fun 𝒜 _ _ => h 𝒜

theorem QOf₂ {E : Par → BdP Bd} (hx : ExB Q Lk) (he : RowE Q Lk E) :
    EvP fun κ K => ∀ β : BPt K, β.Is Q → QOf Q Lk E κ β.D β.O :=
  (EvP.and hx he).mono fun _ _ hk H β hq _ c => let ⟨b, hb⟩ := H.1 β hq c; ⟨b, Built.intro hk hq hb, H.2 β hq c b hb⟩

theorem Row.elim {H : ∀ 𝒜 : FamClass, RawSel Bd 𝒜 → Prop} (hx : ExB Q Lk) (h : Row Q Lk H) :
    ∃ E : Par → BdP Bd, (EvP fun κ K => ∀ β : BPt K, β.Is Q → QOf Q Lk E κ β.D β.O) ∧ H (cls Q Lk E) (pick Q Lk E) :=
  let ⟨E, e, h⟩ := h; ⟨E, QOf₂ hx e, h _ _ (pick_isSel Q Lk E)⟩

abbrev W1 (𝒜 : FamClass) : FamClass := fun Fm =>
  ((𝒜 Fm ∧ DC.DGamDvdF Fm ∧ DC.TameDistinctF Fm ∧ BoxesF Fm ∧ QDRowsF Fm ∧ Fm.CYL ≤ 9) ∧ Formalism.MainNotions.Pk.DGamSmooth Fm) ∧ TwGood Fm

abbrev W3 (𝒜 : FamClass) : FamClass := fun Fm =>
  W1 𝒜 Fm ∧ (∃ CH : ℝ, ChosenE Fm 3 CH) ∧ TuSize Fm ∧ DGamSize Fm

theorem w3_a {𝒜 : FamClass} {eps : ℝ} {Fm : FamP eps} (h : W3 𝒜 Fm) : 𝒜 Fm := h.1.1.1.1

def EvC (R : ∀ D : D7, Obj D → Prop) (𝒜 : FamClass) : Prop :=
  Closed (W3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x), R (Fm.D x i) (objAt Fm x hx i)

def EvCC {α : Type} (R : α → ∀ D : D7, Obj D → Prop) (𝒜 : FamClass) : Prop :=
  Closed (W3 𝒜) fun Fm _ => ∃ (a : α) (x0 : ℝ), ∀ x, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x), R a (Fm.D x i) (objAt Fm x hx i)

theorem evaluation_constantFamily {α : Type} {R : α → ∀ D : D7, Obj D → Prop} (a : Par → α)
    (h : EvP fun κ K => ∀ β : BPt K, β.Is Q → R (a κ) β.D β.O) : Row0 Q (EvCC R) :=
  ⟨fun κ D O _ _ => R (a κ) D O, EvP.mono (fun _ _ _ H β hq _ _ _ => H β hq) h, fun _ _ s =>
    ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ hc _ =>
      let ⟨κ, _, _, t⟩ := s Fm (w3_a hc); ⟨a κ, 0, fun x _ hx i => (t x hx i).2⟩⟩⟩⟩

theorem validForConstructedPointClasses_eventuallyWorkingClass {R : ∀ D : D7, Obj D → Prop} (h : EvP fun _ K => ∀ β : BPt K, β.Is Q → R β.D β.O) : Row0 Q (EvC R) :=
  ⟨fun _ D O _ _ => R D O, EvP.mono (fun _ _ _ H β hq _ _ _ => H β hq) h, fun _ _ s =>
    ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ hc _ =>
      let ⟨_, _, _, t⟩ := s Fm (w3_a hc); ⟨0, fun x _ hx i => (t x hx i).2⟩⟩⟩⟩

example : ExB (Bd := Bd0) Q fun _ _ _ _ => True := EvP.of_all fun _ _ _ _ _ _ => ⟨PUnit.unit, trivial⟩

end GlobalTheory.Fc

end
