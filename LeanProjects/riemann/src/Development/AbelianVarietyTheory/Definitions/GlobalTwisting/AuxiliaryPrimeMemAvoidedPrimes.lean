import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
import Formalism.SharpRestriction.LevelLetterCocycles.TwGood
import Formalism.SharpRestriction.GlobalSchurBounds.MainIn
import Formalism.LocalRingCardinality.DataMink
import Formalism.CyclotomicNorms.StatementI
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DisjointExceptional
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.TameGeneratorWindow
import Development.AutomorphicArithmetic.PrimeDiscriminants.Scales

noncomputable section

namespace GlobalTheory.EX.DC

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.FrobeniusOrbits Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

def MinkDiv : Prop := ∀ n : ℕ, MinkMult n (minkM n)

def DGamDvdF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) u,
    ((Fm.D x i).mem u).C.DGam ∣ minkM (2 * (Fm.D x i).R.f * (Fm.D x i).R.N (Fm.D x i).R.m)

def CodeUpF {eps : ℝ} (Fm : FamP eps) (C0 CH : ℝ) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x,
    (Fintype.card (Fm.D x i).what₂.Word : ℝ) ≤ C0 * GamL (Fm.L x i) ^ 2 * x ^ CH + 1

def tameList {g m : ℕ} (χ : Fin m → (ZMod g)ˣ) : Option (Fin m × Bool) → (ZMod g)ˣ
  | none => 1
  | some (j, true) => χ j
  | some (j, false) => (χ j)⁻¹

def TameDistinct (r g : ℕ) [Fact g.Prime] {m : ℕ} (χ : Fin m → (ZMod g)ˣ) : Prop :=
  Function.Injective (tameList χ) ∧
  (∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ Formalism.CyclotomicNorms.BB r g →
    Function.Injective (fun o => Formalism.CyclotomicNorms.primeToPart ℓ
      (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) ((tameList χ o : (ZMod g)ˣ) : ZMod g)))) ∧
  ∀ j, IsSquare (χ j)

def TameDistinctF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) (k : Fin 2) (v : (Fm.D x i).nd.PlG k),
    haveI : Fact ((Fm.D x i).host.g k).Prime := ⟨(Fm.D x i).host.g_prime k⟩
    TameDistinct (Fm.D x i).R.r ((Fm.D x i).host.g k) ((Fm.D x i).nd.chiT k v)

def DesignChoices (𝒞 : FamClass) (C0 : ℝ) (cT : ℝ → ℝ → ℝ) : Prop :=
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ eps : ℝ, 0 < eps → eps ≤ ε0 → ∀ K : TransportedAlt, ∃ (Fm : FamP eps) (CH C5 Cb : ℝ),
    𝒞 Fm ∧ 0 ≤ CH ∧ Fm.Large K CH ∧ 0 < C5 ∧ 0 < Cb ∧ ThickSetEventually Fm ∧ ChosenTT Fm ∧ ChosenBad Fm Cb ∧ ChosenQD Fm C5 ∧
      ChosenCode Fm C0 CH ∧ BoxesF Fm ∧ QDRowsF Fm ∧ DGamDvdF Fm ∧ cT eps Fm.CYL ≤ Fm.CTu ∧
      TameDistinctF Fm ∧ Fm.CF = CH ∧ CodeUpF Fm C0 CH ∧ Fm.CYL ≤ 9

abbrev WithTw (𝒞 : FamClass) : FamClass := fun Fm => 𝒞 Fm ∧ TwGood Fm

def PageFix {eps : ℝ} (Fm : FamP eps) : Prop :=
  Fm.Cp = 1 ∧ Fm.eP = 12 ∧ Fm.cTO = 28 * Fm.eP + 41 ∧ Fm.Ct = Fm.cTO + 24 ∧ Fm.CetaF = 6 ∧ Fm.Cc = 2 ∧ Fm.cw = 9 / 10 ∧ Fm.CYL = 9 ∧
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x),
    (Fm.D x i).host.ccK = ⊤ ∧
    (∀ τ τ', ((Fm.D x i).hc τ).v = ((Fm.D x i).hc τ').v) ∧
    (∀ j : Fin 2, (((Fm.D x i).host.g j : ℕ) : ℝ) ≤ Real.exp (9 * (Fm.L x i).sc.L)) ∧
    ((Fm.D x i).host.pde : ℝ) < (Fm.L x i).sc.X' ∧ ((Fm.D x i).host.pde' : ℝ) < (Fm.L x i).sc.X' ∧
    (Fm.L x i).j0 = ⌈Real.logb 5 (((Fm.D x i).R.n : ℝ) * (Fm.D x i).R.N (Fm.D x i).R.m / (Fm.D x i).R.m)⌉₊ ∧
    (Fm.D x i).host.Lw = 10 * ⌈(Fm.Ct + 4) * Real.log x⌉₊ + 2 * ⌈30 / eps⌉₊ + 22 ∧
    (Fm.parT x hx i).TO = ⌈x ^ Fm.cTO⌉₊

def PageWin {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∀ x (_ : Fm.x1 < x) (i : Fm.Ix x),
    (x ^ (2 + 8 * eps) ≤ ((Fm.D x i).R.n : ℝ) ∧ ((Fm.D x i).R.n : ℝ) ≤ 2 * x ^ (2 + 8 * eps)) ∧
    (Real.sqrt (x * (Fm.L x i).sc.delta1) ≤ ((Fm.D x i).R.m : ℝ) ∧
      ((Fm.D x i).R.m : ℝ) ≤ 2 * Real.sqrt (x * (Fm.L x i).sc.delta1)) ∧
    (x ^ (9 / 2 + 10 * eps) ≤ ((Fm.D x i).R.k : ℝ) ∧ ((Fm.D x i).R.k : ℝ) ≤ 2 * x ^ (9 / 2 + 10 * eps))

def rPrH {R : Ranks} (H : Host R) : ℕ :=
  sInf {p : ℕ | p.Prime ∧ ¬ p ∣ H.QS * H.q * H.d * (H.pde - 1) * (H.pde' - 1) * Ideal.absNorm H.ccK}

def q0H {R : Ranks} (H : Host R) : ℕ :=
  sInf {p : ℕ | p.Prime ∧ p % (rPrH H * (H.QS * H.q * H.d)) = 1 ∧ ¬ p ∣ Ideal.absNorm H.ccK}

def GlobalTwistingFacts {D : D7} (L : SizeData₂ D) : Prop :=
  q0Av D ∈ D.host.levelPrimes ∧ (q0Av D).Prime ∧ q0Av D % (rPrAv D * LevelStarExponents.condE D) = 1 ∧
    Real.log (q0Av D) ≤ L.sc.L ∧ (q0Av D : ℝ) < L.sc.X' ∧ (q0Av D : ℝ) ≤ GlobalTheory.IndefiniteRowSideFullHecke.TameGeneratorWindow.lJ L ∧
    q0Av D ≠ D.host.pde ∧ q0Av D ≠ D.host.pde' ∧ (∀ j, q0Av D ≠ D.host.g j) ∧ ∀ u, q0Av D ≠ (D.mem u).A.T

def globalTwisting_fact {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∀ x (_ : Fm.x1 < x) (i : Fm.Ix x), GlobalTwistingFacts (Fm.L x i)

def WallAll {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∀ x (_ : Fm.x1 < x) (i : Fm.Ix x), AuxBlock8.admW (Fm.D x i) (Fm.L x i) (Fm.Gx x i) Fm.GK

def Duty {eps : ℝ} (Fm : FamP eps) : Prop := PageFix Fm ∧ PageWin Fm ∧ globalTwisting_fact Fm ∧ TameDistinctF Fm ∧ WallAll Fm

def TamePt : PtProp := fun D _ _ _ _ _ _ _ _ => ∀ (k : Fin 2) (v : D.nd.PlG k),
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  TameDistinct D.R.r (D.host.g k) (D.nd.chiT k v)

def MinkPt : PtProp := fun D _ _ _ _ _ _ _ _ => DGamChoice_at D

def WallPt : PtProp := fun D L _ Gx _ K _ _ _ => AuxBlock8.admW D L Gx K

def twistingGlobalPointProp : PtProp := fun _ L _ _ _ _ _ _ _ => GlobalTwistingFacts L

def withObj (Q : PtProp) : PtProp := (Q.and twistingGlobalPointProp).and (TamePt.and (MinkPt.and TwPt))

def cls (Q : PtProp) : FamClass := fun Fm =>
  classOf ((withDuty (withObj Q)).and WallPt) Fm ∧ PageFix Fm ∧ PageWin Fm

def HostExQW (la : ℝ) (P : HostReq) : Prop := HostExW la fun C5 s R H q0 => q0 = q0H H ∧ P C5 s R H q0

def HostExQ : Prop := HostExP fun _ _ _ H q0 => q0 = q0H H

def ObjC (Q : PtProp) : Prop :=
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ eps C8 C5 c6 Cb : ℝ, 0 < eps → eps ≤ ε0 → eps < 1 / 52 → 1 ≤ C8 → ∃ K0 : TransportedAlt,
    ∀ C : FC, Std C → C.P.Cpde = C8 → C.Large K0 C.P.CF → ∃ c1 : ℝ, ∀ cD ≥ c1, ∃ c2 : ℝ, ∀ ch ≥ c2, ∃ x0 : ℝ,
      ∀ (s : Scale) (R : Ranks) (H : Host R) (q0 : ℕ) (a b : R.A → ℤ) (M : ℕ)
        (c : Fin M → Fin (R.k - 2) → Bool) (u0 : ℕ), s.eps = eps → x0 ≤ s.x → RankVal s R → H.CT2 = C.CT2 →
        HostGood s C8 C5 c6 Cb H q0 → q0 = q0H H → WinOK s C.GK H a b →
        M = ⌈3 * Real.exp (C.CGam * (R.m : ℝ) ^ 5 * R.f * s.L) ^ 2 * s.x ^ C.P.CF⌉₊ → Function.Injective c → u0 < R.n →
        ∃ p : Pt C, p.L.sc = s ∧ Val C cD ch p.L ∧ HostArith p.D.host ∧ p.From H a b c u0 ∧ CanonInst p.ta.Gx ∧ p.Has Q

def HostWW (la : ℝ) (P : HostReq) : Prop :=
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ eps : ℝ, 0 < eps → eps ≤ ε0 → eps < 1 / 52 → ∃ (CT2 C8 C5 c6 Cb : ℝ) (K0 : TransportedAlt),
    1 ≤ C8 ∧ 0 < C5 ∧ 0 < c6 ∧ 0 < Cb ∧
    ∀ C : FC, Std C → C.CT2 = CT2 → C.P.Cpde = C8 → C.Large K0 C.P.CF → ∃ c1 : ℝ, ∀ cD ≥ c1, ∃ c2 : ℝ, ∀ ch ≥ c2, ∃ x0 : ℝ,
      ∃ S : Scales la, ∀ s : Scale, s.eps = eps → x0 ≤ s.x → S.Mem s →
        ∃ (R : Ranks) (H : Host R) (q0 : ℕ) (a b : R.A → ℤ),
          RankVal s R ∧ H.CT2 = CT2 ∧ HostGood s C8 C5 c6 Cb H q0 ∧ q0 = q0H H ∧
          (∀ t, t ∉ H.TT → a t = 0 ∧ b t = 0) ∧ WinOK s C.GK H a b ∧ WOK s cD ch C.GK H a b ∧ P C5 s R H q0

def HostW : Prop := ∃ la : ℝ, 1 < la ∧ HostWW la fun _ _ _ _ _ => True

def KitCW (la : ℝ) (Q : PtProp) : Prop :=
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ eps : ℝ, 0 < eps → eps ≤ ε0 → eps < 1 / 52 → ∃ (CT2 C8 : ℝ) (K0 : TransportedAlt), 1 ≤ C8 ∧
    ∀ C : FC, Std C → C.CT2 = CT2 → C.P.Cpde = C8 → C.Large K0 C.P.CF → ∃ c1 : ℝ, ∀ cD ≥ c1, ∃ c2 : ℝ, ∀ ch ≥ c2,
      ∃ C5 Cb x0 : ℝ, 0 < C5 ∧ 0 < Cb ∧ ∃ S : Scales la, ∀ s : Scale, s.eps = eps → x0 ≤ s.x → S.Mem s →
        ∃ k : Kit C cD ch s, ∀ i, (k.pt i).Has Q ∧ ThickSetLowerBound (k.pt i).L ∧ ChBad_at (k.pt i).ta.Gx Cb ∧
          ChQD_at (k.pt i).D (k.pt i).L.sc.x (k.pt i).L.sc.eps C5

def KitC (Q : PtProp) : Prop := ∃ la : ℝ, 1 < la ∧ KitCW la Q

def WClosed : Prop :=
  Closed (fun _ => True) fun Fm _ => ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, AuxBlock8.WeightVectorExists (Fm.D x i) (Fm.L x i) (Fm.Gx x i) Fm.GK

def setTu {eps : ℝ} (Fm : FamP eps) (t : ℝ) : FamP eps := { Fm with CTu := t }

def thrTu (K : TransportedAlt) (t : ℝ) : TransportedAlt := ⟨K.pre, K.t, fun l => K.mid (l.set 13 t), fun l => K.last (l.set 13 t)⟩

theorem setTu_large {eps : ℝ} (Fm : FamP eps) (K : TransportedAlt) (t CH : ℝ) :
    (setTu Fm t).Large K CH ↔ Fm.Large (thrTu K t) CH := Iff.rfl

theorem setTu_cls (Q : PtProp) {eps : ℝ} (Fm : FamP eps) (t : ℝ) : cls Q (setTu Fm t) ↔ cls Q Fm := Iff.rfl

theorem duty_of_cls (Q : PtProp) {eps : ℝ} (Fm : FamP eps) (h : cls Q Fm) : Duty Fm := by
  obtain ⟨hc, hf, hw⟩ := h
  refine ⟨hf, hw, fun x hx i => (hc x hx i).1.1.1.2, ⟨Fm.x1 + 1, fun x hx i => ?_⟩, fun x hx i => (hc x hx i).2⟩
  exact (hc x (by linarith) i).1.1.2.1

theorem classOf_of_cls (Q : PtProp) {eps : ℝ} (Fm : FamP eps) (h : cls Q Fm) : classOf Q Fm :=
  fun x hx i => (h.1 x hx i).1.1.1.1

theorem ObjC.imp {Q Q' : PtProp} (h : ObjC Q) (hQ : ∀ (C : FC) (p : Pt C), p.Has Q → p.Has Q') : ObjC Q' := by
  obtain ⟨ε0, h0, h⟩ := h
  refine ⟨ε0, h0, fun eps C8 C5 c6 Cb a1 a2 a3 a4 => ?_⟩
  obtain ⟨K0, h⟩ := h eps C8 C5 c6 Cb a1 a2 a3 a4
  refine ⟨K0, fun C b1 b2 b3 => ?_⟩
  obtain ⟨c1, h⟩ := h C b1 b2 b3
  refine ⟨c1, fun cD hcD => ?_⟩
  obtain ⟨c2, h⟩ := h cD hcD
  refine ⟨c2, fun ch hch => ?_⟩
  obtain ⟨x0, h⟩ := h ch hch
  refine ⟨x0, fun s R H q0 a b M c u0 d1 d2 d3 d4 d5 d0 d6 d7 d8 d9 => ?_⟩
  obtain ⟨p, e1, e2, e3, e4, e5, e6⟩ := h s R H q0 a b M c u0 d1 d2 d3 d4 d5 d0 d6 d7 d8 d9
  exact ⟨p, e1, e2, e3, e4, e5, hQ C p e6⟩

theorem HostExQW.imp {la : ℝ} {P P' : HostReq} (h : HostExQW la P)
    (hP : ∀ C5 s R H q0, P C5 s R H q0 → P' C5 s R H q0) : HostExQW la P' :=
  HostExW.imp h fun _ _ _ _ _ c => ⟨c.1, hP _ _ _ _ _ c.2⟩

theorem HostWW.imp {la : ℝ} {P P' : HostReq} (h : HostWW la P)
    (hP : ∀ C5 s R H q0, P C5 s R H q0 → P' C5 s R H q0) : HostWW la P' := by
  obtain ⟨ε0, h0, h⟩ := h
  refine ⟨ε0, h0, fun eps h1 h2 h3 => ?_⟩
  obtain ⟨CT2, C8, C5, c6, Cb, K0, a1, a2, a3, a4, h⟩ := h eps h1 h2 h3
  refine ⟨CT2, C8, C5, c6, Cb, K0, a1, a2, a3, a4, fun C a b c d => ?_⟩
  obtain ⟨c1, h⟩ := h C a b c d
  refine ⟨c1, fun cD hcD => ?_⟩
  obtain ⟨c2, h⟩ := h cD hcD
  refine ⟨c2, fun ch hch => ?_⟩
  obtain ⟨x0, S, h⟩ := h ch hch
  refine ⟨x0, S, fun s b1 b2 b3 => ?_⟩
  obtain ⟨R, H, q0, u, v, e1, e2, e3, e4, e5, e6, e7, e8⟩ := h s b1 b2 b3
  exact ⟨R, H, q0, u, v, e1, e2, e3, e4, e5, e6, e7, hP _ _ _ _ _ e8⟩

section Primes

variable {R : Ranks} (H : Host R)

theorem cond_pos : 0 < H.QS * H.q * H.d := by
  have h1 := H.QS_pos
  have h2 := H.hyp.1.pos
  have h3 := H.hyp.2.1.pos
  positivity

theorem absNorm_ccK_ne_zero : Ideal.absNorm H.ccK ≠ 0 := fun h => H.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 h)

theorem rPrH_spec : (rPrH H).Prime ∧
    ¬ rPrH H ∣ H.QS * H.q * H.d * (H.pde - 1) * (H.pde' - 1) * Ideal.absNorm H.ccK := by
  refine Nat.sInf_mem (s := {p : ℕ | p.Prime ∧
    ¬ p ∣ H.QS * H.q * H.d * (H.pde - 1) * (H.pde' - 1) * Ideal.absNorm H.ccK}) ?_
  have h1 := cond_pos H
  have h2 : 0 < H.pde - 1 := Nat.sub_pos_of_lt H.pde_prime.one_lt
  have h3 : 0 < H.pde' - 1 := Nat.sub_pos_of_lt H.pde'_prime.one_lt
  have h4 := Nat.pos_of_ne_zero (absNorm_ccK_ne_zero H)
  obtain ⟨p, hp, hpp⟩ := Nat.exists_infinite_primes
    (H.QS * H.q * H.d * (H.pde - 1) * (H.pde' - 1) * Ideal.absNorm H.ccK + 1)
  exact ⟨p, hpp, Nat.not_dvd_of_pos_of_lt (by positivity) hp⟩

theorem rPrH_le {p : ℕ} (hp : p.Prime)
    (h : ¬ p ∣ H.QS * H.q * H.d * (H.pde - 1) * (H.pde' - 1) * Ideal.absNorm H.ccK) : rPrH H ≤ p :=
  Nat.sInf_le ⟨hp, h⟩

theorem one_lt_rPrH_mul : 1 < rPrH H * (H.QS * H.q * H.d) :=
  (rPrH_spec H).1.one_lt.trans_le (Nat.le_mul_of_pos_right _ (cond_pos H))

theorem globalTwisting_spec_fact : (q0H H).Prime ∧ q0H H % (rPrH H * (H.QS * H.q * H.d)) = 1 ∧ ¬ q0H H ∣ Ideal.absNorm H.ccK := by
  refine Nat.sInf_mem (s := {p : ℕ | p.Prime ∧ p % (rPrH H * (H.QS * H.q * H.d)) = 1 ∧ ¬ p ∣ Ideal.absNorm H.ccK}) ?_
  have h1 := one_lt_rPrH_mul H
  obtain ⟨p, hp, hlt, hm⟩ := Nat.exists_prime_gt_modEq_one (k := rPrH H * (H.QS * H.q * H.d)) (Ideal.absNorm H.ccK) (by omega)
  exact ⟨p, hp, Eq.trans hm (Nat.mod_eq_of_lt h1),
    Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero (absNorm_ccK_ne_zero H)) hlt⟩

theorem globalTwisting_le_fact (hc : H.ccK = ⊤) {p : ℕ} (hp : p.Prime) (h : p % (rPrH H * (H.QS * H.q * H.d)) = 1) : q0H H ≤ p :=
  Nat.sInf_le ⟨hp, h, by rw [hc, Ideal.absNorm_top, Nat.dvd_one]; exact hp.ne_one⟩

theorem mod_cond : q0H H % (H.QS * H.q * H.d) = 1 := by
  rw [← Nat.mod_mul_left_mod (q0H H) (rPrH H), (globalTwisting_spec_fact H).2.1]
  refine Nat.mod_eq_of_lt ?_
  exact H.hyp.2.1.one_lt.trans_le (Nat.le_mul_of_pos_left _ (Nat.mul_pos H.QS_pos H.hyp.1.pos))

theorem rPrH_dvd : rPrH H ∣ q0H H - 1 :=
  (Dvd.intro _ rfl).trans ((Nat.modEq_iff_dvd' (globalTwisting_spec_fact H).1.one_le).1
    (((globalTwisting_spec_fact H).2.1.trans (Nat.mod_eq_of_lt (one_lt_rPrH_mul H)).symm).symm))

theorem q0H_ne_pde_and_ne_pde' : q0H H ≠ H.pde ∧ q0H H ≠ H.pde' := by
  have h := rPrH_dvd H
  constructor <;> intro e <;> rw [e] at h <;> apply (rPrH_spec H).2
  · exact ((h.mul_left _).mul_right _).mul_right _
  · exact (h.mul_left _).mul_right _

theorem globalTwisting_congr_fact {H' : Host R} (h0 : H.QS = H'.QS) (h1 : H.q = H'.q) (h2 : H.d = H'.d) (h3 : H.pde = H'.pde)
    (h4 : H.pde' = H'.pde') (h5 : Ideal.absNorm H.ccK = Ideal.absNorm H'.ccK) : q0H H = q0H H' := by
  unfold q0H rPrH
  rw [h0, h1, h2, h3, h4, h5]

end Primes

theorem eq_of_from {C : FC} (p : Pt C) {R : Ranks} {H : Host R} {a b : R.A → ℤ} {M : ℕ}
    {c : Fin M → Fin (R.k - 2) → Bool} {u0 : ℕ} (hF : p.From H a b c u0) (h1 : p.D.host.ccK = ⊤) (h2 : H.ccK = ⊤) :
    q0Av p.D = q0H H := by
  have eS : p.D.host.QS = H.QS := hF.QS_eq
  obtain ⟨eR, -, -, eq, ed, -, ep, ep', -⟩ := hF
  subst eR
  exact globalTwisting_congr_fact p.D.host eS eq ed ep ep' (by rw [h1, h2, Ideal.absNorm_top, Ideal.absNorm_top])

theorem auxiliaryPrime_mem_avoidedPrimes (D : D7) : q0Av D ∈ avPrimes D := by
  have h : q0Av D ≠ 0 := (globalTwisting_spec_fact D.host).1.ne_zero
  simp [avPrimes, h]

theorem not_tameDistinct_of_eq_inv {r g m : ℕ} [Fact g.Prime] (χ : Fin m → (ZMod g)ˣ) (j : Fin m) (h : χ j = (χ j)⁻¹) :
    ¬ TameDistinct r g χ := fun hd => by
  have := hd.1 (a₁ := some (j, true)) (a₂ := some (j, false)) h
  simp at this

theorem primeToPart_of_cube {M : Type} [Monoid M] (l : ℕ) (hl : l.Prime) (h3 : l ≠ 3) (x : M) (hx : x ^ 3 = 1) :
    Formalism.CyclotomicNorms.primeToPart l x = x := by
  have hd : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx
  have hf : (orderOf x).factorization l = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    intro h
    exact h3 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_three).1 (h.trans hd))
  unfold Formalism.CyclotomicNorms.primeToPart
  rw [hf]
  rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h
  · rw [orderOf_eq_one_iff.1 h]; simp
  · have e : ∀ n, n = 3 → (((l ^ 0 : ℕ) : ZMod (n / l ^ 0))⁻¹).val = 1 := by
      rintro n rfl
      have e2 : ∀ m, m = 3 → (((1 : ℕ) : ZMod m)⁻¹).val = 1 := by
        rintro m rfl
        decide +kernel
      rw [show ((l ^ 0 : ℕ) : ZMod (3 / l ^ 0)) = ((1 : ℕ) : ZMod (3 / l ^ 0)) by rw [pow_zero l]]
      exact e2 _ (by simp)
    rw [e _ h]; simp

local instance factPrimeSeven : Fact (Nat.Prime 7) := ⟨by norm_num⟩

example : TameDistinct 1 7 (fun _ : Fin 1 => (⟨2, 4, by decide, by decide⟩ : (ZMod 7)ˣ)) := by
  have hinj : Function.Injective (tameList (fun _ : Fin 1 => (⟨2, 4, by decide, by decide⟩ : (ZMod 7)ˣ))) := by decide
  refine ⟨hinj, fun l hl hB => ?_, fun _ => ⟨⟨3, 5, by decide, by decide⟩, Units.ext (by show (2 : ZMod 7) = 3 * 3; decide)⟩⟩
  have h3 : l ≠ 3 := by
    rintro rfl
    apply hB
    right
    refine ⟨1, le_rfl, le_rfl, Nat.prime_three, ?_⟩
    have : padicValNat 3 (7 ^ 1 - 1) = 1 := by
      have : (7 ^ 1 - 1 : ℕ) = 3 * 2 := by norm_num
      rw [this, padicValNat.mul (by norm_num) (by norm_num), padicValNat_self, padicValNat.eq_zero_of_not_dvd (by norm_num)]
    rw [this]; norm_num
  have hc : ∀ o, tameList (fun _ : Fin 1 => (⟨2, 4, by decide, by decide⟩ : (ZMod 7)ˣ)) o ^ 3 = 1 := by decide
  intro a b hab
  simp only at hab
  rw [primeToPart_of_cube l hl h3, primeToPart_of_cube l hl h3] at hab
  · exact hinj (Units.ext ((algebraMap (ZMod 7) (Formalism.CyclotomicNorms.Fbar 7)).injective hab))
  · rw [← map_pow, ← Units.val_pow_eq_pow_val, hc]; simp
  · rw [← map_pow, ← Units.val_pow_eq_pow_val, hc]; simp

example {r g : ℕ} [Fact g.Prime] : ¬ TameDistinct r g (fun _ : Fin 1 => 1) :=
  not_tameDistinct_of_eq_inv _ 0 inv_one.symm

example : minkM 1 = 2 ∧ minkM 2 = 24 ∧ minkM 4 = 5760 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

example {eps : ℝ} (Fm : FamP eps) : ¬ cls (fun _ _ _ _ _ _ _ _ _ => False) Fm := fun h =>
  let ⟨x, _, hx, _, ⟨i⟩⟩ := Fm.exists_pt 0
  classOf_of_cls _ Fm h x hx i

example (C0 : ℝ) (cT : ℝ → ℝ → ℝ) : ¬ DesignChoices (fun _ => False) C0 cT := by
  rintro ⟨e, he, h⟩
  obtain ⟨_, _, _, _, h, _⟩ := h e he le_rfl ⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩
  exact h

end GlobalTheory.EX.DC

end
