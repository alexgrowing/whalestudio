import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
import Formalism.CyclotomicNorms.StatementI
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DisjointExceptional
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.Analytic
import Development.AutomorphicArithmetic.PrimeDiscriminants.Scales

noncomputable section

namespace GlobalTheory.EX

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.FrobeniusOrbits Formalism.L2.GlobalTheoryTheory NumberField

variable {R : Ranks}

def hPH (H : Host R) (p : ℕ) : R.A :=
  R.iotaInv (Classical.epsilon (fun g => g ∈
    {g : R.GG | ∃ (P : Ideal (𝓞 H.E)) (_ : P.IsPrime) (_ : P.LiesOver (Ideal.span {(p : ℤ)}))
      (σ : H.E ≃ₐ[ℚ] H.E), IsArithFrobAt ℤ σ P ∧ H.galE σ = g})).2

def dlogH (H : Host R) : ℝ :=
  haveI : Fact H.d.Prime := ⟨H.hyp.2.1⟩
  haveI : NeZero H.d := ⟨H.hyp.2.1.ne_zero⟩
  (deriv (DirichletCharacter.LFunction ((quadraticChar (ZMod H.d)).ringHomComp (Int.castRingHom ℂ))) 1 /
    DirichletCharacter.LFunction ((quadraticChar (ZMod H.d)).ringHomComp (Int.castRingHom ℂ)) 1).re

abbrev baseOf (s : Scale) (cD ch : ℝ) (H : Host R) : Arith.Base :=
  { R := R, sc := s, q := H.q, d := H.d, cls := H.cls, TT := H.TT, Sc := (R.k : ℝ) * (4 * (Delv s cD : ℝ)),
    eta := (R.m : ℝ) * (h0v s ch : ℝ) }

open Classical in

def BadOK (s : Scale) (Cb : ℝ) (H : Host R) : Prop :=
  let B := baseOf s 0 0 H
  let PR := (Finset.range ⌈s.X'⌉₊).filter (fun p =>
    p.Prime ∧ B.IsResidueClassZero p ∧ s.x ^ (s.eps / 4) ≤ (addOrderOf (hPH H p) : ℝ))
  ∑ p ∈ PR, Real.log p / p *
      ((H.TT.filter (fun t => ¬ Arith.Loc.Good B (hPH H p) (Arith.bsH (Arith.Loc.stepP B (hPH H p) p) t))).card : ℝ) ≤
    4 * (Cb * s.x ^ (-2 : ℝ)) * s.delta1 * R.n * ∑ p ∈ PR, Real.log p / p

def IsCharH (H : Host R) {N : ℕ} (χ : DirichletCharacter ℂ N) : Prop :=
  χ.IsPrimitive ∧ ∃ ψ : R.GG →* ℂˣ, ∀ (a : ℕ) (h : a.Coprime H.condN),
    χ (a : ZMod N) = ((ψ (H.art (ZMod.unitOfCoprime a h)) : ℂˣ) : ℂ)

theorem isCharH_iff_isCharED (D : D7) {N : ℕ} (χ : DirichletCharacter ℂ N) : IsCharH D.host χ ↔ GlobalTheoryTheory.IsCharED D χ := Iff.rfl

theorem isCharH_iff (H : Host R) {N : ℕ} (χ : DirichletCharacter ℂ N) : IsCharH H χ ↔ H.IsCharE χ := by
  have key : ∀ (ψ : R.GG →* ℂˣ) (a : ℕ) (h : a.Coprime H.condN),
      H.dirAt ψ a = ((ψ (H.art (ZMod.unitOfCoprime a h)) : ℂˣ) : ℂ) := fun ψ a h => by
    rw [← H.dir_unit ψ (ZMod.unitOfCoprime a h), ZMod.coe_unitOfCoprime]
    rfl
  constructor
  · rintro ⟨h1, ψ, h2⟩
    exact ⟨ψ, h1, fun a ha => (h2 a ha).trans (key ψ a ha).symm⟩
  · rintro ⟨ψ, h1, h2⟩
    exact ⟨h1, ψ, fun a ha => (h2 a ha).trans (key ψ a ha)⟩

def ThinOK (s : Scale) (c : ℝ) (H : Host R) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), IsCharH H χ →
    ∀ y : ℝ, Real.exp (s.x ^ (s.eps / 3)) / 3 ≤ y → ‖GlobalTheoryTheory.gChi χ y‖ ≤ y * Real.exp (-(c * s.x ^ (s.eps / 8)))

theorem thinScales_iff_hostBound (s : Scale) (c : ℝ) (H : Host R) : ThinOK s c H ↔ H.ChebyshevCharacterBound s.x s.eps c :=
  forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun χ => imp_congr (isCharH_iff H χ) Iff.rfl

def BoxH (H : Host R) (Y eps : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), IsCharH H χ → GlobalTheoryTheory.IsRealChar χ →
    (H.d ∣ N → GlobalTheoryTheory.GoodFor (8 * ((ordCompl[2] H.QS : ℕ) : ℝ) * GlobalTheoryTheory.X1 Y eps * GlobalTheoryTheory.X2 Y eps) χ) ∧
    (H.q ∣ N → ¬ H.d ∣ N → GlobalTheoryTheory.GoodFor (8 * ((ordCompl[2] H.QS : ℕ) : ℝ) * GlobalTheoryTheory.X1 Y eps) χ)

def BoxW (s : Scale) (H : Host R) : Prop :=
  ∃ Y : ℝ, PairWin s Y ∧ PairRow Y s.eps H ∧ Boxq Y s.eps H.q H.d ∧ BoxH H Y s.eps

theorem BoxW.what₂ {s : Scale} {H : Host R} (h : BoxW s H) : ∃ Y : ℝ, PairWin s Y ∧ PairRow Y s.eps H :=
  let ⟨Y, h1, h2, _⟩ := h
  ⟨Y, h1, h2⟩

theorem BoxW.boxesW {s : Scale} {D : D7} (h : BoxW s D.host) : BoxesW D s :=
  let ⟨Y, h1, _, h3, h4⟩ := h
  ⟨Y, h1, h3, h4⟩

theorem BoxW.qdRowsW {s : Scale} {D : D7} (h : BoxW s D.host) : QDRowsW D s := h.what₂

theorem BoxH.real_ne_zero {H : Host R} {Y eps : ℝ} (h : BoxH H Y eps) {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : IsCharH H χ) (hr : GlobalTheoryTheory.IsRealChar χ) (hN : H.q ∣ N ∨ H.d ∣ N) (β : ℝ) (hβ : 1 - 1 / 400 < β) :
    DirichletCharacter.LFunction χ β ≠ 0 := by
  have key : ∀ Q : ℝ, GlobalTheoryTheory.GoodFor Q χ → DirichletCharacter.LFunction χ β ≠ 0 := fun Q hQ =>
    hQ.2.2.2 β (by simpa using hβ) (by simpa using (Nat.cast_nonneg N).trans hQ.2.2.1)
  by_cases hd : H.d ∣ N
  · exact key _ ((h N χ hχ hr).1 hd)
  · exact key _ ((h N χ hχ hr).2 (hN.resolve_right hd) hd)

theorem BoxW.real_ne_zero {s : Scale} {H : Host R} (h : BoxW s H) {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : H.IsCharE χ) (hr : GlobalTheoryTheory.IsRealChar χ) (hN : H.q ∣ N ∨ H.d ∣ N) (β : ℝ) (hβ : 1 - 1 / 400 < β) :
    DirichletCharacter.LFunction χ β ≠ 0 :=
  let ⟨_, _, _, _, hB⟩ := h
  hB.real_ne_zero χ ((isCharH_iff H χ).2 hχ) hr hN β hβ

def HostGood (s : Scale) (C8 C5 c6 Cb : ℝ) (H : Host R) (q0 : ℕ) : Prop :=
  HostVal s C8 H ∧ HostArith H ∧ H.secondSet_card_lower_bound ∧ 4 * H.Lw * H.T2.card ≤ R.n0 ∧
  QDq s.x s.eps C5 H.q H.d ∧ BoxW s H ∧ |dlogH H| ≤ s.x ^ s.eps ∧ ThinOK s c6 H ∧ BadOK s Cb H ∧
  Disjoint (Formalism.CyclotomicNorms.BB R.r (H.g 0)) (Formalism.CyclotomicNorms.BB R.r (H.g 1)) ∧
  (∀ i, ∃ π : 𝓞 H.E, (π : H.E) ∈ H.K ∧ (π : H.E) * H.conj (π : H.E) = (H.g i : H.E) ∧
    (π - 1) ∈ Ideal.span {((H.QS * H.q * H.d : ℕ) : 𝓞 H.E)}) ∧
  (H.pde % Nat.lcm 15 (H.QS * H.q * H.d) = 1 ∧ H.pde' % Nat.lcm 15 (H.QS * H.q * H.d) = 1) ∧
  (q0.Prime ∧ q0 % (H.QS * H.q * H.d) = 1 ∧ (q0 : ℝ) ≤ ((H.QS : ℝ) * H.q * H.d) ^ C8 ∧ q0 ≠ H.pde ∧ q0 ≠ H.pde') ∧
  H.levelPrimes = {H.g 0, H.g 1, H.pde, H.pde', q0}

private theorem one_lt_modulus (H : Host R) : 1 < H.QS * H.q * H.d :=
  lt_of_lt_of_le H.hyp.2.1.one_lt (Nat.le_mul_of_pos_left _ (Nat.mul_pos H.QS_pos H.hyp.1.pos))

theorem HostGood.pde_mod {s : Scale} {C8 C5 c6 Cb : ℝ} {H : Host R} {q0 : ℕ} (h : HostGood s C8 C5 c6 Cb H q0) :
    H.pde % (H.QS * H.q * H.d) = 1 ∧ H.pde' % (H.QS * H.q * H.d) = 1 :=
  ⟨(mod_of_mod_lcm (one_lt_modulus H) h.2.2.2.2.2.2.2.2.2.2.2.1.1).2, (mod_of_mod_lcm (one_lt_modulus H) h.2.2.2.2.2.2.2.2.2.2.2.1.2).2⟩

abbrev HostReq : Type 1 := ℝ → Scale → ∀ R : Ranks, Host R → ℕ → Prop

def HostExW (la : ℝ) (P : HostReq) : Prop :=
  ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ CT2 C8 C5 c6 Cb x0 : ℝ, 1 ≤ C8 ∧ 0 < C5 ∧ 0 < c6 ∧ 0 < Cb ∧
    ∃ S : Scales la, ∀ s : Scale, s.eps = eps → x0 ≤ s.x → S.Mem s →
      ∃ (R : Ranks) (H : Host R) (q0 : ℕ), RankVal s R ∧ H.CT2 = CT2 ∧ HostGood s C8 C5 c6 Cb H q0 ∧ P C5 s R H q0

def HostExP (P : HostReq) : Prop := ∃ la : ℝ, 1 < la ∧ HostExW la P

def HostEx : Prop := HostExP fun _ _ _ _ _ => True

theorem HostExW.imp {la : ℝ} {P P' : HostReq} (h : HostExW la P) (hP : ∀ c s R H q0, P c s R H q0 → P' c s R H q0) :
    HostExW la P' := by
  intro eps h1 h2
  obtain ⟨CT2, C8, C5, c6, Cb, x0, a1, a2, a3, a4, S, h⟩ := h eps h1 h2
  refine ⟨CT2, C8, C5, c6, Cb, x0, a1, a2, a3, a4, S, fun s b1 b2 b3 => ?_⟩
  obtain ⟨R, H, q0, c1, c2, c3, c4⟩ := h s b1 b2 b3
  exact ⟨R, H, q0, c1, c2, c3, hP _ _ _ _ _ c4⟩

theorem HostExP.imp {P P' : HostReq} (h : HostExP P) (hP : ∀ c s R H q0, P c s R H q0 → P' c s R H q0) : HostExP P' :=
  let ⟨la, h1, h2⟩ := h
  ⟨la, h1, h2.imp hP⟩

theorem HostExP.hostEx {P : HostReq} (h : HostExP P) : HostEx := h.imp fun _ _ _ _ _ _ => trivial

def WinOK (s : Scale) (K : G.Consts) (H : Host R) (a b : R.A → ℤ) : Prop :=
  ∀ t ∈ H.TT, (s.a ≤ (a t : ℝ) ∧ (a t : ℝ) ≤ s.a + s.a / ((R.k : ℝ) * s.x ^ (Scale.A / 2))) ∧
    s.b' ≤ (b t : ℝ) ∧ (b t : ℝ) ≤ s.b' + 2 * (R.n : ℝ) * s.delta1 * s.x ^ s.eps * G.La K s * s.b' / (R.k : ℝ)

open Classical in

def WOK (s : Scale) (cD ch : ℝ) (K : G.Consts) (H : Host R) (a b : R.A → ℤ) : Prop :=
  let B := baseOf s cD ch H
  ∑ p ∈ (Finset.range ⌈s.X'⌉₊).filter (fun p => Arith.Loc.Cand B K (hPH H p) p), Real.log p / p *
      (2 * (if s.x ^ (-s.eps) < Arith.Loc.Sig B (Arith.ins B K 1) K a b (hPH H p) p then (1 : ℝ) else 0) +
        4 * Arith.Loc.Sig B (Arith.ins B K 1) K a b (hPH H p) p) ≤ s.x ^ (-9 : ℝ)

def WeightEx : Prop :=
  ∀ eps C8 : ℝ, 0 < eps → eps < 1 / 52 → ∃ K0 : TransportedAlt, ∀ C : FC, Std C → C.Large K0 C.P.CF → ∀ cD ch : ℝ, 0 ≤ cD → ∃ x0 : ℝ,
    ∀ (s : Scale) (R : Ranks) (H : Host R), s.eps = eps → x0 ≤ s.x → RankVal s R → HostVal s C8 H →
      ∃ a b : R.A → ℤ, (∀ t, t ∉ H.TT → a t = 0 ∧ b t = 0) ∧ WinOK s C.GK H a b ∧ WOK s cD ch C.GK H a b

def Pt.From {C : FC} (p : Pt C) (H : Host R) (a b : R.A → ℤ) {M : ℕ} (c : Fin M → Fin (R.k - 2) → Bool)
    (u0 : ℕ) : Prop :=
  p.D.R = R ∧ p.D.host.TT.image Formalism.HC.Frame.A.val = H.TT.image Formalism.HC.Frame.A.val ∧ p.D.host.T2 = H.T2 ∧ p.D.host.q = H.q ∧ p.D.host.d = H.d ∧
  p.D.host.g = H.g ∧ p.D.host.pde = H.pde ∧ p.D.host.pde' = H.pde' ∧ H.levelPrimes ⊆ p.D.host.levelPrimes ∧
  p.D.host.u0.val = u0 ∧ (∀ l, (G.hP p.D l).val = (hPH H l).val) ∧
  (∀ (t : p.D.host.TT) (t' : R.A), (t : p.D.R.A).val = t'.val → p.L.aT t = a t' ∧ p.L.bT t = b t') ∧
  (∃ eW : p.D.what₂.Word ≃ Fin M, ∀ u l, wordBits p.D u l = if h : l < R.k - 2 then c (eW u) ⟨l, h⟩ else false) ∧
  HEq p.D.host.toHostAx H.toHostAx

section From

variable {C : FC} {p : Pt C} {H : Host R} {a b : R.A → ℤ} {M : ℕ} {c : Fin M → Fin (R.k - 2) → Bool} {u0 : ℕ}

theorem Pt.From.words (h : p.From H a b c u0) :
    ∃ eW : p.D.what₂.Word ≃ Fin M, ∀ u l, wordBits p.D u l = if h : l < R.k - 2 then c (eW u) ⟨l, h⟩ else false :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem Pt.From.field (h : p.From H a b c u0) : HEq p.D.host.toHostAx H.toHostAx := h.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem Pt.From.congr_field (h : p.From H a b c u0) {α : Sort*} (f : ∀ φ : Formalism.HC.Frame, Formalism.HC.HostAx φ → α) :
    f p.D.R.toFrame p.D.host.toHostAx = f R.toFrame H.toHostAx := by
  have h1 := h.1
  have h2 := h.field
  subst h1
  rw [eq_of_heq h2]

theorem Pt.From.QS_eq (h : p.From H a b c u0) : p.D.host.QS = H.QS := h.congr_field fun _ X => X.QS

theorem Pt.From.art_eq (h : p.From H a b c u0) : artNum p.D.host.toHostRaw = artNum H.toHostRaw :=
  h.congr_field fun _ X => artNum X.toHostRaw

theorem Pt.From.rd_eq (h : p.From H a b c u0) : p.D.host.rdE = H.rdE := h.congr_field fun _ X => X.rd

theorem Pt.From.cls_eq (h : p.From H a b c u0) : p.D.host.cls = H.cls :=
  h.congr_field fun _ X => primeClass X.toHostRaw

theorem Pt.From.isCharED_iff (h : p.From H a b c u0) {N : ℕ} (χ : DirichletCharacter ℂ N) :
    GlobalTheoryTheory.IsCharED p.D χ ↔ IsCharH H χ := by
  rw [← isCharH_iff_isCharED, isCharH_iff, isCharH_iff]
  exact iff_of_eq (h.congr_field fun _ X => X.IsCharE χ)

theorem Pt.From.chThin (h : p.From H a b c u0) {s : Scale} {c6 : ℝ} (hT : ThinOK s c6 H) : ChThin_at p.D s.x s.eps c6 :=
  fun N _ χ hχ => hT N χ ((h.isCharED_iff χ).1 hχ)

theorem Pt.From.boxE (h : p.From H a b c u0) {Y eps : ℝ} (hB : BoxH H Y eps) : GlobalTheoryTheory.BoxE p.D Y eps := by
  intro N _ χ hχ hr
  have := hB N χ ((h.isCharED_iff χ).1 hχ) hr
  unfold GlobalTheoryTheory.oddQS
  rw [h.QS_eq, h.2.2.2.1, h.2.2.2.2.1]
  exact this

theorem Pt.From.pairRow (h : p.From H a b c u0) {Y eps : ℝ} (hr : PairRow Y eps H) : PairRow Y eps p.D.host := by
  unfold PairRow
  rw [h.QS_eq, h.2.2.2.1, h.2.2.2.2.1]
  exact hr

theorem Pt.From.boxW (h : p.From H a b c u0) {s : Scale} (hB : BoxW s H) : BoxW s p.D.host := by
  obtain ⟨Y, h1, h2, h3, h4⟩ := hB
  refine ⟨Y, h1, h.pairRow h2, ?_, h.boxE h4⟩
  rw [h.2.2.2.1, h.2.2.2.2.1]
  exact h3

theorem Pt.From.boxesW (h : p.From H a b c u0) {s : Scale} (hB : BoxW s H) : BoxesW p.D s := (h.boxW hB).boxesW

theorem Pt.From.qdRowsW (h : p.From H a b c u0) {s : Scale} (hB : BoxW s H) : QDRowsW p.D s := (h.boxW hB).qdRowsW

end From

def CanonInst {D : D7} {L : SizeData₂ D} (X : G.Inst D L) : Prop :=
  (∀ h t, X.bs h t = Arith.bsH h t) ∧
  ∀ j, j ∉ SizeData₂.lifts D → ∀ t : G.HH D,
    X.off j (false, t) = if t ∈ D.host.TT then L.sc.b' / L.sc.x else L.sc.w'' D.R.n

def ObjEx (Q : PtProp) : Prop :=
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ eps C8 C5 c6 Cb : ℝ, 0 < eps → eps ≤ ε0 → eps < 1 / 52 → 1 ≤ C8 → ∃ K0 : TransportedAlt,
    ∀ C : FC, Std C → C.P.Cpde = C8 → C.Large K0 C.P.CF → ∃ c1 : ℝ, ∀ cD ≥ c1, ∃ c2 : ℝ, ∀ ch ≥ c2, ∃ Cdg x0 : ℝ,
      ∀ (s : Scale) (R : Ranks) (H : Host R) (q0 : ℕ) (a b : R.A → ℤ) (M : ℕ)
        (c : Fin M → Fin (R.k - 2) → Bool) (u0 : ℕ), s.eps = eps → x0 ≤ s.x → RankVal s R → H.CT2 = C.CT2 →
        HostGood s C8 C5 c6 Cb H q0 → WinOK s C.GK H a b →
        M = ⌈3 * Real.exp (C.CGam * (R.m : ℝ) ^ 5 * R.f * s.L) ^ 2 * s.x ^ C.P.CF⌉₊ → Function.Injective c → u0 < R.n →
        ∃ p : Pt C, p.L.sc = s ∧ Val C cD ch p.L ∧ HostArith p.D.host ∧ p.From H a b c u0 ∧ CanonInst p.ta.Gx ∧ p.Has Q ∧
          ChProviso_at p.L 3 ∧ p.L.TuGe ∧ (∀ u, Real.log ((p.D.mem u).A.T : ℝ) ≤ C.CTu * p.D.R.m * p.L.sc.L) ∧
          FactDGam p.D Cdg

def withDuty (Q : PtProp) : PtProp := fun D L gatT Gx Gy K X cX ex =>
  Q D L gatT Gx Gy K X cX ex ∧ Formalism.MainNotions.AuxBlock8.WReq Gx K (G.aL L) (G.bL L) ∧
    BoxesW D L.sc ∧ QDRowsW D L.sc ∧
    ∃ q0 ∈ D.host.levelPrimes, q0.Prime ∧ q0 % (D.host.QS * D.host.q * D.host.d) = 1 ∧ Real.log q0 ≤ L.sc.L ∧ (q0 : ℝ) < L.sc.X' ∧
      q0 ≠ D.host.pde ∧ q0 ≠ D.host.pde' ∧ ∀ i, q0 ≠ D.host.g i

end GlobalTheory.EX

end
