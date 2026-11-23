import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
import Formalism.CyclotomicNorms.StatementI
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AutomorphicArithmetic.PrimeDiscriminants.Scales

noncomputable section

namespace GlobalTheory.EX

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab NumberField

structure Pt (C : FC) : Type 1 where
  D : D7
  L : SizeData₂ D
  gatT : GatTies D
  ta : TiesAt C L gatT
  xa : ExtraAt C L gatT ta.Gx ta.Gy

abbrev PtProp : Type 1 :=
  ∀ (D : D7) (L : SizeData₂ D) (gatT : GatTies D) (Gx : G.Inst D L) (Gy : G.LatInst D) (K : G.Consts) (X : DivX D) (cX : ExtraC),
    Extra D L gatT Gx Gy K X cX → Prop

def Pt.Has {C : FC} (p : Pt C) (Q : PtProp) : Prop :=
  Q p.D p.L p.gatT p.ta.Gx p.ta.Gy C.GK p.xa.X C.cX p.xa.ex

def classOf (Q : PtProp) : FamClass := fun Fm =>
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x),
    Q (Fm.D x i) (Fm.L x i) (Fm.gatT x i) (Fm.Gx x i) (Fm.Gy x i) Fm.GK (Fm.X x i) Fm.cX (Fm.ex x hx i)

def Pt.Chosen {C : FC} (p : Pt C) (C5 c6 Cb Cdg : ℝ) : Prop :=
  ThickSetLowerBound p.L ∧ ChBad_at p.ta.Gx Cb ∧ ChQD_at p.D p.L.sc.x p.L.sc.eps C5 ∧ ChThin_at p.D p.L.sc.x p.L.sc.eps c6 ∧
    ChProviso_at p.L 3 ∧ p.L.TuGe ∧
    (∀ u, Real.log ((p.D.mem u).A.T : ℝ) ≤ C.CTu * p.D.R.m * p.L.sc.L) ∧ FactDGam p.D Cdg

def Pt.Same {C : FC} (p p' : Pt C) : Prop :=
  p.D.R = p'.D.R ∧ p.D.host.TT.image Formalism.HC.Frame.A.val = p'.D.host.TT.image Formalism.HC.Frame.A.val ∧ p.D.host.T2 = p'.D.host.T2 ∧
  p.D.host.q = p'.D.host.q ∧ p.D.host.d = p'.D.host.d ∧ p.D.host.g = p'.D.host.g ∧
  p.D.host.pde = p'.D.host.pde ∧ p.D.host.pde' = p'.D.host.pde' ∧
  p.L.etaSz = p'.L.etaSz ∧ p.L.Sc = p'.L.Sc ∧ (∀ l, (G.hP p.D l).val = (G.hP p'.D l).val) ∧
  (∀ (h t : G.HH p.D) (h' t' : G.HH p'.D), h.val = h'.val → t.val = t'.val → (p.ta.Gx.bs h t).val = (p'.ta.Gx.bs h' t').val) ∧
  (∀ j (t : G.HH p.D) (t' : G.HH p'.D), t.val = t'.val → p.ta.Gx.off j (false, t) = p'.ta.Gx.off j (false, t')) ∧
  p.ta.Gx.kapI = p'.ta.Gx.kapI ∧ p.ta.Gx.ep = p'.ta.Gx.ep ∧
  (∀ (t : p.D.host.TT) (t' : p'.D.host.TT), (t : p.D.R.A).val = (t' : p'.D.R.A).val →
    p.L.aT t = p'.L.aT t' ∧ p.L.bT t = p'.L.bT t') ∧
  p.D.host.QS = p'.D.host.QS ∧ artNum p.D.host.toHostRaw = artNum p'.D.host.toHostRaw ∧ p.D.host.rdE = p'.D.host.rdE

structure Kit (C : FC) (cD ch : ℝ) (s : Scale) : Type 1 where
  Ix : Type
  ne : Nonempty Ix
  pt : Ix → Pt C
  sc_eq : ∀ i, (pt i).L.sc = s
  val : ∀ i, Val C cD ch (pt i).L
  arith : ∀ i, HostArith (pt i).D.host
  same : ∀ i i', (pt i).Same (pt i')
  W : Type
  eW : ∀ i, (pt i).D.what₂.Word ≃ W
  eW_code : ∀ i i' u u', eW i u = eW i' u' → wordBits (pt i).D u = wordBits (pt i').D u'
  cover : ∀ i0 (u0 : ℕ), u0 < (pt i0).D.R.n → ∃ i, (pt i).D.host.u0.val = u0

def KitExW (la : ℝ) (Q : PtProp) : Prop :=
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ eps : ℝ, 0 < eps → eps ≤ ε0 → eps < 1 / 52 → ∃ (CT2 C8 : ℝ) (K0 : TransportedAlt), 1 ≤ C8 ∧
    ∀ C : FC, Std C → C.CT2 = CT2 → C.P.Cpde = C8 → C.Large K0 C.P.CF → ∃ c1 : ℝ, ∀ cD ≥ c1, ∃ c2 : ℝ, ∀ ch ≥ c2,
      ∃ C5 c6 Cb Cdg x0 : ℝ, 0 < C5 ∧ 0 < c6 ∧ 0 < Cb ∧ ∃ S : Scales la, ∀ s : Scale, s.eps = eps → x0 ≤ s.x → S.Mem s →
        ∃ k : Kit C cD ch s, ∀ i, (k.pt i).Has Q ∧ (k.pt i).Chosen C5 c6 Cb Cdg

def KitEx (Q : PtProp) : Prop := ∃ la : ℝ, 1 < la ∧ KitExW la Q

def PtProp.and (Q Q' : PtProp) : PtProp := fun D L gatT Gx Gy K X cX ex =>
  Q D L gatT Gx Gy K X cX ex ∧ Q' D L gatT Gx Gy K X cX ex

def BoxesW (D : D7) (s : Scale) : Prop := ∃ Y : ℝ, PairWin s Y ∧ Boxes_at D Y s.eps ∧ GlobalTheoryTheory.BoxE D Y s.eps

def QDRowsW (D : D7) (s : Scale) : Prop := ∃ Y : ℝ, PairWin s Y ∧ QDRows_at D Y s.eps

def BoxesWF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ Y : ℝ, (x ^ (1 / Fm.J) ≤ Y ∧ Y ≤ x) ∧
    Boxes_at (Fm.D x i) Y eps ∧ GlobalTheoryTheory.BoxE (Fm.D x i) Y eps

def QDRowsWF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ Y : ℝ, (x ^ (1 / Fm.J) ≤ Y ∧ Y ≤ x) ∧ QDRows_at (Fm.D x i) Y eps

def ReqPt : PtProp := fun D L _ Gx _ K _ _ _ =>
  AuxBlock8.admW D L Gx K ∧ BoxesW D L.sc ∧ QDRowsW D L.sc

def PrimePt : PtProp := fun D L _ _ _ _ _ _ _ =>
  4 * D.host.Lw * D.host.T2.card ≤ D.R.n0 ∧
  (∀ i, ∃ π : 𝓞 D.host.E, (π : D.host.E) ∈ D.host.K ∧ (π : D.host.E) * D.host.conj (π : D.host.E) = (D.host.g i : D.host.E) ∧
    (π - 1) ∈ Ideal.span {((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E)}) ∧
  (D.host.pde % Nat.lcm 15 (D.host.QS * D.host.q * D.host.d) = 1 ∧ D.host.pde' % Nat.lcm 15 (D.host.QS * D.host.q * D.host.d) = 1) ∧
  ∃ q0 ∈ D.host.levelPrimes, q0.Prime ∧ q0 % (D.host.QS * D.host.q * D.host.d) = 1 ∧ Real.log q0 ≤ L.sc.L ∧ (q0 : ℝ) < L.sc.X' ∧
    q0 ≠ D.host.pde ∧ q0 ≠ D.host.pde' ∧ ∀ i, q0 ≠ D.host.g i

def TwPt : PtProp := fun D _ _ _ _ _ _ _ ex => LocalQuadraticParts.TWAt D ex.nch ex.xd

def AllReq : PtProp := ReqPt.and (PrimePt.and TwPt)

def ExFull (Q : PtProp) : Prop := KitEx (Q.and AllReq)

theorem Pt.has_and {C : FC} (p : Pt C) (Q Q' : PtProp) : p.Has (Q.and Q') ↔ p.Has Q ∧ p.Has Q' := Iff.rfl

theorem classOf_and (Q Q' : PtProp) {eps : ℝ} (Fm : FamP eps) : classOf (Q.and Q') Fm ↔ classOf Q Fm ∧ classOf Q' Fm :=
  ⟨fun h => ⟨fun x hx i => (h x hx i).1, fun x hx i => (h x hx i).2⟩, fun h x hx i => ⟨h.1 x hx i, h.2 x hx i⟩⟩

theorem KitExW.imp {la : ℝ} {Q Q' : PtProp} (h : KitExW la Q)
    (hQ : ∀ (C : FC) (cD ch : ℝ) (p : Pt C), Val C cD ch p.L → HostArith p.D.host → p.Has Q → p.Has Q') : KitExW la Q' := by
  obtain ⟨ε0, h0, h⟩ := h
  refine ⟨ε0, h0, fun eps h1 h2 h3 => ?_⟩
  obtain ⟨CT2, C8, K0, h8, h⟩ := h eps h1 h2 h3
  refine ⟨CT2, C8, K0, h8, fun C a b c d => ?_⟩
  obtain ⟨c1, h⟩ := h C a b c d
  refine ⟨c1, fun cD hcD => ?_⟩
  obtain ⟨c2, h⟩ := h cD hcD
  refine ⟨c2, fun ch hch => ?_⟩
  obtain ⟨C5, c6, Cb, Cdg, x0, p5, p6, pb, S, h⟩ := h ch hch
  refine ⟨C5, c6, Cb, Cdg, x0, p5, p6, pb, S, fun s hs hx hm => ?_⟩
  obtain ⟨k, hk⟩ := h s hs hx hm
  exact ⟨k, fun i => ⟨hQ C cD ch _ (k.val i) (k.arith i) (hk i).1, (hk i).2⟩⟩

theorem KitEx.imp {Q Q' : PtProp} (h : KitEx Q)
    (hQ : ∀ (C : FC) (cD ch : ℝ) (p : Pt C), Val C cD ch p.L → HostArith p.D.host → p.Has Q → p.Has Q') : KitEx Q' :=
  let ⟨la, h1, h⟩ := h
  ⟨la, h1, h.imp hQ⟩

theorem ExFull.kitEx {Q : PtProp} (h : ExFull Q) : KitEx Q := KitEx.imp h fun _ _ _ _ _ _ hp => hp.1

theorem Pt.Same.refl {C : FC} (p : Pt C) : p.Same p := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, ?_, ?_, rfl, rfl, ?_, rfl, rfl, rfl⟩
  · intro h t h' t' e1 e2
    rw [Formalism.HC.Frame.A.val_injective _ e1, Formalism.HC.Frame.A.val_injective _ e2]
  · intro j t t' e
    rw [Formalism.HC.Frame.A.val_injective _ e]
  · intro t t' e
    rw [Subtype.ext (Formalism.HC.Frame.A.val_injective _ e : t.1 = t'.1)]
    exact ⟨rfl, rfl⟩

theorem Pt.Same.weights {C : FC} {p p' : Pt C} (h : p.Same p') (t : p.D.host.TT) (t' : p'.D.host.TT)
    (e : (t : p.D.R.A).val = (t' : p'.D.R.A).val) : p.L.aT t = p'.L.aT t' ∧ p.L.bT t = p'.L.bT t' :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 t t' e

theorem Pt.Same.QS_eq {C : FC} {p p' : Pt C} (h : p.Same p') : p.D.host.QS = p'.D.host.QS :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem Pt.Same.art_eq {C : FC} {p p' : Pt C} (h : p.Same p') :
    artNum p.D.host.toHostRaw = artNum p'.D.host.toHostRaw :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem Pt.Same.rd_eq {C : FC} {p p' : Pt C} (h : p.Same p') : p.D.host.rdE = p'.D.host.rdE :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem Kit.cover_weights {C : FC} {cD ch : ℝ} {s : Scale} (k : Kit C cD ch s) (i0 : k.Ix) (u0 : ℕ)
    (hu : u0 < (k.pt i0).D.R.n) : ∃ i, (k.pt i).D.host.u0.val = u0 ∧
      ∀ (t : (k.pt i).D.host.TT) (t0 : (k.pt i0).D.host.TT),
        (t : (k.pt i).D.R.A).val = (t0 : (k.pt i0).D.R.A).val →
          (k.pt i).L.aT t = (k.pt i0).L.aT t0 ∧ (k.pt i).L.bT t = (k.pt i0).L.bT t0 := by
  obtain ⟨i, hi⟩ := k.cover i0 u0 hu
  exact ⟨i, hi, (k.same i i0).weights⟩

theorem Pt.disjoint_exceptional {C : FC} (p : Pt C) :
    Disjoint (Formalism.CyclotomicNorms.BB p.D.R.r (p.D.host.g 0)) (Formalism.CyclotomicNorms.BB p.D.R.r (p.D.host.g 1)) := p.D.ntypes.BB_disj

theorem Val.qdRows {C : FC} {cD ch : ℝ} {D : D7} {L : SizeData₂ D} (h : Val C cD ch L) : QDRowsW D L.sc := h.host.1

theorem Val.mem_box {C : FC} {cD ch : ℝ} {D : D7} {L : SizeData₂ D} (h : Val C cD ch L) :
    G.aL L ∈ G.box D (G.winA D L.sc) ∧ G.bL L ∈ G.box D (G.winB D C.GK L.sc) := by
  classical
  constructor
  · refine Fintype.mem_piFinset.2 fun t => ?_
    by_cases ht : t ∈ D.host.TT
    · simp only [G.aL, ht, dif_pos, if_true, G.winA, Finset.mem_Icc, Int.ceil_le, Int.le_floor]
      exact L.aT_win ⟨t, ht⟩
    · simp [G.aL, ht]
  · refine Fintype.mem_piFinset.2 fun t => ?_
    by_cases ht : t ∈ D.host.TT
    · simp only [G.bL, ht, dif_pos, if_true, G.winB, Finset.mem_Icc, Int.ceil_le, Int.le_floor, G.Nstar]
      exact ⟨L.bT_ge ⟨t, ht⟩, h.La_eq ▸ h.bT_le ⟨t, ht⟩⟩
    · simp [G.bL, ht]

theorem Pt.has_reqPt_iff {C : FC} {cD ch : ℝ} (p : Pt C) (h : Val C cD ch p.L) :
    p.Has ReqPt ↔ AuxBlock8.WReq p.ta.Gx C.GK (G.aL p.L) (G.bL p.L) ∧ BoxesW p.D p.L.sc :=
  ⟨fun hp => ⟨hp.1.2.2, hp.2.1⟩, fun hp => ⟨⟨h.mem_box.1, h.mem_box.2, hp.1⟩, hp.2, h.qdRows⟩⟩

theorem classOf_reqPt {eps : ℝ} (Fm : FamP eps) (h : classOf ReqPt Fm) :
    (∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, AuxBlock8.admW (Fm.D x i) (Fm.L x i) (Fm.Gx x i) Fm.GK) ∧ BoxesWF Fm ∧ QDRowsWF Fm := by
  refine ⟨fun x hx i => (h x hx i).1, ⟨Fm.x1 + 1, fun x hx i => ?_⟩, ⟨Fm.x1 + 1, fun x hx i => ?_⟩⟩
  · have hx' : Fm.x1 < x := by linarith
    have := (h x hx' i).2.1
    unfold BoxesW PairWin at this
    rwa [Fm.L_x x i hx', Fm.L_eps x i, Fm.L_J x i] at this
  · have hx' : Fm.x1 < x := by linarith
    have := (h x hx' i).2.2
    unfold QDRowsW PairWin at this
    rwa [Fm.L_x x i hx', Fm.L_eps x i, Fm.L_J x i] at this

theorem BoxesWF.boxesF {eps : ℝ} {Fm : FamP eps} (h : BoxesWF Fm) (hJ : Fm.J = 1) : BoxesF Fm := h

theorem QDRowsWF.qdRowsF {eps : ℝ} {Fm : FamP eps} (h : QDRowsWF Fm) (hJ : Fm.J = 1) : QDRowsF Fm := h

theorem boxesWF_iff {eps : ℝ} (Fm : FamP eps) : BoxesWF Fm ↔ BoxesF Fm := Iff.rfl

theorem qdRowsWF_iff {eps : ℝ} (Fm : FamP eps) : QDRowsWF Fm ↔ QDRowsF Fm := Iff.rfl

theorem mod_lcm_of_mod_mul {p N : ℕ} (hN : 0 < N) (h : p % (15 * N) = 1) : p % Nat.lcm 15 N = 1 := by
  have h1 : 1 < Nat.lcm 15 N := lt_of_lt_of_le (by norm_num) (Nat.le_of_dvd (Nat.lcm_pos (by norm_num) hN) (Nat.dvd_lcm_left 15 N))
  rw [← Nat.mod_mod_of_dvd p (Nat.lcm_dvd_mul 15 N), h, Nat.mod_eq_of_lt h1]

theorem mod_of_mod_lcm {p N : ℕ} (hN : 1 < N) (h : p % Nat.lcm 15 N = 1) : p % 15 = 1 ∧ p % N = 1 := by
  constructor
  · rw [← Nat.mod_mod_of_dvd p (Nat.dvd_lcm_left 15 N), h]
  · rw [← Nat.mod_mod_of_dvd p (Nat.dvd_lcm_right 15 N), h, Nat.mod_eq_of_lt hN]

theorem classOf_twPt {eps : ℝ} (Fm : FamP eps) (h : classOf TwPt Fm) : TwGood Fm := ⟨0, fun x _ hx i => h x hx i⟩

example {eps : ℝ} (Fm : FamP eps) : classOf (fun _ _ _ _ _ _ _ _ _ => True) Fm := fun _ _ _ => trivial

example {eps : ℝ} (Fm : FamP eps) : ¬ classOf (fun _ _ _ _ _ _ _ _ _ => False) Fm := fun h => by
  obtain ⟨x, -, hx, -, ⟨i⟩⟩ := Fm.toFamCore.exists_pt 0
  exact h x hx i

example {C : FC} {cD ch : ℝ} {s : Scale} (k : Kit C cD ch s) :
    ∃ i i' : k.Ix, (k.pt i).D.host.u0.val ≠ (k.pt i').D.host.u0.val := by
  obtain ⟨i0⟩ := k.ne
  have h2 : 1 < (k.pt i0).D.R.n := by
    have h1 : 1 < 2 ^ ((k.pt i0).D.R.e + 2) := Nat.one_lt_two_pow (by omega)
    have h3 := (h1.trans_le (Nat.le_of_dvd (k.pt i0).D.host.QS_pos (k.pt i0).D.host.tower_dvd)).trans_le (k.pt i0).D.host.QS_le
    by_contra hn
    have h4 : (k.pt i0).D.R.n ^ 2 ≤ 1 := pow_le_one₀ (Nat.zero_le _) (by omega)
    omega
  obtain ⟨i, hi⟩ := k.cover i0 0 (by omega)
  obtain ⟨i', hi'⟩ := k.cover i0 1 h2
  exact ⟨i, i', by omega⟩

end GlobalTheory.EX

end
