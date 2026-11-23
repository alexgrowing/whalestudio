import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts
import Development.AutomorphicArithmetic.WeightCongruences.ProdNegOneZpow

noncomputable section

namespace GlobalTheory.EX

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab NumberField

def Std (C : FC) : Prop :=
  C.Fixed ∧ C.Cc = 2 ∧ C.P.CLw = 11 * 405 ∧ C.P.Cj0 = 405 ∧ C.P.cw = 9 / 10 ∧ C.P.CYL = 9 ∧ C.P.CccK = 1 ∧
    C.T.Cp = 1 ∧ C.T.eP = 12 ∧ C.T.cTO = 377 ∧ C.CTu = 25 ∧ C.P.CetaF = 6 ∧ 1 ≤ C.P.Cpde ∧ 1000 ≤ C.T.CP ∧
    (∀ c ∈ C.cMid C.P.CF, 1 ≤ c) ∧ ∀ c ∈ C.cLast, 1 ≤ c

def TOv (s : Scale) : ℕ := ⌈s.x ^ (377 : ℝ)⌉₊

def nWv (R : Ranks) (s : Scale) : ℕ :=
  8 * ⌈10 * (R.r : ℝ) * ((R.f : ℝ) + (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2 / R.m) / 8⌉₊

def h0v (s : Scale) (ch : ℝ) : ℕ := 2 * ⌈s.x ^ ch⌉₊

def Delv (s : Scale) (cD : ℝ) : ℕ := ⌈s.x ^ cD⌉₊

def Lwv (s : Scale) : ℕ := 10 * ⌈(405 : ℝ) * Real.log s.x⌉₊ + 2 * ⌈30 / s.eps⌉₊ + 22

def RankVal (s : Scale) (R : Ranks) : Prop :=
  (s.x ^ (2 + 8 * s.eps) ≤ (R.n : ℝ) ∧ (R.n : ℝ) ≤ 2 * s.x ^ (2 + 8 * s.eps)) ∧
  (Real.sqrt (s.x * s.delta1) ≤ (R.m : ℝ) ∧ (R.m : ℝ) ≤ 2 * Real.sqrt (s.x * s.delta1)) ∧
  (s.x ^ (9 / 2 + 10 * s.eps) ≤ (R.k : ℝ) ∧ (R.k : ℝ) ≤ 2 * s.x ^ (9 / 2 + 10 * s.eps)) ∧
  R.r + R.t = 8 * R.f * R.r + 4 + TOv s * nWv R s

namespace RankVal

variable {s : Scale} {R : Ranks}

theorem n_lo (h : RankVal s R) : s.x ^ (2 + 8 * s.eps) ≤ (R.n : ℝ) := h.1.1
theorem n_up (h : RankVal s R) : (R.n : ℝ) ≤ 2 * s.x ^ (2 + 8 * s.eps) := h.1.2

theorem n_le (h : RankVal s R) : (R.n : ℝ) ≤ 2 * s.x ^ (2 + 8 * s.eps + s.eps / 100) := by
  have h2 : s.x ^ (2 + 8 * s.eps) ≤ s.x ^ (2 + 8 * s.eps + s.eps / 100) :=
    Real.rpow_le_rpow_of_exponent_le s.one_lt_alt.le (by linarith [s.eps_pos])
  linarith [h.n_up]

theorem n_le_of_o (h : RankVal s R) {C : ℝ} (hC : (R.o : ℝ) ≤ C) : (R.n : ℝ) ≤ 2 * C * s.x ^ (2 + 8 * s.eps) := by
  have h0 : 0 < R.o := by
    rcases Nat.eq_zero_or_pos R.o with h0 | h0
    · have h1 := R.toFrame.ord_le_o_mul_two_pow
      have h2 := R.toFrame.ord_pos
      rw [h0] at h1
      omega
    · exact h0
  have h1 : (1 : ℝ) ≤ C := le_trans (by exact_mod_cast h0) hC
  have h2 : 0 ≤ s.x ^ (2 + 8 * s.eps) := Real.rpow_nonneg (by linarith [s.one_lt_alt]) _
  nlinarith [h.n_up]

theorem n_le' (h : RankVal s R) : (R.n : ℝ) ≤ 2 * s.x ^ ((9 : ℝ) / 4) := by
  have := s.eps_lt
  have h2 : s.x ^ (2 + 8 * s.eps + s.eps / 100) ≤ s.x ^ ((9 : ℝ) / 4) :=
    Real.rpow_le_rpow_of_exponent_le s.one_lt_alt.le (by linarith)
  linarith [h.n_le]

end RankVal

def PairWin (s : Scale) (Y : ℝ) : Prop := s.x ^ (1 / s.J) ≤ Y ∧ Y ≤ s.x

def PairRow (Y eps : ℝ) {R : Ranks} (H : Host R) : Prop :=
  H.q.Prime ∧ H.q % 8 = 3 ∧ Real.sqrt (GlobalTheoryTheory.X1 Y eps) < H.q ∧ (H.q : ℝ) ≤ GlobalTheoryTheory.X1 Y eps ∧
  H.d.Prime ∧ H.d % 16 = 7 ∧ Real.sqrt (GlobalTheoryTheory.X2 Y eps) < H.d ∧ (H.d : ℝ) ≤ GlobalTheoryTheory.X2 Y eps ∧
  GlobalTheoryTheory.kronSym (-(H.d : ℤ)) H.q = 1 ∧
  (∀ p : ℕ, p.Prime → (p : ℝ) ≤ Y ^ (eps / 5) → GlobalTheoryTheory.kronSym (-(H.d : ℤ)) p = 1) ∧
  Real.log (H.QS * H.q * H.d) ≤ 2 * Y ^ (eps / 5) * Real.log Y ^ 2

def HostConst (s : Scale) (C8 : ℝ) {R : Ranks} (H : Host R) : Prop :=
  s.J ≤ C8 ∧ (R.o : ℝ) ≤ C8 ∧ (H.QS : ℝ) ≤ C8 * R.n

def HostVal (s : Scale) (C8 : ℝ) {R : Ranks} (H : Host R) : Prop :=
  (∃ Y : ℝ, PairWin s Y ∧ PairRow Y s.eps H) ∧
  (s.delta1 * R.n / 2 ≤ (H.TT.card : ℝ) ∧ (H.TT.card : ℝ) ≤ 2 * s.delta1 * R.n) ∧
  s.x ^ (-s.eps) * R.n ≤ (H.T2.card : ℝ) ∧
  ((H.pde : ℝ) ≤ ((H.QS : ℝ) * H.q * H.d) ^ C8 ∧ (H.pde' : ℝ) ≤ ((H.QS : ℝ) * H.q * H.d) ^ C8) ∧
  (∀ i, ((R.k : ℝ) * s.b) ^ 8 ≤ (H.g i : ℝ) ∧ (H.g i : ℝ) ≤ 2 * ((R.k : ℝ) * s.b) ^ 8) ∧
  H.Lw = Lwv s ∧ H.ccK = ⊤ ∧ ⌊s.x ^ (s.ez / 5)⌋₊ ≤ H.splitBound ∧ HostConst s C8 H

def HostArith {R : Ranks} (H : Host R) : Prop :=
  (∀ i, ∃ π : 𝓞 H.E, (π : H.E) ∈ H.K ∧ (π : H.E) * H.conj (π : H.E) = (H.g i : H.E)) ∧
  (∀ i, H.g i % (H.QS * H.q * H.d) = 1) ∧
  ((Ideal.primesOver (Ideal.span {(H.pde : ℤ)}) (𝓞 H.E)).ncard = Module.finrank ℚ H.E ∧
    (Ideal.primesOver (Ideal.span {(H.pde' : ℤ)}) (𝓞 H.E)).ncard = Module.finrank ℚ H.E) ∧
  ∀ p ∈ H.levelPrimes, H.cls p = .splitK

def HCVal (s : Scale) (cD ch : ℝ) {R : Ranks} (H : Host R) {Tau : Type} [Fintype Tau]
    (eTau : Tau → R.GG) (hc : Tau → HCParam R) (bT : H.TT → ℤ) : Prop :=
  (∀ τ (i : Fin (R.k - 1)), (hc τ).v i = ((R.k - 2 - i.1 : ℕ) : ℚ) * (4 * (Delv s cD : ℚ))) ∧
  (∀ τ (hk : 0 < R.k), eTau τ ∉ H.topPlaces →
    (hc τ).u ⟨0, hk⟩ = ((R.k - 2 : ℕ) : ℚ) * (4 * (Delv s cD : ℚ)) + (R.k : ℚ) * (4 * (Delv s cD : ℚ)) + 1 / 2 ∧
    (hc τ).u ⟨R.k - 1, by omega⟩ = -1 / 2) ∧
  (∃ b1 : Tau → ℤ,
    (∀ τ (j : Fin R.m), (hc τ).b j = (b1 τ : ℚ) + (j.1 : ℚ) * (h0v s ch : ℚ) ∧
      (hc τ).e j = (hc τ).b j + (h0v s ch : ℚ) / 2) ∧
    (∀ τ (t : H.TT), eTau τ = R.tau1 t → b1 τ = bT t + ⌊s.b' / s.x⌋) ∧
    (∀ τ, eTau τ ∈ H.thickPlaces → ⌈s.b⌉ ≤ b1 τ ∧ b1 τ < ⌈s.b⌉ + (NumberField.Units.torsionOrder H.E : ℤ)) ∧
    (∀ τ, H.IsThin (eTau τ) → b1 τ = ⌈s.w'' R.n⌉)) ∧
  ∀ j : Fin R.m, UpperTheory.MUQ (fun τ => H.emb (eTau τ)) (fun τ => (hc τ).e j)

structure Val (C : FC) (cD ch : ℝ) {D : D7} (L : SizeData₂ D) : Prop where
  ranks : RankVal L.sc D.R
  host : HostVal L.sc C.P.Cpde D.host
  hc : HCVal L.sc cD ch D.host (fun τ => (D.eTau τ : D.R.GG)) D.hc L.bT
  dlog : |L.logDerivativeAtOne| ≤ L.sc.x ^ L.sc.eps
  Del_eq : D.s.Del = (Delv L.sc cD : ℚ)
  eta_eq : L.etaSz = (D.R.m : ℝ) * (h0v L.sc ch : ℝ)
  La_eq : L.LaG = G.La C.GK L.sc
  bT_le : ∀ t, (L.bT t : ℝ) ≤ L.sc.b' + 2 * (D.R.n : ℝ) * L.sc.delta1 * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / (D.R.k : ℝ)
  logFiveDepth_eq : L.j0 = ⌈Real.logb 5 ((D.R.n : ℝ) * D.R.N D.R.m / D.R.m)⌉₊
  Ct_eq : L.Ct = C.Ct
  Cc_eq : L.Cc = C.Cc
  CGam_eq : L.CGam = C.CGam
  secondConstant_eq : D.host.CT2 = C.CT2
  words : Fintype.card D.what₂.Word = ⌈3 * GamL L ^ 2 * L.sc.x ^ C.P.CF⌉₊
  etaF_eq : D.div.etaF = 6 * L.sc.x ^ (-C.P.CF)

def SzRow (P : FC → ∀ D : D7, SizeData₂ D → Prop) : Prop :=
  ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∀ C : FC, Std C → ∃ c1 : ℝ, ∀ cD ≥ c1, ∃ c2 : ℝ, ∀ ch ≥ c2, ∃ x0 : ℝ,
    ∀ (D : D7) (L : SizeData₂ D), L.sc.eps = eps → x0 ≤ L.sc.x → Val C cD ch L → P C D L

theorem pairWin_self (s : Scale) : PairWin s s.x := by
  refine ⟨?_, le_rfl⟩
  have h : 1 / s.J ≤ 1 := (div_le_one (lt_of_lt_of_le one_pos s.one_le_J)).2 s.one_le_J
  simpa using Real.rpow_le_rpow_of_exponent_le s.one_lt_alt.le h

theorem PairWin.one_lt {s : Scale} {Y : ℝ} (h : PairWin s Y) : 1 < Y :=
  (Real.one_lt_rpow s.one_lt_alt (one_div_pos.2 (lt_of_lt_of_le one_pos s.one_le_J))).trans_le h.1

theorem PairWin.rpow_ez_le {s : Scale} {Y : ℝ} (h : PairWin s Y) {c : ℝ} (hc : 0 < c) :
    s.x ^ (s.ez / c) ≤ Y ^ (s.eps / c) := by
  have hx : 0 < s.x := lt_trans one_pos s.one_lt_alt
  have e : s.ez / c = 1 / s.J * (s.eps / c) := by unfold Scale.ez; ring
  rw [e, Real.rpow_mul hx.le]
  exact Real.rpow_le_rpow (Real.rpow_nonneg hx.le _) h.1 (div_nonneg s.eps_pos.le hc.le)

theorem PairWin.rpow_le {s : Scale} {Y : ℝ} (h : PairWin s Y) {a : ℝ} (ha : 0 ≤ a) : Y ^ a ≤ s.x ^ a :=
  Real.rpow_le_rpow (by linarith [h.one_lt]) h.2 ha

theorem PairWin.log_le {s : Scale} {Y : ℝ} (h : PairWin s Y) : Real.log Y ≤ Real.log s.x :=
  Real.log_le_log (by linarith [h.one_lt]) h.2

theorem PairWin.log_div_le {s : Scale} {Y : ℝ} (h : PairWin s Y) : Real.log s.x / s.J ≤ Real.log Y := by
  have hx : 0 < s.x := lt_trans one_pos s.one_lt_alt
  have h1 := Real.log_le_log (Real.rpow_pos_of_pos hx _) h.1
  rw [Real.log_rpow hx] at h1
  calc Real.log s.x / s.J = 1 / s.J * Real.log s.x := by ring
    _ ≤ _ := h1

theorem PairWin.rpow_inv_le {s : Scale} {Y C : ℝ} (h : PairWin s Y) (hJ : s.J ≤ C) : s.x ^ (1 / C) ≤ Y :=
  (Real.rpow_le_rpow_of_exponent_le s.one_lt_alt.le
    (one_div_le_one_div_of_le (lt_of_lt_of_le one_pos s.one_le_J) hJ)).trans h.1

theorem PairWin.z_log_sq_le {s : Scale} {Y : ℝ} (h : PairWin s Y) :
    Y ^ (s.eps / 5) * Real.log Y ^ 2 ≤ s.x ^ (s.eps / 5) * Real.log s.x ^ 2 := by
  have h0 : 0 ≤ Real.log Y := Real.log_nonneg h.one_lt.le
  have h1 := h.rpow_le (a := s.eps / 5) (by linarith [s.eps_pos])
  exact mul_le_mul h1 (pow_le_pow_left₀ h0 h.log_le 2) (sq_nonneg _)
    (Real.rpow_nonneg (by linarith [s.one_lt_alt]) _)

theorem four_mul_QS_div {R : Ranks} (H : Host R) : 4 * (H.QS / 4) = H.QS :=
  Nat.mul_div_cancel' (Dvd.dvd.trans ⟨2 ^ R.e, by ring⟩ H.tower_dvd)

theorem pairRow_iff_rowq (Y eps : ℝ) {R : Ranks} (H : Host R) : PairRow Y eps H ↔ Rowq Y eps (H.QS / 4) H.q H.d := by
  have e : (4 : ℝ) * ((H.QS / 4 : ℕ) : ℝ) = H.QS := by exact_mod_cast four_mul_QS_div H
  unfold PairRow Rowq
  rw [e]

namespace HostVal

variable {s : Scale} {C8 : ℝ} {R : Ranks} {H : Host R}

theorem split_tie (h : HostVal s C8 H) : ⌊s.x ^ (s.ez / 5)⌋₊ ≤ H.splitBound := h.2.2.2.2.2.2.2.1

theorem J_le (h : HostVal s C8 H) : s.J ≤ C8 := h.2.2.2.2.2.2.2.2.1

theorem o_le (h : HostVal s C8 H) : (R.o : ℝ) ≤ C8 := h.2.2.2.2.2.2.2.2.2.1

theorem QS_le (h : HostVal s C8 H) : (H.QS : ℝ) ≤ C8 * R.n := h.2.2.2.2.2.2.2.2.2.2

theorem one_le (h : HostVal s C8 H) : 1 ≤ C8 := s.one_le_J.trans h.J_le

theorem eps_div_le_ez (h : HostVal s C8 H) : s.eps / C8 ≤ s.ez :=
  div_le_div_of_nonneg_left s.eps_pos.le (lt_of_lt_of_le one_pos s.one_le_J) h.J_le

theorem log_cond_le (h : HostVal s C8 H) :
    Real.log ((H.QS : ℝ) * H.q * H.d) ≤ 2 * s.x ^ (s.eps / 5) * Real.log s.x ^ 2 := by
  obtain ⟨Y, hY, hr⟩ := h.1
  have := hY.z_log_sq_le
  linarith [hr.2.2.2.2.2.2.2.2.2.2]

theorem d_le (h : HostVal s C8 H) : (H.d : ℝ) ≤ GlobalTheoryTheory.X2 s.x s.eps := by
  obtain ⟨Y, hY, hr⟩ := h.1
  exact hr.2.2.2.2.2.2.2.1.trans (Real.exp_le_exp.2 hY.z_log_sq_le)

theorem split (h : HostVal s C8 H) (p : ℕ) (hp : p.Prime) (hle : (p : ℝ) ≤ s.x ^ (s.ez / 5)) :
    GlobalTheoryTheory.kronSym (-(H.d : ℤ)) p = 1 := by
  obtain ⟨Y, hY, hr⟩ := h.1
  exact hr.2.2.2.2.2.2.2.2.2.1 p hp (hle.trans (hY.rpow_ez_le (by norm_num)))

theorem mono (h : HostVal s C8 H) {C8' : ℝ} (hC : C8 ≤ C8') : HostVal s C8' H := by
  have hN : (1 : ℝ) ≤ (H.QS : ℝ) * H.q * H.d := by
    have : 0 < H.QS * H.q * H.d := Nat.mul_pos (Nat.mul_pos H.QS_pos H.hyp.1.pos) H.hyp.2.1.pos
    exact_mod_cast this
  have m := Real.rpow_le_rpow_of_exponent_le hN hC
  obtain ⟨a, b, c, ⟨d1, d2⟩, e, f, g, i, j1, j2, j3⟩ := h
  exact ⟨a, b, c, ⟨d1.trans m, d2.trans m⟩, e, f, g, i, j1.trans hC, j2.trans hC,
    j3.trans (mul_le_mul_of_nonneg_right hC (Nat.cast_nonneg _))⟩

end HostVal

end GlobalTheory.EX

end
