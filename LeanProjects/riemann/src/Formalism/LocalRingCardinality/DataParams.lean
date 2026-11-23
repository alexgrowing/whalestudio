import Formalism.LocalRingCardinality.DataParams₂

noncomputable section

namespace Formalism.BasicNotions

open NumberField

namespace LevelStarExponents

def jG : ℕ := 5

def hExp (s : Scale) : ℝ := ((jG : ℝ) - 1) / 2 + 8 * s.eps

def KG (s : Scale) : ℕ := ⌈8 * (hExp s + 2) / s.eps⌉₊

def rG (s : Scale) : ℕ := KG s + 1

def Av5 (s : Scale) : ℝ := max 26 (4 * hExp s + 9)

theorem Av5_eq (s : Scale) : Av5 s = Scale.A := by
  unfold Av5 hExp jG Scale.A
  have h1 := s.eps_lt
  rw [max_eq_left]
  push_cast
  linarith

variable {D : D7} (L : SizeData₂ D)

def Nstar : ℝ := 2 * (D.R.n : ℝ) * L.sc.delta1

def R0 : ℝ := (D.R.n : ℝ) * L.sc.x ^ (-L.sc.eps)

def condE (D : D7) : ℕ := D.host.QS * D.host.q * D.host.d

def lA : ℝ := (D.R.k : ℝ) * L.sc.x ^ L.sc.eps / ((D.R.m : ℝ) * L.de2)

def lStar : ℝ :=
  (D.R.m : ℝ) * L.sc.b / ((D.R.n : ℝ) * (D.R.t : ℝ) ^ 2 * ((D.R.N D.R.m : ℝ) + D.R.t) * L.sc.L ^ 2 +
    (D.R.k : ℝ) * (D.R.n : ℝ) ^ 2 * (L.Sc + D.R.t + L.sc.L))

def h0 : ℝ := L.etaSz / D.R.m

def qSig (D : D7) : ℕ := D.R.m

def Mrt (D : D7) : ℕ := D.R.r + D.R.m * D.R.t

def nW (C : ℝ) : ℝ :=
  C * D.R.r * ((D.R.f : ℝ) + (D.R.f : ℝ) ^ 2 * ((D.R.k : ℝ) - 1) ^ 3 * L.sc.L ^ 2 / D.R.m)

def rhoP (C : ℝ) : ℝ :=
  4 * Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k + C * Real.log L.sc.x * L.LaG / D.R.k

def sgS (D : D7) : ℝ := D.what₂.Dstar / (∑ u : D.what₂.Word, (D.duS u : ℝ))

def gapS (D : D7) (C : ℝ) : ℝ := C * D.R.k * (D.R.m : ℝ) ^ 4 + (D.R.N D.R.m : ℝ) * (D.R.m : ℝ) ^ 10

end LevelStarExponents

open LevelStarExponents

structure ParameterChoice' (D : D7) (L : SizeData₂ D) : Type where

  CkLow : ℝ
  CkLow_pos : 0 < CkLow

  Ck6 : ℝ
  Ck6_pos : 0 < Ck6

  CfL : ℝ
  CfL_pos : 0 < CfL

  cLL : ℝ
  cLL_pos : 0 < cLL

  CnW : ℝ
  CnW_pos : 0 < CnW

  Crho : ℝ
  Crho_pos : 0 < Crho

  CDelG : ℝ
  CDelG_pos : 0 < CDelG

  CLw : ℝ
  CLw_pos : 0 < CLw

  Cj0 : ℝ
  Cj0_pos : 0 < Cj0

  Cw : ℝ
  Cw_pos : 0 < Cw
  cw : ℝ
  cw_pos : 0 < cw

  CDel : ℝ
  CDel_pos : 0 < CDel

  CCount : ℝ
  CCount_pos : 0 < CCount

  Ch0r : ℝ
  Ch0r_pos : 0 < Ch0r

  Ch0k : ℝ
  Ch0k_pos : 0 < Ch0k

  Ch0N : ℝ
  Ch0N_pos : 0 < Ch0N

  Cgap : ℝ
  Cgap_pos : 0 < Cgap

  CetaF : ℝ
  CetaF_pos : 0 < CetaF

  CF : ℝ
  CF_pos : 0 < CF

  CY : ℝ
  CY_pos : 0 < CY
  CYL : ℝ
  CYL_pos : 0 < CYL

  Cpde : ℝ
  Cpde_pos : 0 < Cpde

  CccK : ℝ
  CccK_pos : 0 < CccK

  qd_pow : L.sc.x ^ (2 * L.Ct + 5) < (D.host.q : ℝ) ∧ L.sc.x ^ (2 * L.Ct + 5) < (D.host.d : ℝ)

  logq_ge : L.sc.x ^ (L.sc.ez / 6) ≤ Real.log D.host.q

  logDerivative_le_power : |L.logDerivativeAtOne| ≤ L.sc.x ^ L.sc.eps

  k_low : CkLow * (D.R.m : ℝ) ^ jG * D.R.f * L.sc.L * L.sc.x ^ L.sc.eps ≤ D.R.k

  k_up : (D.R.k : ℝ) ≤ L.sc.x ^ ((1 : ℝ) / 2) * D.R.n * R0 L

  radius_ge_sqrt_ratio : Real.sqrt ((D.R.k : ℝ) / D.R.m) ≤ R0 L

  k_ge_m2L : (D.R.m : ℝ) ^ 2 * L.sc.L ≤ D.R.k

  k_ge_mx : (D.R.m : ℝ) * L.sc.x ^ ((1 : ℝ) / 2) * Real.log L.sc.x ≤ D.R.k

  klogk : Ck6 * (D.R.m : ℝ) ^ 6 * L.sc.L ≤ (D.R.k : ℝ) * Real.log D.R.k

  logf_le : Real.log D.R.f ≤ Real.sqrt D.R.rS

  log_sq_conductor_le : Real.log D.R.f ^ 2 ≤ (D.R.m : ℝ) ^ 2 * L.sc.L

  loglogb : Real.log (Real.log L.sc.b) ≤ cLL * D.R.r * D.R.f * Real.log D.R.r

  flogk : CfL * L.sc.L ≤ (D.R.f : ℝ) * Real.log D.R.k

  eta_le : L.etaSz ≤ L.sc.b / ((D.R.t : ℝ) ^ 3 * D.R.f * (D.R.k : ℝ) ^ 3)

  condE_le : (condE D : ℝ) ^ 36 * (D.R.t : ℝ) ^ 150 ≤ L.sc.b ^ ((1 : ℝ) / 2)

  TT_card_le : (D.host.TT.card : ℝ) ≤ Nstar L

  rho_le : rhoP L Crho ≤ L.sc.x ^ (-2 : ℝ)

  S_le : 4 * L.Sc ≤ L.LaG * L.sc.b' / D.R.k

  Del_le : 4 * CDelG * (D.R.k : ℝ) ^ 2 * (D.s.Del : ℝ) ≤ L.LaG * L.sc.b'

  Lw_j : ∀ l : ℕ, 11 ≤ l → ∃ j : ℕ, lA L ≤ ((l : ℝ) - 1) ^ j ∧ 2 * j + 2 ≤ D.host.Lw

  Lw_le : (D.host.Lw : ℝ) ≤ CLw * Real.log L.sc.x

  jetIndex_le_log : (L.j0 : ℝ) ≤ Cj0 * Real.log L.sc.x

  bT_le : ∀ t, (L.bT t : ℝ) ≤ L.sc.b' + Nstar L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k

  topPlace_first_bound : ∀ τ (t : D.host.TT) (hm : 0 < D.R.m),
    (D.eTau τ : D.R.GG) = D.R.tau1 t →
    (((D.hc τ).b ⟨0, hm⟩ : ℚ) : ℝ) = (L.bT t : ℝ) + (⌊L.sc.b' / L.sc.x⌋ : ℤ)

  lows_far : ∀ τ (i j : Fin D.R.m),
    2 * L.sc.b / lStar L + (D.R.t : ℝ) / 2 + 3 ≤ |(((D.hc τ).b i - (D.hc τ).e j : ℚ) : ℝ)|

  X''_ratio : ∀ j j' τ τ', 1 ≤ j → j ≤ D.R.m → 1 ≤ j' → j' ≤ D.R.m →
    wj D j τ ≤ L.sc.X'' D.R.n * wj D j' τ'

  cloud_place_bound : ∀ τ (h0 : 0 < D.R.k - 1), (D.eTau τ : D.R.GG) ∉ D.host.topPlaces →
    (((D.hc τ).u ⟨0, by omega⟩ - (D.hc τ).v ⟨0, h0⟩ : ℚ) : ℝ) ≤ 2 * L.Sc

  uk_extreme : ∀ τ (hk : 2 ≤ D.R.k), (D.eTau τ : D.R.GG) ∉ D.host.topPlaces →
    (D.hc τ).u ⟨D.R.k - 1, by omega⟩ = (D.hc τ).v ⟨D.R.k - 2, by omega⟩ - 1 / 2

  w''_ge : (D.R.k : ℝ) ^ Cw ≤ L.sc.w'' D.R.n ∧ L.sc.b ^ cw ≤ L.sc.w'' D.R.n

  Del_ge : (D.R.k : ℝ) ^ CDel * (CDel * D.R.m) ^ 3 / D.div.etaF ^ CDel ≤ (D.s.Del : ℝ) ∧
    CDel * D.R.m * D.R.N D.R.m ≤ (D.s.Del : ℝ) ∧
    (D.R.k : ℝ) ^ CDel * (CDel * (D.R.m : ℝ) ^ 4 * L.sc.L) ^ 4 ≤ (D.s.Del : ℝ) ∧
    (D.R.N D.R.m : ℝ) * (D.R.m : ℝ) ^ 10 ≤ (D.s.Del : ℝ)

  Del_count : ((D.R.N D.R.m : ℝ) * D.R.f * L.sc.L) ^ CCount ≤ (D.s.Del : ℝ)

  logDel : Real.log (D.s.Del : ℝ) ≤ L.sc.x ^ (L.sc.eps / 4) / 2

  kS_le : (D.R.k : ℝ) * L.Sc ≤ L.sc.w'' D.R.n

  bm_le : ∀ τ (hm : 0 < D.R.m), (D.hc τ).b ⟨D.R.m - 1, by omega⟩ ≤ 2 * (D.hc τ).b ⟨0, hm⟩

  h0_ge : 12 * L.sc.b / lStar L + 2 * D.R.t + 8 ≤ h0 L ∧
    (D.R.k : ℝ) * D.R.t * L.sc.L ≤ h0 L ∧
    Ch0r * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L.sc.L ≤ h0 L ∧
    ((D.R.N D.R.m : ℝ) * D.R.f * L.sc.L) ^ CCount ≤ h0 L ∧
    4 * (D.R.N D.R.m : ℝ) ^ 3 + 2 * D.R.t + 6 ≤ h0 L ∧
    Ch0k * D.R.k * (D.R.m : ℝ) ^ ((9 : ℝ) / 2) ≤ h0 L ∧
    2 * (Mrt D : ℝ) ^ 3 + D.R.t + 3 ≤ h0 L ∧
    120 * (D.R.r : ℝ) * (qSig D : ℝ) ^ ((3 : ℝ) / 2) ≤ h0 L ∧
    (D.R.N D.R.m : ℝ) * (D.R.m : ℝ) ^ 10 ≤ h0 L ∧
    16 * (qSig D : ℝ) * D.R.N D.R.m ≤ h0 L

  heightBound_ge_rank_cubic : (D.R.t : ℝ) + 2 * ((D.R.k : ℝ) + D.R.m * (D.R.t + (D.R.r + 6) + 1)) ^ 3 + 1 ≤ h0 L

  heightBound_ge_degree_power : (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ Ch0N ≤ h0 L

  em_win : ∀ τ (hm : 0 < D.R.m),
    |((((D.hc τ).e ⟨D.R.m - 1, by omega⟩ - (D.hc τ).b ⟨D.R.m - 1, by omega⟩ : ℚ)) : ℝ) - h0 L / 2| ≤ 2

  nodes_gap : ∀ τ (j : ℕ) (h : j + 1 < D.R.m),
    h0 L ≤ (((D.hc τ).b ⟨j + 1, h⟩ - (D.hc τ).b ⟨j, by omega⟩ : ℚ) : ℝ) ∧
    (((D.hc τ).b ⟨j + 1, h⟩ - (D.hc τ).b ⟨j, by omega⟩ : ℚ) : ℝ) ≤ h0 L + 1

  e_centred : ∀ τ (j : Fin D.R.m), |((((D.hc τ).e j - (D.hc τ).b j : ℚ)) : ℝ) - h0 L / 2| ≤ 2

  sig_gaps : ∀ τ,
    (∀ (i : ℕ) (h : i + 1 < D.R.k - 1),
      gapS D Cgap < (((D.hc τ).v ⟨i, by omega⟩ - (D.hc τ).v ⟨i + 1, h⟩ : ℚ) : ℝ)) ∧
    (∀ (hk : 2 ≤ D.R.k) (hm : 0 < D.R.m),
      gapS D Cgap < (((D.hc τ).v ⟨D.R.k - 2, by omega⟩ + (D.hc τ).b ⟨0, hm⟩ : ℚ) : ℝ)) ∧
    (∀ (j : ℕ) (h : j + 1 < D.R.m),
      gapS D Cgap < (((D.hc τ).b ⟨j + 1, h⟩ - (D.hc τ).b ⟨j, by omega⟩ : ℚ) : ℝ))

  nW_ge : (4 * (D.R.f : ℝ) + 10) * D.R.r ≤ nW L CnW

  logeta : Real.log L.etaSz ≤ L.sc.x ^ (L.sc.eps / 4)

  t_le_eta : (D.R.t : ℝ) ≤ L.etaSz

  teta : (D.R.t : ℝ) * L.etaSz ≤ L.sc.w'' D.R.n / L.sc.x

  mteta : (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz ≤ L.sc.w'' D.R.n

  mSeta : (D.R.m : ℝ) * (L.Sc + L.etaSz) ≤ L.sc.w'' D.R.n * L.sc.L

  Neta : (D.R.N D.R.m : ℝ) * L.etaSz ≤ L.de2 * D.R.m * L.sc.w'' D.R.n

  eta2 : L.etaSz ^ 2 * D.R.r * L.sc.L ≤ L.de2 * D.R.m * L.sc.w'' D.R.n ^ 2

  rbS : (D.R.r : ℝ) * (L.sc.b' + L.Sc) * Real.log L.sc.x * lA L ≤ L.de2 * D.R.m * L.sc.b

  lstar1 : L.sc.b' + L.Sc + L.etaSz + L.sc.b / lStar L < lStar L

  lstar2 : 2 * L.etaSz + D.R.t + 8 * L.sc.b / lStar L + 7 < lStar L

  words_le : Fintype.card D.what₂.Word ≤ 2 ^ (D.R.k - 3)

  etaF_eq : D.div.etaF = CetaF * L.sc.x ^ (-CF)

  g_Y : ∃ Y : ℝ, ((D.R.k : ℝ) * L.sc.b) ^ 8 ≤ Y ∧
    (D.R.N D.R.m : ℝ) ^ 4 * (condE D : ℝ) ^ CY ≤ Y ^ ((1 : ℝ) / 4) ∧ Real.log Y ≤ CYL * L.sc.L ∧
    ∀ i, Y ≤ (D.host.g i : ℝ) ∧ (D.host.g i : ℝ) ≤ 2 * Y

  g_norm : ∀ i, ∃ π : 𝓞 D.host.E, (π : D.host.E) ∈ D.host.K ∧
    (π : D.host.E) * D.host.conj (π : D.host.E) = (D.host.g i : D.host.E)

  g_mod : ∀ i, D.host.g i % condE D = 1

  pde_mod : D.host.pde % 15 = 1 ∧ D.host.pde' % 15 = 1

  pde_split : (Ideal.primesOver (Ideal.span {(D.host.pde : ℤ)}) (𝓞 D.host.E)).ncard =
      Module.finrank ℚ D.host.E ∧
    (Ideal.primesOver (Ideal.span {(D.host.pde' : ℤ)}) (𝓞 D.host.E)).ncard = Module.finrank ℚ D.host.E

  pde_ne : ∀ i, D.host.pde ≠ D.host.g i ∧ D.host.pde' ≠ D.host.g i

  pde_log : Real.log D.host.pde ≤ L.sc.L ∧ Real.log D.host.pde' ≤ L.sc.L

  level_split : ∀ p ∈ D.host.levelPrimes, D.host.cls p = .splitK

  ccK_log : Real.log (Ideal.absNorm D.host.ccK) ≤ L.sc.L

  e_mu : ∀ j : Fin D.R.m, D.host.MuCond (fun τ => (D.eTau τ : D.R.GG)) (fun τ => (D.hc τ).e j)

  ccK_le : (Ideal.absNorm D.host.ccK : ℝ) ≤ CccK * D.host.d

namespace ParameterChoice'

variable {D : D7} {L : SizeData₂ D}

def SgWin (P : ParameterChoice' D L) (C0 : ℝ) : Prop :=
  L.sc.x ^ (-P.CF) / C0 ^ 2 ≤ sgS D ∧ sgS D ≤ L.sc.x ^ (-P.CF)

theorem bT_ge_half (P : ParameterChoice' D L) (τ : D.what₂.Tau) (t : D.host.TT) (hm : 0 < D.R.m)
    (ht : (D.eTau τ : D.R.GG) = D.R.tau1 t) :
    (((D.hc τ).b ⟨0, hm⟩ : ℚ) : ℝ) / 2 ≤ (L.bT t : ℝ) := by
  rw [P.topPlace_first_bound τ t hm ht]
  have hb := L.bT_ge t
  have hx : 1 < L.sc.x := L.sc.one_lt_alt
  have hbpos : 0 < L.sc.b' := by
    unfold Scale.b' Scale.a Scale.X' Scale.b
    have : 0 < L.sc.x := by linarith
    positivity
  have hfl : ((⌊L.sc.b' / L.sc.x⌋ : ℤ) : ℝ) ≤ L.sc.b' / L.sc.x := Int.floor_le _
  have hdiv : L.sc.b' / L.sc.x ≤ L.sc.b' := div_le_self hbpos.le hx.le
  linarith

end ParameterChoice'

theorem f_le_m_sq_n (R : Ranks) : R.f ≤ R.m ^ 2 * R.n := by
  unfold Ranks.f
  have h := R.two_le_m
  have : 4 ≤ R.m ^ 2 := by nlinarith
  nlinarith

theorem f_le_r_sq (R : Ranks) : R.f ≤ R.r ^ 2 := by
  have h1 := R.f_le_k
  have h2 := R.two_le_m
  have h3 : R.k ≤ R.r := by unfold Ranks.r; omega
  have h4 : R.r ≤ R.r ^ 2 := Nat.le_self_pow (by norm_num) _
  have h5 : R.f = 2 * R.ord := rfl
  omega

end Formalism.BasicNotions

end
