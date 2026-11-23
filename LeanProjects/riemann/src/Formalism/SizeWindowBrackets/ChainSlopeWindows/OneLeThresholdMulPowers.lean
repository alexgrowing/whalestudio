import Formalism.SizeWindowBrackets.WindowSettingSatisfiable
import Formalism.SizeWindowBrackets.ChainSlopeWindows.AdmissibleSchurLemma

namespace Formalism.LFunctionChainParameters.PrimeWindowSizeBounds

open Finset Classical
open Formalism.LFunctionChainParameters.DeficitSplitLemmas Formalism.LFunctionChainParameters.LErr

structure Facts (P : Par) (e K z u E X S sb v w8 : ℝ) : Prop where
  hx : 100 ≤ P.x
  he : 0 ≤ e
  hK : 1 ≤ K
  z1 : 1 ≤ z
  hz4 : 100 * K * z ^ 4 ≤ P.x
  u1 : 1 ≤ u
  uz : u ≤ z
  E1 : 1 ≤ E
  hXB : 100 * K * (E ^ 4 * P.x ^ 4) ≤ X
  S1 : 1 ≤ S
  hsb : 100 * K * (E ^ 4 * P.x ^ 4) * (X * S) ≤ sb
  hb : P.b = sb * sb
  ha : P.a = P.x * P.b
  hXp : P.Xp = X
  hvX : v * X = P.b
  v0 : 0 ≤ v
  hbp : P.bp = P.x * v
  hwpp : P.wpp = v / P.n
  hXpp : P.Xpp = P.x * P.n * X
  lx0 : 0 ≤ P.lx
  lxz : P.lx ≤ z
  elx : e * P.lx ≤ z
  logX : Real.log X = u
  loga : Real.log P.a = P.lx + z
  nx : P.x ^ 2 ≤ P.n
  n2x : P.x ^ 2 ≤ (2 : ℝ) ^ P.e₂
  n2n : (2 : ℝ) ^ P.e₂ ≤ P.n
  nE : P.n ≤ E
  kx : P.x ^ 2 ≤ P.k
  kE : P.k ≤ E
  N0 : 0 ≤ P.N
  NE : P.N ≤ E
  t0 : 0 ≤ P.t
  tE : P.t ≤ E
  px : P.x ^ 4 + 1 ≤ (P.p₀ : ℝ)
  pE : (P.p₀ : ℝ) ≤ E
  La0 : 0 ≤ P.La
  Laz : P.La ≤ z ^ 2
  r0 : 0 ≤ P.rG
  rE : P.rG ≤ E
  Sc0 : 0 ≤ P.Sc
  ScS : P.Sc ≤ S
  η0 : 0 ≤ P.η
  ηS : P.η ≤ S
  ρ0 : 0 ≤ P.ρ
  ρx : P.ρ ≤ (P.x ^ 2)⁻¹
  th0 : 0 ≤ P.th
  thx : P.th ≤ P.x⁻¹
  x_sq_le_threshold : P.x ^ 2 ≤ P.K₀
  dx : P.x ^ 2 ≤ (P.d : ℝ)
  C0 : 0 ≤ P.C
  CK : P.C ≤ K
  β0 : 0 ≤ P.β
  βK : P.β ≤ K * (P.x ^ 2)⁻¹
  Co0 : 0 ≤ P.Cord
  CoK : P.Cord ≤ K
  Y1 : 1 ≤ P.Y
  YX : P.Y ≤ 2 * X
  s0 : 0 ≤ P.s₀
  sx : P.s₀ ≤ (P.x ^ 2)⁻¹
  bo0 : 0 ≤ P.bo
  bosb : P.bo ≤ sb
  hδ : P.δ₁ = w8⁻¹
  w81 : 1 ≤ w8
  w8z : w8 ≤ z
  hθ : P.θ = z⁻¹
  Joz : (P.Jo : ℝ) ≤ z
  Ibu : (P.Ib : ℝ) ≤ u
  hE : E = P.x ^ e
  hu : u = P.x ^ (P.ε / 3)
  hz : z = P.x ^ P.ε

theorem facts {P : Par} {e K : ℝ} (hW : Windows P e K) (hL : LargeX P.x P.ε e K) :
    ∃ z u E X S sb v w8 : ℝ, Facts P e K z u E X S sb v w8 := by
  obtain ⟨hε, hε1, he, hK, ⟨n2x, n2n⟩, nE, kx, kE, N0, NE, t0, tE, px, pE, La0, Laz, r0, rE, Sc0, ScS, η0, ηS,
    ρ0, ρx, th0, thx, x_sq_le_threshold, dx, C0, CK, β0, βK, Co0, CoK, Y1, YX, s0, sx, bo0, bosb⟩ := hW
  have nx := n2x.trans n2n
  obtain ⟨x1, hC, hB, hA⟩ := hL
  have xpos : 0 < P.x := by linarith
  have e4 : P.x ^ (4 * P.ε) = (P.x ^ P.ε) ^ 4 := by
    rw [mul_comm, Real.rpow_mul xpos.le, Real.rpow_ofNat]
  have e2 : P.x ^ (2 * P.ε) = (P.x ^ P.ε) ^ 2 := by
    rw [mul_comm, Real.rpow_mul xpos.le, Real.rpow_ofNat]
  have eM : P.x ^ (4 * e + 4) = (P.x ^ e) ^ 4 * P.x ^ 4 := by
    rw [Real.rpow_add xpos, mul_comm 4 e, Real.rpow_mul xpos.le, Real.rpow_ofNat, Real.rpow_ofNat]
  rw [e4] at hC
  rw [e2] at Laz
  rw [eM] at hB hA
  rw [Real.exp_add] at hA
  have z1 : 1 ≤ P.x ^ P.ε := Real.one_le_rpow x1 hε.le
  have u1 : 1 ≤ P.x ^ (P.ε / 3) := Real.one_le_rpow x1 (by positivity)
  have E1 : 1 ≤ P.x ^ e := Real.one_le_rpow x1 he
  have z41 : 1 ≤ (P.x ^ P.ε) ^ 4 := one_le_pow₀ z1
  have hx : 100 ≤ P.x := by
    have h1 : 1 ≤ K * (P.x ^ P.ε) ^ 4 := one_le_mul_of_one_le_of_one_le hK z41
    linarith only [h1, hC]
  have hM1 : 1 ≤ (P.x ^ e) ^ 4 * P.x ^ 4 := one_le_mul_of_one_le_of_one_le (one_le_pow₀ E1) (one_le_pow₀ x1)
  have lx0 : 0 ≤ Real.log P.x := Real.log_nonneg x1
  have hlog : Real.log P.x * (4 * e + 4) ≤ P.x ^ (P.ε / 3) := by
    have h1 : P.x ^ (4 * e + 4) ≤ Real.exp (P.x ^ (P.ε / 3)) := by
      rw [eM]
      have h2 : (1 : ℝ) ≤ 100 * K := by linarith only [hK]
      exact (le_mul_of_one_le_left (by linarith only [hM1]) h2).trans hB
    rwa [Real.rpow_def_of_pos xpos, Real.exp_le_exp] at h1
  have uz : P.x ^ (P.ε / 3) ≤ P.x ^ P.ε := Real.rpow_le_rpow_of_exponent_le x1 (by linarith)
  have helx : 0 ≤ e * Real.log P.x := mul_nonneg he lx0
  have hlog' : 4 * (e * Real.log P.x) + 4 * Real.log P.x ≤ P.x ^ (P.ε / 3) := by
    have : Real.log P.x * (4 * e + 4) = 4 * (e * Real.log P.x) + 4 * Real.log P.x := by ring
    linarith only [this, hlog]
  have Xpos : 0 < Real.exp (P.x ^ (P.ε / 3)) := Real.exp_pos _
  have bpos : 0 < Real.exp (P.x ^ P.ε) := Real.exp_pos _
  have npos : 0 < P.n := lt_of_lt_of_le (by positivity) n2n
  refine ⟨P.x ^ P.ε, P.x ^ (P.ε / 3), P.x ^ e, Real.exp (P.x ^ (P.ε / 3)), Real.exp (P.x ^ (P.ε / 4)),
    Real.exp (P.x ^ P.ε / 2), Real.exp (P.x ^ P.ε) / Real.exp (P.x ^ (P.ε / 3)), P.x ^ (P.ε / 8), ?_⟩
  exact
  { hx := hx, he := he, hK := hK, z1 := z1, hz4 := hC, u1 := u1, uz := uz, E1 := E1, hXB := hB
    S1 := Real.one_le_exp (Real.rpow_nonneg xpos.le _)
    hsb := hA
    hb := by
      unfold Par.b bTx
      rw [← Real.exp_add, add_halves]
    ha := by simp only [Par.a, Par.b, aTx]
    hXp := by simp only [Par.Xp, XpTx]
    hvX := by unfold Par.b bTx; field_simp
    v0 := by positivity
    hbp := by unfold Par.bp bpTx aTx bTx XpTx; ring
    hwpp := by
      unfold Par.wpp wppTx bpTx aTx bTx XpTx
      field_simp
    hXpp := by
      unfold Par.Xpp XppTx wppTx bpTx aTx bTx XpTx
      field_simp
    lx0 := lx0
    lxz := by unfold Par.lx; linarith only [hlog', helx, lx0, uz]
    elx := by unfold Par.lx; linarith only [hlog', helx, lx0, uz]
    logX := Real.log_exp _
    loga := by
      unfold Par.a aTx bTx Par.lx
      rw [Real.log_mul xpos.ne' bpos.ne', Real.log_exp]
    nx := nx, n2x := n2x, n2n := n2n, nE := nE, kx := kx, kE := kE, N0 := N0, NE := NE, t0 := t0, tE := tE, px := px, pE := pE
    La0 := La0, Laz := Laz, r0 := r0, rE := rE, Sc0 := Sc0, ScS := ScS, η0 := η0, ηS := ηS, ρ0 := ρ0
    ρx := ρx, th0 := th0, thx := thx, x_sq_le_threshold := x_sq_le_threshold, dx := dx, C0 := C0, CK := CK, β0 := β0, βK := βK
    Co0 := Co0, CoK := CoK, Y1 := Y1, YX := YX, s0 := s0, sx := sx, bo0 := bo0, bosb := bosb
    hδ := by unfold Par.δ₁; rw [Real.rpow_neg xpos.le]
    w81 := Real.one_le_rpow x1 (by positivity)
    w8z := Real.rpow_le_rpow_of_exponent_le x1 (by linarith)
    hθ := by unfold Par.θ; rw [Real.rpow_neg xpos.le]
    Joz := (Nat.floor_le (Real.rpow_nonneg xpos.le _)).trans
      (Real.rpow_le_rpow_of_exponent_le x1 (by linarith))
    Ibu := Nat.floor_le (Real.rpow_nonneg xpos.le _)
    hE := rfl
    hu := rfl
    hz := rfl }

lemma scale1' {m T q c b : ℝ} (hm : 0 ≤ m) (hT : 1 ≤ T) (hcb : 0 ≤ c * b) (h : q ≤ c * b) :
    m * q ≤ c * (T * m * b) := by
  have h1 : m * q ≤ m * (c * b) := mul_le_mul_of_nonneg_left h hm
  have h2 : 0 ≤ (T - 1) * (m * (c * b)) := mul_nonneg (by linarith) (mul_nonneg hm hcb)
  linarith

lemma scale2 {m T q c b : ℝ} (hm : 0 ≤ m) (hT : 1 ≤ T) (h : q ≤ c * b) :
    m * T * q ≤ c * (T * m * b) := by
  have h1 : (m * T) * q ≤ (m * T) * (c * b) :=
    mul_le_mul_of_nonneg_left h (mul_nonneg hm (by linarith))
  linarith

lemma log_four_le_three_halves : Real.log 4 ≤ 3 / 2 := by
  have h : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have := Real.log_two_lt_d9
  linarith

lemma log_four_nonneg : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)

lemma log_two_le_one_alt : Real.log 2 ≤ 1 := by
  have := Real.log_two_lt_d9
  linarith

lemma log_two_nonneg : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)

namespace Facts

variable {P : Par} {e K z u E X S sb v w8 : ℝ} (F : Facts P e K z u E X S sb v w8)
include F

lemma xpos : 0 < P.x := by linarith [F.hx]
lemma x1 : 1 ≤ P.x := by linarith [F.hx]
lemma Kpos : 0 < K := by linarith [F.hK]
lemma zpos : 0 < z := by linarith [F.z1]
lemma Epos : 0 < E := by linarith [F.E1]
lemma Spos : 0 < S := by linarith [F.S1]

lemma M1 : 1 ≤ E ^ 4 * P.x ^ 4 :=
  one_le_mul_of_one_le_of_one_le (one_le_pow₀ F.E1) (one_le_pow₀ F.x1)

lemma one_le_threshold_mul_powers : 1 ≤ K * (E ^ 4 * P.x ^ 4) := one_le_mul_of_one_le_of_one_le F.hK F.M1

lemma X1 : 1 ≤ X := by
  have := F.one_le_threshold_mul_powers
  have := F.hXB
  linarith

lemma Xpos : 0 < X := by linarith [F.X1]

lemma one_le_x_mul_s : 1 ≤ X * S := one_le_mul_of_one_le_of_one_le F.X1 F.S1

lemma sb1 : 1 ≤ sb := by
  have h1 : 1 ≤ K * (E ^ 4 * P.x ^ 4) * (X * S) := one_le_mul_of_one_le_of_one_le F.one_le_threshold_mul_powers F.one_le_x_mul_s
  have := F.hsb
  linarith

lemma bpos : 0 < P.b := by
  rw [F.hb]
  have := F.sb1
  positivity

lemma b0 : 0 ≤ P.b := F.bpos.le

lemma sb_le_b : sb ≤ P.b := by
  rw [F.hb]
  have := F.sb1
  exact le_mul_of_one_le_left (by linarith) this

lemma hbXS : 100 * K * (E ^ 4 * P.x ^ 4) * (X * S) ≤ P.b := F.hsb.trans F.sb_le_b

lemma hbsb : 100 * K * (E ^ 4 * P.x ^ 4) * (X * S) * sb ≤ P.b := by
  rw [F.hb]
  have := F.sb1
  exact mul_le_mul_of_nonneg_right F.hsb (by linarith)

lemma zpow_le {i : ℕ} (hi : i ≤ 4) : 100 * K * z ^ i ≤ P.x := by
  refine le_trans ?_ F.hz4
  have := F.Kpos
  have := pow_le_pow_right₀ F.z1 hi
  gcongr

lemma hundred_z_le_x : 100 * z ≤ P.x := by
  have h := F.zpow_le (i := 1) (by norm_num)
  rw [pow_one] at h
  have h2 : 100 * 1 * z ≤ 100 * K * z := by
    have := F.hK
    have := F.zpos
    gcongr
  linarith

lemma rpos : 0 < P.x⁻¹ := inv_pos.2 F.xpos
lemma xr : P.x * P.x⁻¹ = 1 := mul_inv_cancel₀ F.xpos.ne'
lemma r2 : (P.x ^ 2)⁻¹ = P.x⁻¹ ^ 2 := (inv_pow _ _).symm

lemma Kzr {i : ℕ} (hi : i ≤ 4) : 100 * K * z ^ i * P.x⁻¹ ≤ 1 := by
  have h := mul_le_mul_of_nonneg_right (F.zpow_le hi) F.rpos.le
  rwa [F.xr] at h

lemma Kzr0 (i : ℕ) : 0 ≤ 100 * K * z ^ i * P.x⁻¹ := by
  have := F.Kpos
  have := F.zpos
  have := F.rpos
  positivity

lemma zr0 (i : ℕ) : 0 ≤ 100 * z ^ i * P.x⁻¹ := by
  have := F.zpos
  have := F.rpos
  positivity

lemma div_le_div_sq_of_le {A B y : ℝ} (hAB : A ≤ B) (hB : 0 ≤ B) (hy : P.x ^ 2 ≤ y) : A / y ≤ B * P.x⁻¹ ^ 2 := by
  have hx2 : 0 < P.x ^ 2 := pow_pos F.xpos 2
  rw [← F.r2, ← div_eq_mul_inv]
  exact div_le_div₀ hB hAB hx2 hy

lemma npos : 0 < P.n := lt_of_lt_of_le (pow_pos F.xpos 2) F.nx
lemma n1 : 1 ≤ P.n := le_trans (one_le_pow₀ F.x1) F.nx
lemma apos : 0 < P.a := by rw [F.ha]; exact mul_pos F.xpos F.bpos

lemma la0 : 0 ≤ P.lx + z := add_nonneg F.lx0 F.zpos.le
lemma la2z : P.lx + z ≤ 2 * z := by linarith [F.lxz]
lemma lax : P.lx + z ≤ P.x := by linarith [F.lxz, F.hundred_z_le_x, F.zpos]

lemma logE : Real.log E = e * P.lx := by
  rw [F.hE, Real.log_rpow F.xpos]; rfl

lemma log_le_alt {y : ℝ} (hy0 : 0 < y) (hy : y ≤ E) : Real.log y ≤ z :=
  (Real.log_le_log hy0 hy).trans (by rw [F.logE]; exact F.elx)

lemma v_le_b : v ≤ P.b := by
  rw [← F.hvX]; exact le_mul_of_one_le_right F.v0 F.X1

lemma hsg : sg P K = 100 * K * z ^ 4 * P.x⁻¹ := by
  unfold sg
  rw [F.hz, div_eq_mul_inv, mul_comm 4 P.ε, Real.rpow_mul F.xpos.le, Real.rpow_ofNat]

lemma sg0 : 0 ≤ sg P K := by rw [F.hsg]; exact F.Kzr0 4
lemma sg1 : sg P K ≤ 1 := by rw [F.hsg]; exact F.Kzr (le_refl _)

lemma Kzr_sg {i : ℕ} (hi : i ≤ 4) : 100 * K * z ^ i * P.x⁻¹ ≤ sg P K := by
  rw [F.hsg]
  have := pow_le_pow_right₀ F.z1 hi
  have := F.Kpos
  have := F.rpos
  gcongr

lemma zr_sg {i : ℕ} (hi : i ≤ 4) : 100 * z ^ i * P.x⁻¹ ≤ sg P K := by
  refine le_trans ?_ (F.Kzr_sg hi)
  have := F.hK
  have := F.zpos
  have := F.rpos
  have h : 100 * 1 * z ^ i * P.x⁻¹ ≤ 100 * K * z ^ i * P.x⁻¹ := by gcongr
  linarith

lemma r_sg : P.x⁻¹ ≤ sg P K := by
  rw [F.hsg]
  have h1 : 1 ≤ K * z ^ 4 := one_le_mul_of_one_le_of_one_le F.hK (one_le_pow₀ F.z1)
  exact le_mul_of_one_le_left F.rpos.le (by linarith)

lemma close_sg {c w : ℝ} (_hc0 : 0 ≤ c) (hc : c ≤ 1) (hw0 : 0 ≤ w) (hw : w ≤ sg P K) :
    P.b * c * w ≤ sg P K * P.b := by
  have h1 : c * w ≤ 1 * sg P K := mul_le_mul hc hw hw0 zero_le_one
  have h2 := mul_le_mul_of_nonneg_left h1 F.b0
  linarith

lemma br_sg : P.b * P.x⁻¹ ≤ sg P K * P.b := by
  have := mul_le_mul_of_nonneg_left F.r_sg F.b0
  linarith

lemma monoG {i j i' j' : ℕ} (hi : i ≤ i') (hj : j ≤ j') : E ^ i * P.x ^ j ≤ E ^ i' * P.x ^ j' :=
  mul_le_mul (pow_le_pow_right₀ F.E1 hi) (pow_le_pow_right₀ F.x1 hj)
    (pow_nonneg F.xpos.le _) (pow_nonneg F.Epos.le _)

lemma mono3 {i j : ℕ} (hi : i ≤ 4) (hj : j ≤ 3) : E ^ i * P.x ^ j ≤ E ^ 4 * P.x ^ 4 * P.x⁻¹ := by
  have h : E ^ 4 * P.x ^ 4 * P.x⁻¹ = E ^ 4 * P.x ^ 3 := by
    rw [show P.x ^ 4 = P.x ^ 3 * P.x by ring, mul_assoc, mul_assoc, F.xr, mul_one]
  rw [h]
  exact F.monoG hi hj

lemma polyXS' {i j : ℕ} (hi : i ≤ 4) (hj : j ≤ 3) {c : ℝ} (hc : c ≤ 100) :
    c * K * (E ^ i * P.x ^ j) * (X * S) ≤ sg P K * P.b := by
  refine le_trans ?_ F.br_sg
  have h1 := F.mono3 hi hj
  have h2 := F.Kpos
  have h3 := F.one_le_x_mul_s
  have h4 : 0 ≤ E ^ i * P.x ^ j := mul_nonneg (pow_nonneg F.Epos.le _) (pow_nonneg F.xpos.le _)
  calc c * K * (E ^ i * P.x ^ j) * (X * S) ≤ 100 * K * (E ^ 4 * P.x ^ 4 * P.x⁻¹) * (X * S) := by gcongr
    _ = (100 * K * (E ^ 4 * P.x ^ 4) * (X * S)) * P.x⁻¹ := by ring
    _ ≤ P.b * P.x⁻¹ := mul_le_mul_of_nonneg_right F.hbXS F.rpos.le

lemma polyX' {i j : ℕ} (hi : i ≤ 4) (hj : j ≤ 3) {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 100) :
    c * K * (E ^ i * P.x ^ j) * X ≤ sg P K * P.b := by
  refine le_trans ?_ (F.polyXS' hi hj hc)
  have h2 := F.Kpos
  have h4 : 0 ≤ E ^ i * P.x ^ j := mul_nonneg (pow_nonneg F.Epos.le _) (pow_nonneg F.xpos.le _)
  have h5 : X ≤ X * S := le_mul_of_one_le_right F.Xpos.le F.S1
  gcongr

lemma polyv' {i j : ℕ} (hi : i ≤ 4) (hj : j ≤ 3) {c : ℝ} (hc : c ≤ 100) :
    c * K * (E ^ i * P.x ^ j) * v ≤ sg P K * P.b := by
  refine le_trans ?_ F.br_sg
  have h1 := F.mono3 hi hj
  have h2 := F.Kpos
  have h4 : 0 ≤ E ^ i * P.x ^ j := mul_nonneg (pow_nonneg F.Epos.le _) (pow_nonneg F.xpos.le _)
  have h5 := F.v0
  calc c * K * (E ^ i * P.x ^ j) * v ≤ 100 * K * (E ^ 4 * P.x ^ 4 * P.x⁻¹) * v := by gcongr
    _ = (100 * K * (E ^ 4 * P.x ^ 4)) * v * P.x⁻¹ := by ring
    _ ≤ X * v * P.x⁻¹ := by
        have := F.hXB
        have := F.rpos
        gcongr
    _ = P.b * P.x⁻¹ := by rw [mul_comm X v, F.hvX]

end Facts

theorem size_floors_bound : SizeFloors := by
  intro P e K m T hW hL hm hT
  obtain ⟨z, u, E, X, S, sb, v, w8, F⟩ := facts hW hL
  unfold tFloors unitU
  apply scale1' hm hT (mul_nonneg F.sg0 F.b0)
  rw [F.hXpp, F.loga]
  unfold Par.f
  have h1 := F.C0; have h2 := F.CK; have h3 := F.npos; have h4 := F.nE; have h5 := F.N0
  have h6 := F.NE; have h7 := F.la0; have h8 := F.lax; have h9 := F.xpos; have h10 := F.Xpos
  have h11 := F.Kpos; have h12 := F.Epos
  calc 2 * P.C * (2 * P.n) * (P.x * P.n * X) * (P.N ^ 2 * (P.lx + z) + 2 * (P.lx + z) ^ 2)
      ≤ 2 * K * (2 * E) * (P.x * E * X) * (E ^ 2 * P.x + 2 * P.x ^ 2) := by gcongr
    _ = 4 * K * (E ^ 4 * P.x ^ 2) * X + 8 * K * (E ^ 2 * P.x ^ 3) * X := by ring
    _ ≤ 4 * K * (E ^ 4 * P.x ^ 3) * X + 8 * K * (E ^ 4 * P.x ^ 3) * X := by
        have a1 := F.monoG (i := 4) (j := 2) (i' := 4) (j' := 3) (by norm_num) (by norm_num)
        have a2 := F.monoG (i := 2) (j := 3) (i' := 4) (j' := 3) (by norm_num) (by norm_num)
        gcongr
    _ = 12 * K * (E ^ 4 * P.x ^ 3) * X := by ring
    _ ≤ sg P K * P.b := F.polyX' (le_refl _) (le_refl _) (by norm_num) (by norm_num)

theorem size_cp_bucket_bound : SizeCp := by
  intro P e K m T hW hL hm hT
  obtain ⟨z, u, E, X, S, sb, v, w8, F⟩ := facts hW hL
  unfold tCp unitU
  have hl : Real.log (2 * P.a) = Real.log 2 + (P.lx + z) := by
    rw [Real.log_mul (by norm_num) F.apos.ne', F.loga]
  have hl0 : 0 ≤ Real.log (2 * P.a) := by rw [hl]; exact add_nonneg log_two_nonneg F.la0
  have hlx : Real.log (2 * P.a) ≤ P.x := by
    rw [hl]; linarith [log_two_le_one_alt, F.la2z, F.hundred_z_le_x, F.z1]
  have hSk0 : 0 ≤ P.Sk := by unfold Par.Sk; linarith [F.Sc0, F.η0, F.kx, pow_pos F.xpos 2]
  have hSk : P.Sk ≤ 3 * (E * S) := by
    unfold Par.Sk
    have a1 : S ≤ E * S := le_mul_of_one_le_left F.Spos.le F.E1
    have a2 : E ≤ E * S := le_mul_of_one_le_right F.Epos.le F.S1
    linarith [F.ScS, F.ηS, F.kE]
  have key : 2 * P.C * P.Sk * Real.log (2 * P.a) * P.Xpp ≤ sg P K * P.b := by
    rw [F.hXpp]
    have h1 := F.C0; have h2 := F.CK; have h3 := F.npos; have h4 := F.nE
    have h9 := F.xpos; have h10 := F.Xpos; have h11 := F.Kpos; have h12 := F.Epos; have h13 := F.Spos
    calc 2 * P.C * P.Sk * Real.log (2 * P.a) * (P.x * P.n * X)
        ≤ 2 * K * (3 * (E * S)) * P.x * (P.x * E * X) := by gcongr
      _ = 6 * K * (E ^ 2 * P.x ^ 2) * (X * S) := by ring
      _ ≤ sg P K * P.b := F.polyXS' (by norm_num) (by norm_num) (by norm_num)
  have := scale2 hm hT key
  linarith

theorem size_prime_low_bound : SizePrLow := by
  intro P e K m T hW hL hm hT
  obtain ⟨z, u, E, X, S, sb, v, w8, F⟩ := facts hW hL
  unfold tPrLow unitU
  have key : 2 * Real.log 4 * (P.p₀ * P.Q₁) ≤ sg P K * P.b := by
    unfold Par.Q₁
    rw [F.hbp]
    have h1 := F.C0; have h2 := F.CK; have h3 := F.r0; have h4 := F.rE; have h5 := F.pE
    have h6 := F.lx0; have h7 : P.lx ≤ P.x := by linarith [F.lxz, F.hundred_z_le_x, F.zpos]
    have h8 := F.v0; have h9 := F.xpos; have h11 := F.Kpos; have h12 := F.Epos
    have h13 := log_four_le_three_halves; have h14 := log_four_nonneg
    have h15 : (0 : ℝ) ≤ P.p₀ := Nat.cast_nonneg _
    calc 2 * Real.log 4 * (P.p₀ * (P.C * P.rG * (P.x * v) * P.lx))
        ≤ 2 * (3 / 2) * (E * (K * E * (P.x * v) * P.x)) := by gcongr
      _ = 3 * K * (E ^ 2 * P.x ^ 2) * v := by ring
      _ ≤ sg P K * P.b := F.polyv' (by norm_num) (by norm_num) (by norm_num)
  have := scale2 hm hT key
  linarith

lemma xprime_q_two_expand {P : Par} {e K z u E X S sb v w8 : ℝ} (F : Facts P e K z u E X S sb v w8) :
    P.Xp * P.Q₂ = P.C * P.b + P.C * X * (P.η + P.Sc) + P.C * (P.b / P.n) * P.lx * w8
      + P.C * X * P.t * P.lx * w8 + X * P.bo := by
  unfold Par.Q₂
  rw [F.hXp, F.hbp, F.hwpp, F.hδ, ← F.hvX, div_inv_eq_mul]
  have h1 := F.xpos.ne'
  have h2 := F.npos.ne'
  field_simp
  ring

theorem size_prime_high_bound : SizePrHigh := by
  intro P e K m T hW hL hm hT
  obtain ⟨z, u, E, X, S, sb, v, w8, F⟩ := facts hW hL
  unfold tPrHigh unitU
  have h1 := F.C0; have h2 := F.CK; have h9 := F.xpos; have h10 := F.Xpos; have h11 := F.Kpos
  have h12 := F.Epos; have h13 := F.Spos; have hb := F.b0; have hz := F.zpos
  have hlx0 := F.lx0; have hlx := F.lxz; have hw0 : 0 ≤ w8 := by linarith [F.w81]
  have hw := F.w8z
  have hr0 := F.rpos
  have p2 : 4 * (P.C * X * (P.η + P.Sc)) ≤ sg P K * P.b := by
    have a1 := F.η0; have a2 := F.ηS; have a3 := F.Sc0; have a4 := F.ScS
    have a5 : 8 * K * (E ^ 0 * P.x ^ 0) * (X * S) ≤ sg P K * P.b :=
      F.polyXS' (by norm_num) (by norm_num) (by norm_num)
    have a6 : P.C * X * (P.η + P.Sc) ≤ K * X * (S + S) := by gcongr
    have a7 : 4 * (K * X * (S + S)) = 8 * K * (E ^ 0 * P.x ^ 0) * (X * S) := by ring
    linarith
  have p3 : 4 * (P.C * (P.b / P.n) * P.lx * w8) ≤ sg P K * P.b := by
    have a1 : P.b / P.n ≤ P.b * P.x⁻¹ ^ 2 := F.div_le_div_sq_of_le (le_refl _) hb F.nx
    have a0 : 0 ≤ P.b / P.n := div_nonneg hb F.npos.le
    have a2 : P.C * (P.b / P.n) * P.lx * w8 ≤ K * (P.b * P.x⁻¹ ^ 2) * z * z := by gcongr
    have a3 : 4 * (K * (P.b * P.x⁻¹ ^ 2) * z * z)
        = P.b * (4 / 100 * (100 * K * z ^ 2 * P.x⁻¹)) * P.x⁻¹ := by ring
    have b1 := F.Kzr (i := 2) (by norm_num)
    have b0 := F.Kzr0 2
    have a4 : P.b * (4 / 100 * (100 * K * z ^ 2 * P.x⁻¹)) * P.x⁻¹ ≤ sg P K * P.b :=
      F.close_sg (by linarith) (by linarith) hr0.le F.r_sg
    linarith
  have p4 : 4 * (P.C * X * P.t * P.lx * w8) ≤ sg P K * P.b := by
    have a1 := F.t0; have a2 := F.tE
    have a3 : z * z ≤ P.x := by
      have := F.zpow_le (i := 2) (by norm_num)
      have b1 : 1 * z ^ 2 ≤ 100 * K * z ^ 2 := by
        have : (1 : ℝ) ≤ 100 * K := by linarith [F.hK]
        gcongr
      nlinarith
    have a4 : P.C * X * P.t * P.lx * w8 ≤ K * X * E * z * z := by gcongr
    have a5 : K * X * E * z * z ≤ K * X * E * P.x := by
      have : K * X * E * z * z = K * X * E * (z * z) := by ring
      rw [this]; gcongr
    have a6 : 4 * K * (E ^ 1 * P.x ^ 1) * X ≤ sg P K * P.b :=
      F.polyX' (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have a7 : 4 * (K * X * E * P.x) = 4 * K * (E ^ 1 * P.x ^ 1) * X := by ring
    linarith
  have p5 : 4 * (X * P.bo) ≤ sg P K * P.b := by
    have a1 := F.bo0; have a2 := F.bosb; have a3 := F.hbsb; have a4 := F.sb1
    have a5 : X * P.bo ≤ X * sb := by gcongr
    have a6 : 4 * 1 * (1 * P.x) * (X * 1) * sb ≤ 100 * K * (E ^ 4 * P.x ^ 4) * (X * S) * sb := by
      have c1 := F.hK; have c2 := F.S1
      have c3 : 1 ≤ E ^ 4 := one_le_pow₀ F.E1
      have c4 : P.x ≤ P.x ^ 4 := by
        calc P.x = P.x ^ 1 := (pow_one _).symm
          _ ≤ P.x ^ 4 := pow_le_pow_right₀ F.x1 (by norm_num)
      gcongr
      norm_num
    have a7 : 4 * (X * sb) = (4 * 1 * (1 * P.x) * (X * 1) * sb) * P.x⁻¹ := by
      have : (4 * 1 * (1 * P.x) * (X * 1) * sb) * P.x⁻¹ = 4 * (X * sb) * (P.x * P.x⁻¹) := by ring
      rw [this, F.xr, mul_one]
    have a8 : (4 * 1 * (1 * P.x) * (X * 1) * sb) * P.x⁻¹ ≤ P.b * P.x⁻¹ :=
      mul_le_mul_of_nonneg_right (a6.trans a3) hr0.le
    have a9 := F.br_sg
    linarith
  have hXQ : P.Xp * P.Q₂ ≤ (P.C + sg P K) * P.b := by
    rw [xprime_q_two_expand F]; linarith
  have hsb0 : 0 ≤ sg P K * P.b := mul_nonneg F.sg0 hb
  have key : 2 * Real.log 4 * (P.Xp * P.Q₂) ≤ (2 * Real.log 4 * P.C + 3 * sg P K) * P.b := by
    have a1 : 2 * Real.log 4 * (P.Xp * P.Q₂) ≤ 2 * Real.log 4 * ((P.C + sg P K) * P.b) :=
      mul_le_mul_of_nonneg_left hXQ (by linarith [log_four_nonneg])
    have a2 : 2 * Real.log 4 * (sg P K * P.b) ≤ 3 * (sg P K * P.b) :=
      mul_le_mul_of_nonneg_right (by linarith [log_four_le_three_halves]) hsb0
    linarith
  exact scale2 hm hT key

theorem size_or_bucket_bound : SizeOr := by
  intro P e K m T hW hL hm hT
  obtain ⟨z, u, E, X, S, sb, v, w8, F⟩ := facts hW hL
  unfold tOr unitU
  have h1 := F.C0; have h2 := F.CK; have h9 := F.xpos; have h11 := F.Kpos
  have hb := F.b0; have hz := F.zpos; have hz1 := F.z1; have hlx0 := F.lx0; have hlx := F.lxz
  have hr0 := F.rpos
  have hx2 : 1 ≤ P.x ^ 2 := one_le_pow₀ F.x1
  have hp1 : P.x ^ 4 ≤ (P.p₀ : ℝ) - 1 := by linarith [F.px]
  have hx24 : P.x ^ 2 ≤ P.x ^ 4 := pow_le_pow_right₀ F.x1 (by norm_num)
  have hp0 : 0 < (P.p₀ : ℝ) - 1 := by linarith
  have c1 : P.La / P.k ≤ z ^ 2 * P.x⁻¹ ^ 2 := F.div_le_div_sq_of_le F.Laz (by positivity) F.kx
  have c2 : 1 / P.K₀ ≤ 1 * P.x⁻¹ ^ 2 := F.div_le_div_sq_of_le (le_refl _) (by norm_num) F.x_sq_le_threshold
  have c3 : Real.log P.Xp + Real.log 4 ≤ 3 * z := by
    rw [F.hXp, F.logX]; linarith [F.uz, log_four_le_three_halves]
  have c30 : 0 ≤ Real.log P.Xp + Real.log 4 := by
    rw [F.hXp, F.logX]; linarith [F.u1, log_four_nonneg]
  have c4 : Real.log ((P.p₀ : ℝ) - 1) ≤ z := F.log_le_alt hp0 (by linarith [F.pE])
  have c5 : 2 * (Real.log ((P.p₀ : ℝ) - 1) + 1) / ((P.p₀ : ℝ) - 1) ≤ 4 * z * P.x⁻¹ ^ 2 :=
    F.div_le_div_sq_of_le (by linarith) (by positivity) (by linarith)
  have c12 : 0 ≤ P.La / P.k + 1 / P.K₀ := by
    have := F.La0
    have : 0 < P.k := by linarith [F.kx]
    have : 0 < P.K₀ := by linarith [F.x_sq_le_threshold]
    positivity
  have z3 : z ≤ z ^ 3 := by
    calc z = z ^ 1 := (pow_one z).symm
      _ ≤ z ^ 3 := pow_le_pow_right₀ hz1 (by norm_num)
  have br : (P.La / P.k + 1 / P.K₀) * (Real.log P.Xp + Real.log 4) +
      2 * (Real.log ((P.p₀ : ℝ) - 1) + 1) / ((P.p₀ : ℝ) - 1) ≤ 10 * z ^ 3 * P.x⁻¹ ^ 2 := by
    have d1 : (P.La / P.k + 1 / P.K₀) * (Real.log P.Xp + Real.log 4)
        ≤ (z ^ 2 * P.x⁻¹ ^ 2 + 1 * P.x⁻¹ ^ 2) * (3 * z) := by gcongr
    have d2 : (z ^ 2 * P.x⁻¹ ^ 2 + 1 * P.x⁻¹ ^ 2) * (3 * z) + 4 * z * P.x⁻¹ ^ 2
        = (3 * z ^ 3 + 7 * z) * P.x⁻¹ ^ 2 := by ring
    have d3 : (3 * z ^ 3 + 7 * z) * P.x⁻¹ ^ 2 ≤ (10 * z ^ 3) * P.x⁻¹ ^ 2 := by
      gcongr
      linarith
    linarith
  have key : 2 * P.C * P.lx * P.a * ((P.La / P.k + 1 / P.K₀) * (Real.log P.Xp + Real.log 4) +
      2 * (Real.log ((P.p₀ : ℝ) - 1) + 1) / ((P.p₀ : ℝ) - 1)) ≤ sg P K * P.b := by
    rw [F.ha]
    calc 2 * P.C * P.lx * (P.x * P.b) * ((P.La / P.k + 1 / P.K₀) * (Real.log P.Xp + Real.log 4) +
          2 * (Real.log ((P.p₀ : ℝ) - 1) + 1) / ((P.p₀ : ℝ) - 1))
        ≤ 2 * P.C * P.lx * (P.x * P.b) * (10 * z ^ 3 * P.x⁻¹ ^ 2) :=
          mul_le_mul_of_nonneg_left br (by positivity)
      _ ≤ 2 * K * z * (P.x * P.b) * (10 * z ^ 3 * P.x⁻¹ ^ 2) := by gcongr
      _ = P.b * (1 / 5 * (P.x * P.x⁻¹)) * (100 * K * z ^ 4 * P.x⁻¹) := by ring
      _ ≤ sg P K * P.b := by
          rw [F.xr]
          exact F.close_sg (by norm_num) (by norm_num) (F.Kzr0 4) (F.Kzr_sg (le_refl _))
  have := scale2 hm hT key
  linarith

theorem size_bad_orbits_bound : SizeBad := by
  intro P e K m T hW hL hm hT
  obtain ⟨z, u, E, X, S, sb, v, w8, F⟩ := facts hW hL
  unfold tBad unitU
  have h9 := F.xpos; have h11 := F.Kpos; have hb := F.b0; have hz := F.zpos; have hr0 := F.rpos
  have c3 : Real.log P.Xp + Real.log 4 ≤ 3 * z := by
    rw [F.hXp, F.logX]; linarith [F.uz, log_four_le_three_halves, F.z1]
  have c30 : 0 ≤ Real.log P.Xp + Real.log 4 := by
    rw [F.hXp, F.logX]; linarith [F.u1, log_four_nonneg]
  have hβ0 := F.β0
  have hβ : P.β ≤ K * P.x⁻¹ ^ 2 := by rw [← F.r2]; exact F.βK
  have key : 32 * P.β * P.a * (Real.log P.Xp + Real.log 4) ≤ sg P K * P.b := by
    rw [F.ha]
    calc 32 * P.β * (P.x * P.b) * (Real.log P.Xp + Real.log 4)
        ≤ 32 * (K * P.x⁻¹ ^ 2) * (P.x * P.b) * (3 * z) := by gcongr
      _ = P.b * (96 / 100 * (P.x * P.x⁻¹)) * (100 * K * z ^ 1 * P.x⁻¹) := by ring
      _ ≤ sg P K * P.b := by
          rw [F.xr]
          exact F.close_sg (by norm_num) (by norm_num) (F.Kzr0 1) (F.Kzr_sg (by norm_num))
  have := scale2 hm hT key
  linarith

theorem size_orders_bucket_bound : SizeOrders := by
  intro P e K m T hW hL hm hT
  obtain ⟨z, u, E, X, S, sb, v, w8, F⟩ := facts hW hL
  unfold tOrders unitU
  have h9 := F.xpos; have h11 := F.Kpos; have hb := F.b0; have hz := F.zpos; have hr0 := F.rpos
  have hM1 : 1 ≤ max P.Y P.Xpp := F.Y1.trans (le_max_left _ _)
  have hlM : Real.log (max P.Y P.Xpp) ≤ 3 * z := by
    rcases max_choice P.Y P.Xpp with h | h <;> rw [h]
    · have hY0 : 0 < P.Y := by linarith [F.Y1]
      have a2 : Real.log P.Y ≤ Real.log (2 * X) := Real.log_le_log hY0 F.YX
      rw [Real.log_mul (by norm_num) F.Xpos.ne', F.logX] at a2
      linarith [log_two_le_one_alt, F.uz, F.z1]
    · rw [F.hXpp, Real.log_mul (mul_pos h9 F.npos).ne' F.Xpos.ne', Real.log_mul h9.ne' F.npos.ne', F.logX]
      have a1 : Real.log P.n ≤ z := F.log_le_alt F.npos F.nE
      have a2 : Real.log P.x ≤ z := F.lxz
      linarith [F.uz]
  generalize max P.Y P.Xpp = M at hM1 hlM ⊢
  have q1 := F.n2x; have q2 := F.n2n
  have q0 : (1 : ℝ) ≤ 2 ^ P.e₂ := one_le_pow₀ (by norm_num)
  generalize (2 : ℝ) ^ P.e₂ = n at q0 q1 q2 ⊢
  have qp : 0 < n := by linarith
  have hnY1 : 1 ≤ n * M := one_le_mul_of_one_le_of_one_le q0 hM1
  have hL0 : 0 ≤ Real.log (n * M) := Real.log_nonneg hnY1
  have hL3 : Real.log (n * M) ≤ 4 * z := by
    rw [Real.log_mul qp.ne' (by linarith)]
    have a1 : Real.log n ≤ z := F.log_le_alt qp (q2.trans F.nE)
    linarith
  have hJ0 : (0 : ℝ) ≤ P.Jo := Nat.cast_nonneg _
  have hJ := F.Joz
  have hC0 := F.Co0; have hCK := F.CoK
  have c1 : P.Cord * P.Jo * Real.log (n * M) ^ 2 / n ≤ K * z * (4 * z) ^ 2 * P.x⁻¹ ^ 2 := by
    refine F.div_le_div_sq_of_le ?_ (by positivity) q1
    gcongr
  have key : 4 * P.a * (P.Cord * P.Jo * Real.log (n * M) ^ 2 / n) ≤ sg P K * P.b := by
    rw [F.ha]
    calc 4 * (P.x * P.b) * (P.Cord * P.Jo * Real.log (n * M) ^ 2 / n)
        ≤ 4 * (P.x * P.b) * (K * z * (4 * z) ^ 2 * P.x⁻¹ ^ 2) := by gcongr
      _ = P.b * (64 / 100 * (P.x * P.x⁻¹)) * (100 * K * z ^ 3 * P.x⁻¹) := by ring
      _ ≤ sg P K * P.b := by
          rw [F.xr]
          exact F.close_sg (by norm_num) (by norm_num) (F.Kzr0 3) (F.Kzr_sg (by norm_num))
  have := scale2 hm hT key
  linarith

theorem size_band_bound : SizeBand := by
  intro P e K m T hW hL hm hT
  obtain ⟨z, u, E, X, S, sb, v, w8, F⟩ := facts hW hL
  unfold tBand unitU
  have h9 := F.xpos; have hb := F.b0; have hz := F.zpos; have hr0 := F.rpos
  have hI0 : (0 : ℝ) ≤ P.Ib := Nat.cast_nonneg _
  have hI : (P.Ib : ℝ) ≤ z := F.Ibu.trans F.uz
  have hx24 : P.x ^ 2 ≤ P.x ^ 4 := pow_le_pow_right₀ F.x1 (by norm_num)
  have c1 : 1 / (P.p₀ : ℝ) ≤ 1 * P.x⁻¹ ^ 2 :=
    F.div_le_div_sq_of_le (le_refl _) (by norm_num) (by linarith [F.px])
  have c10 : 0 ≤ 1 / (P.p₀ : ℝ) := by positivity
  have c2 : P.ρ ≤ P.x⁻¹ ^ 2 := by rw [← F.r2]; exact F.ρx
  have c20 := F.ρ0
  have c3 : Real.log (2 * P.Xp) ≤ 2 * z := by
    rw [F.hXp, Real.log_mul (by norm_num) F.Xpos.ne', F.logX]; linarith [log_two_le_one_alt, F.uz, F.z1]
  have c30 : 0 ≤ Real.log (2 * P.Xp) := by
    rw [F.hXp]; exact Real.log_nonneg (by linarith [F.X1])
  have key : 4 * P.a * (P.Ib * ((4 * P.ρ + 1 / (P.p₀ : ℝ)) * Real.log (2 * P.Xp))) ≤ sg P K * P.b := by
    rw [F.ha]
    calc 4 * (P.x * P.b) * (P.Ib * ((4 * P.ρ + 1 / (P.p₀ : ℝ)) * Real.log (2 * P.Xp)))
        ≤ 4 * (P.x * P.b) * (z * ((4 * P.x⁻¹ ^ 2 + 1 * P.x⁻¹ ^ 2) * (2 * z))) := by gcongr
      _ = P.b * (40 / 100 * (P.x * P.x⁻¹)) * (100 * z ^ 2 * P.x⁻¹) := by ring
      _ ≤ sg P K * P.b := by
          rw [F.xr]
          exact F.close_sg (by norm_num) (by norm_num) (F.zr0 2) (F.zr_sg (by norm_num))
  have := scale2 hm hT key
  linarith

theorem size_high_bucket_bound : SizeHigh := by
  intro P e K m T hW hL hm hT
  obtain ⟨z, u, E, X, S, sb, v, w8, F⟩ := facts hW hL
  unfold tHigh unitU
  have h9 := F.xpos; have hb := F.b0; have hz := F.zpos; have hr0 := F.rpos
  have hXpp1 : 1 ≤ P.x * P.n * X :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le F.x1 F.n1) F.X1
  have c3 : Real.log (2 * P.Xpp) ≤ 4 * z := by
    rw [F.hXpp, Real.log_mul (by norm_num) (by positivity),
      Real.log_mul (mul_pos h9 F.npos).ne' F.Xpos.ne', Real.log_mul h9.ne' F.npos.ne', F.logX]
    have a1 : Real.log P.n ≤ z := F.log_le_alt F.npos F.nE
    have a2 : Real.log P.x ≤ z := F.lxz
    linarith [log_two_le_one_alt, F.uz, F.z1]
  have c30 : 0 ≤ Real.log (2 * P.Xpp) := by
    rw [F.hXpp]; exact Real.log_nonneg (by linarith)
  have ht0 := F.th0; have ht := F.thx
  have c4 : P.a * P.th ^ 2 ≤ P.b * P.x⁻¹ := by
    rw [F.ha]
    calc P.x * P.b * P.th ^ 2 ≤ P.x * P.b * P.x⁻¹ ^ 2 := by gcongr
      _ = P.b * P.x⁻¹ * (P.x * P.x⁻¹) := by ring
      _ = P.b * P.x⁻¹ := by rw [F.xr, mul_one]
  have c5 : P.wpp * P.th ≤ P.b * P.x⁻¹ := by
    rw [F.hwpp]
    have a1 : v / P.n ≤ P.b := (div_le_self F.v0 F.n1).trans F.v_le_b
    have a0 : 0 ≤ v / P.n := div_nonneg F.v0 F.npos.le
    gcongr
  have c6 : 0 ≤ P.a * P.th ^ 2 + P.wpp * P.th := by
    have := F.apos
    have : 0 ≤ P.wpp := by rw [F.hwpp]; exact div_nonneg F.v0 F.npos.le
    positivity
  have key : 2 * Real.log (2 * P.Xpp) * (P.a * P.th ^ 2 + P.wpp * P.th) ≤ sg P K * P.b := by
    calc 2 * Real.log (2 * P.Xpp) * (P.a * P.th ^ 2 + P.wpp * P.th)
        ≤ 2 * (4 * z) * (P.b * P.x⁻¹ + P.b * P.x⁻¹) := by gcongr
      _ = P.b * (16 / 100) * (100 * z ^ 1 * P.x⁻¹) := by ring
      _ ≤ sg P K * P.b := F.close_sg (by norm_num) (by norm_num) (F.zr0 1) (F.zr_sg (by norm_num))
  have := scale2 hm hT key
  linarith

theorem size_discriminant_bound : SizeD := by
  intro P e K m T hW hL hm hT
  obtain ⟨z, u, E, X, S, sb, v, w8, F⟩ := facts hW hL
  unfold tD unitU
  have h9 := F.xpos; have hb := F.b0; have hz := F.zpos; have hr0 := F.rpos
  have hx2 : Real.exp 1 ≤ P.x ^ 2 := by
    have a1 := Real.exp_one_lt_d9
    have a2 : (100 : ℝ) ^ 2 ≤ P.x ^ 2 := by
      have := F.hx
      gcongr
    linarith
  have c1 : Real.log P.d / P.d ≤ Real.log (P.x ^ 2) / P.x ^ 2 :=
    Real.log_div_self_antitoneOn (by exact hx2) (by exact hx2.trans F.dx) F.dx
  have c2 : Real.log (P.x ^ 2) / P.x ^ 2 = 2 * P.lx * P.x⁻¹ ^ 2 := by
    rw [Real.log_pow, div_eq_mul_inv, F.r2]; push_cast; rfl
  have hlx := F.lxz
  have key : 2 * P.a * Real.log P.d / P.d ≤ sg P K * P.b := by
    rw [F.ha, mul_div_assoc]
    calc 2 * (P.x * P.b) * (Real.log P.d / P.d)
        ≤ 2 * (P.x * P.b) * (2 * z * P.x⁻¹ ^ 2) := by
          rw [c2] at c1
          have : 2 * P.lx * P.x⁻¹ ^ 2 ≤ 2 * z * P.x⁻¹ ^ 2 := by gcongr
          gcongr
          linarith
      _ = P.b * (4 / 100 * (P.x * P.x⁻¹)) * (100 * z ^ 1 * P.x⁻¹) := by ring
      _ ≤ sg P K * P.b := by
          rw [F.xr]
          exact F.close_sg (by norm_num) (by norm_num) (F.zr0 1) (F.zr_sg (by norm_num))
  have := scale2 hm hT key
  linarith

theorem size_second_io_bound : SizeSecondIo := by
  intro P e K m T hW hL hm hT
  obtain ⟨z, u, E, X, S, sb, v, w8, F⟩ := facts hW hL
  unfold tSecondIo unitU
  have h9 := F.xpos; have hb := F.b0; have hz := F.zpos; have hr0 := F.rpos; have hz1 := F.z1
  have hY0 : 0 < P.Y := by linarith [F.Y1]
  have c3 : Real.log P.Y + Real.log 4 ≤ 4 * z := by
    have a2 : Real.log P.Y ≤ Real.log (2 * X) := Real.log_le_log hY0 F.YX
    rw [Real.log_mul (by norm_num) F.Xpos.ne', F.logX] at a2
    linarith [log_two_le_one_alt, log_four_le_three_halves, F.uz]
  have c30 : 0 ≤ Real.log P.Y + Real.log 4 := add_nonneg (Real.log_nonneg F.Y1) log_four_nonneg
  have hs0 := F.s0
  have hs : P.s₀ ≤ P.x⁻¹ ^ 2 := by rw [← F.r2]; exact F.sx
  have c4 : P.s₀ / P.θ + P.s₀ ≤ P.x⁻¹ ^ 2 * (2 * z) := by
    rw [F.hθ, div_inv_eq_mul]
    have : P.s₀ * z + P.s₀ = P.s₀ * (z + 1) := by ring
    rw [this]
    gcongr
    linarith
  have c40 : 0 ≤ P.s₀ / P.θ + P.s₀ := by
    rw [F.hθ, div_inv_eq_mul]; positivity
  have key : (P.s₀ / P.θ + P.s₀) * (4 * P.a * (Real.log P.Y + Real.log 4)) ≤ sg P K * P.b := by
    rw [F.ha]
    calc (P.s₀ / P.θ + P.s₀) * (4 * (P.x * P.b) * (Real.log P.Y + Real.log 4))
        ≤ (P.x⁻¹ ^ 2 * (2 * z)) * (4 * (P.x * P.b) * (4 * z)) := by gcongr
      _ = P.b * (32 / 100 * (P.x * P.x⁻¹)) * (100 * z ^ 2 * P.x⁻¹) := by ring
      _ ≤ sg P K * P.b := by
          rw [F.xr]
          exact F.close_sg (by norm_num) (by norm_num) (F.zr0 2) (F.zr_sg (by norm_num))
  have := scale2 hm hT key
  linarith

theorem sigma_le_one : SgLeOne := by
  intro P e K hW hL
  obtain ⟨z, u, E, X, S, sb, v, w8, F⟩ := facts hW hL
  exact ⟨F.sg0, F.sg1⟩

theorem size_sharp_bound : WindowSizeBoundSharp := by
  intro P e K m T hW hL hm hT
  have a1 := size_floors_bound P e K m T hW hL hm hT
  have a2 := size_cp_bucket_bound P e K m T hW hL hm hT
  have a3 := size_prime_low_bound P e K m T hW hL hm hT
  have a4 := size_prime_high_bound P e K m T hW hL hm hT
  have a5 := size_or_bucket_bound P e K m T hW hL hm hT
  have a6 := size_bad_orbits_bound P e K m T hW hL hm hT
  have a7 := size_orders_bucket_bound P e K m T hW hL hm hT
  have a8 := size_band_bound P e K m T hW hL hm hT
  have a9 := size_high_bucket_bound P e K m T hW hL hm hT
  have a10 := size_discriminant_bound P e K m T hW hL hm hT
  have a11 := size_second_io_bound P e K m T hW hL hm hT
  unfold tDet
  linarith

lemma unitU_nonneg {P : Par} {m T : ℝ} (hm : 0 ≤ m) (hT : 1 ≤ T) : 0 ≤ unitU P m T := by
  have hb : 0 < P.b := Real.exp_pos _
  have : 0 ≤ T := by linarith
  unfold unitU
  positivity

theorem size_total_bound : WindowSizeBound := by
  intro P e K m T hW hL hm hT
  have h := size_sharp_bound P e K m T hW hL hm hT
  obtain ⟨z, u, E, X, S, sb, v, w8, F⟩ := facts hW hL
  have hU := unitU_nonneg (P := P) hm hT
  have h1 : 2 * Real.log 4 * P.C + 13 * sg P K ≤ 3 * P.C + 13 := by
    have := mul_le_mul_of_nonneg_right (show 2 * Real.log 4 ≤ 3 by linarith [log_four_le_three_halves]) F.C0
    linarith [F.sg1]
  exact h.trans (mul_le_mul_of_nonneg_right h1 hU)

lemma secondIo_le_unit {P : Par} {e K m T : ℝ} (hW : Windows P e K) (hL : LargeX P.x P.ε e K)
    (hm : 0 ≤ m) (hT : 1 ≤ T) : tSecondIo P m T ≤ unitU P m T := by
  have h := size_second_io_bound P e K m T hW hL hm hT
  have h1 := (sigma_le_one P e K hW hL).2
  have := mul_le_mul_of_nonneg_right h1 (unitU_nonneg (P := P) hm hT)
  linarith

theorem side_condition_of_windows : SideConditionsOfWindows := by
  intro P e K hW hL
  obtain ⟨z, u, E, X, S, sb, v, w8, F⟩ := facts hW hL
  have hx := F.hx
  have hvpos : 0 < v := by
    have h : 0 < v * X := by rw [F.hvX]; exact F.bpos
    exact (pos_iff_pos_of_mul_pos h).2 F.Xpos
  have hx2 : P.x ≤ P.x ^ 2 := by
    calc P.x = P.x ^ 1 := (pow_one _).symm
      _ ≤ P.x ^ 2 := pow_le_pow_right₀ F.x1 (by norm_num)
  have hx4 : P.x ≤ P.x ^ 4 := by
    calc P.x = P.x ^ 1 := (pow_one _).symm
      _ ≤ P.x ^ 4 := pow_le_pow_right₀ F.x1 (by norm_num)
  have hw0 : 0 < P.wpp := by rw [F.hwpp]; exact div_pos hvpos F.npos
  have hb1 : 1 ≤ P.b := F.sb1.trans F.sb_le_b
  have hw8 : 0 < w8 := by linarith [F.w81]
  have hbp0 : 0 ≤ P.bp := by rw [F.hbp]; exact mul_nonneg F.xpos.le F.v0
  refine ⟨hw0, F.th0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, F.C0, ?_, ?_, ?_, ?_, F.lx0, F.La0, ?_, ?_, by rw [F.hXp]; exact F.hXpp⟩
  · have h1 : P.x⁻¹ ≤ (100 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hx
    have := F.thx
    norm_num at h1
    linarith
  · rw [F.hXpp]
    have h1 : 1 ≤ P.n * X := one_le_mul_of_one_le_of_one_le F.n1 F.X1
    have h2 : P.x * 1 ≤ P.x * (P.n * X) := mul_le_mul_of_nonneg_left h1 F.xpos.le
    have h3 : P.x * P.n * X = P.x * (P.n * X) := by ring
    linarith
  · rw [F.hXpp, F.hwpp, F.ha, ← F.hvX]
    have := F.npos.ne'
    field_simp
  · rw [F.ha]; exact one_le_mul_of_one_le_of_one_le F.x1 hb1
  · rw [F.hXp]; exact F.X1
  · have h1 : (3 : ℝ) ≤ (P.p₀ : ℝ) := by linarith [F.px]
    exact_mod_cast h1
  · have h1 : (4 : ℝ) ≤ (P.d : ℝ) := by linarith [F.dx]
    exact_mod_cast h1
  · unfold Par.f; linarith [F.npos]
  · unfold Par.Sk; linarith [F.Sc0, F.η0, F.kx]
  · unfold Par.Q₁
    have := F.C0; have := F.r0; have := F.lx0
    positivity
  · unfold Par.Q₂
    rw [F.hδ, div_inv_eq_mul]
    have := F.C0; have := F.lx0; have := F.η0; have := F.Sc0; have := F.t0; have := F.bo0
    have := F.xpos
    positivity
  · linarith [F.kx]
  · linarith [F.x_sq_le_threshold]

theorem large_x_eventually : LargeXEv := by
  intro ε e K hε hε4
  have hε3 : 0 < ε / 3 := by positivity
  have hC : ∀ᶠ x : ℝ in Filter.atTop, 100 * K * x ^ (4 * ε) ≤ x := by
    have h := (tendsto_rpow_atTop (show 0 < 1 - 4 * ε by linarith)).eventually_ge_atTop (100 * K)
    filter_upwards [h, Filter.eventually_ge_atTop (1 : ℝ)] with x hx hx1
    have xpos : 0 < x := by linarith
    calc 100 * K * x ^ (4 * ε) ≤ x ^ (1 - 4 * ε) * x ^ (4 * ε) :=
          mul_le_mul_of_nonneg_right hx (Real.rpow_nonneg xpos.le _)
      _ = x := by
          rw [← Real.rpow_add xpos]
          have : 1 - 4 * ε + 4 * ε = 1 := by ring
          rw [this, Real.rpow_one]
  have hB : ∀ᶠ x : ℝ in Filter.atTop, 100 * K * x ^ (4 * e + 4) ≤ Real.exp (x ^ (ε / 3)) := by
    have hc : 0 < (2 * (|4 * e + 4| + 1))⁻¹ := by positivity
    have hb := (isLittleO_log_rpow_atTop hε3).bound hc
    have hA := (tendsto_rpow_atTop hε3).eventually_ge_atTop (2 * Real.log (100 * (|K| + 1)))
    filter_upwards [hb, hA, Filter.eventually_ge_atTop (1 : ℝ)] with x hx hxA hx1
    have xpos : 0 < x := by linarith
    rw [Real.norm_of_nonneg (Real.rpow_nonneg xpos.le _),
      Real.norm_of_nonneg (Real.log_nonneg hx1)] at hx
    have hlog0 := Real.log_nonneg hx1
    have h1 : (|4 * e + 4| + 1) * Real.log x ≤ x ^ (ε / 3) / 2 := by
      have h2 : (|4 * e + 4| + 1) * Real.log x
          ≤ (|4 * e + 4| + 1) * ((2 * (|4 * e + 4| + 1))⁻¹ * x ^ (ε / 3)) := by gcongr
      have h3 : (|4 * e + 4| + 1) * ((2 * (|4 * e + 4| + 1))⁻¹ * x ^ (ε / 3)) = x ^ (ε / 3) / 2 := by
        have : |4 * e + 4| + 1 ≠ 0 := by positivity
        field_simp
      linarith
    have h4 : Real.log x * (4 * e + 4) ≤ x ^ (ε / 3) / 2 := by
      have h5 : Real.log x * (4 * e + 4) ≤ Real.log x * (|4 * e + 4| + 1) := by
        have := le_abs_self (4 * e + 4)
        exact mul_le_mul_of_nonneg_left (by linarith) hlog0
      linarith
    have hKpos : 0 < 100 * (|K| + 1) := by positivity
    calc 100 * K * x ^ (4 * e + 4) ≤ 100 * (|K| + 1) * x ^ (4 * e + 4) := by
          have := le_abs_self K
          have := Real.rpow_nonneg xpos.le (4 * e + 4)
          gcongr
          linarith
      _ = Real.exp (Real.log (100 * (|K| + 1)) + Real.log x * (4 * e + 4)) := by
          rw [Real.exp_add, Real.exp_log hKpos, Real.rpow_def_of_pos xpos]
      _ ≤ Real.exp (x ^ (ε / 3)) := Real.exp_le_exp.2 (by linarith)
  have h6 : ∀ᶠ x : ℝ in Filter.atTop, (6 : ℝ) ≤ x ^ (2 * ε / 3) :=
    (tendsto_rpow_atTop (by positivity)).eventually_ge_atTop _
  obtain ⟨x0, hx0⟩ :=
    Filter.eventually_atTop.1 (((hC.and hB).and h6).and (Filter.eventually_ge_atTop (1 : ℝ)))
  refine ⟨x0, fun x hx => ?_⟩
  obtain ⟨⟨⟨c1, c2⟩, c3⟩, c4⟩ := hx0 x hx
  have xpos : 0 < x := by linarith
  refine ⟨c4, c1, c2, ?_⟩
  have hw0 : 0 ≤ x ^ (ε / 3) := Real.rpow_nonneg xpos.le _
  have h43 : x ^ (ε / 4) ≤ x ^ (ε / 3) := Real.rpow_le_rpow_of_exponent_le c4 (by linarith)
  have hz : x ^ ε = x ^ (2 * ε / 3) * x ^ (ε / 3) := by
    rw [← Real.rpow_add xpos]; congr 1; ring
  have hz6 : 6 * x ^ (ε / 3) ≤ x ^ ε := by rw [hz]; gcongr
  calc 100 * K * x ^ (4 * e + 4) * Real.exp (x ^ (ε / 3) + x ^ (ε / 4))
      ≤ Real.exp (x ^ (ε / 3)) * Real.exp (x ^ (ε / 3) + x ^ (ε / 4)) :=
        mul_le_mul_of_nonneg_right c2 (Real.exp_pos _).le
    _ = Real.exp (x ^ (ε / 3) + (x ^ (ε / 3) + x ^ (ε / 4))) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (x ^ ε / 2) := Real.exp_le_exp.2 (by linarith)

theorem loss_choice_uniform : LossChoiceU := by
  intro Ω U _ π Loss s Sig io D Y θ s₀ mTa h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  obtain ⟨o, a1, a2, a3⟩ := loss_choice Ω π
    (fun o => 0 + ∑ p ∈ s, (if θ < Sig p o then 4 * mTa * Real.log p / p else 0)) s Sig
    (fun p o => 2 * Sig p o * (2 * mTa / p)) 0 Y θ s₀ mTa
    h1 h2 h3 h4 h5 h6 h7 h8 h9 (fun o => le_refl _) (fun p _ o => le_refl _)
  refine ⟨o, a1, fun υ => ?_, fun υ => le_trans ?_ a3⟩
  · have := h10 υ o
    linarith
  · exact Finset.sum_le_sum (fun p hp =>
      mul_le_mul_of_nonneg_left (h11 υ p hp o) (Real.log_natCast_nonneg p))

theorem second_term_le : SecondLe := by
  intro Ps s cl Sg θ m T a hm hT ha hcl
  rw [← Finset.sum_filter, Finset.mul_sum]
  have hsub : Ps.filter (fun p => cl p = PClass.second) ⊆ s.filter (fun p => θ < Sg p) := by
    intro p hp
    rw [Finset.mem_filter] at hp ⊢
    exact hcl p hp.1 hp.2
  calc ∑ p ∈ Ps.filter (fun p => cl p = PClass.second), 4 * m * T * a * (Real.log p / p)
      ≤ ∑ p ∈ s.filter (fun p => θ < Sg p), 4 * m * T * a * (Real.log p / p) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => ?_)
        have : 0 ≤ Real.log p / p := div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)
        positivity
    _ = _ := Finset.sum_congr rfl (fun p _ => by ring)

theorem first_kind_bound : FirstKind := by
  obtain ⟨C, hC⟩ := first_kind_bucket_bound
  refine ⟨C, ?_⟩
  intro e J Y X' ρ p₀ s h1 h2 h3 h4 h5 h6 h7 h8
  refine hC e J ⌊Real.log X'⌋₊ Y X' ρ p₀ (fun i => X' ^ ((1 : ℝ) / ((i + 1 : ℕ) : ℝ))) s h1 h2 h3 h4 h5
    (by linarith) ?_ ?_
  · intro i _
    have hx : (1 : ℝ) ≤ X' := by linarith
    have hpos : (0 : ℝ) < ((i + 1 : ℕ) : ℝ) := by positivity
    have h0 : (0 : ℝ) ≤ (1 : ℝ) / ((i + 1 : ℕ) : ℝ) := by positivity
    have h1' : (1 : ℝ) / ((i + 1 : ℕ) : ℝ) ≤ 1 := by
      rw [div_le_one hpos]; push_cast; linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
    refine ⟨Real.one_le_rpow hx h0, ?_⟩
    calc X' ^ ((1 : ℝ) / ((i + 1 : ℕ) : ℝ)) ≤ X' ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx h1'
      _ = X' := Real.rpow_one X'
  · intro p hp
    obtain ⟨a1, a2, a3⟩ := h8 p hp
    refine ⟨a1, a2, ?_⟩
    rcases a3 with a3 | ⟨b1, i, b2, b3, b4⟩
    · exact Or.inl a3
    · right
      have hp8 : 8 ≤ p := by
        have : (8 : ℝ) ≤ p := le_trans h6 b1
        exact_mod_cast this
      have hi := band_exponent_bound X' ρ p i h7 (by linarith) hp8 b4
      have hi' : i ≤ ⌊Real.log X'⌋₊ := Nat.le_floor hi
      obtain ⟨c1, c2⟩ := band_root_bound X' ρ p i (by linarith) h4 (by linarith) (Nat.cast_nonneg p) b2 b3 b4
      refine ⟨i - 1, by omega, b1, ?_, ?_⟩
      · have : i - 1 + 1 = i := Nat.sub_add_cancel b2
        simp only [this]; exact c1
      · have : i - 1 + 1 = i := Nat.sub_add_cancel b2
        simp only [this]; exact c2

lemma bad_le {τ : Type} (P : Par) (Ps sB : Finset ℕ) (cl : ℕ → PClass) (TT : Finset τ)
    (TTp : ℕ → Finset τ) (BAD : ℕ → τ → Prop) (m : ℝ) (hm : 0 ≤ m) (ha : 0 ≤ P.a) (hβ : 0 ≤ P.β)
    (hX : 1 ≤ P.Xp) (hsB : ∀ p ∈ sB, p.Prime ∧ (p : ℝ) ≤ P.Xp)
    (hTops : ∑ p ∈ sB, 4 * m * P.a * (Real.log p / p) * ((TT.filter fun t => BAD p t).card : ℝ) ≤
      32 * P.β * m * P.a * TT.card * ∑ p ∈ sB, Real.log p / p)
    (hBad : ∀ p ∈ Ps, cl p = PClass.served → ∀ t ∈ TT \ TTp p, p ∈ sB ∧ BAD p t) :
    ∑ p ∈ Ps.filter (fun p => cl p = PClass.served),
      4 * m * P.a * (Real.log p / p) * ((TT \ TTp p).card : ℝ) ≤ tBad P m TT.card := by
  have hco : ∀ p : ℕ, 0 ≤ 4 * m * P.a * (Real.log p / p) := fun p => by
    have : 0 ≤ Real.log p / p := div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)
    positivity
  have h1 : ∑ p ∈ Ps.filter (fun p => cl p = PClass.served),
      4 * m * P.a * (Real.log p / p) * ((TT \ TTp p).card : ℝ) ≤
      ∑ p ∈ Ps.filter (fun p => cl p = PClass.served),
        (if p ∈ sB then 4 * m * P.a * (Real.log p / p) * ((TT.filter fun t => BAD p t).card : ℝ)
          else 0) := by
    refine Finset.sum_le_sum (fun p hp => ?_)
    rw [Finset.mem_filter] at hp
    have hb := hBad p hp.1 hp.2
    by_cases hps : p ∈ sB
    · rw [if_pos hps]
      refine mul_le_mul_of_nonneg_left ?_ (hco p)
      have hsub : TT \ TTp p ⊆ TT.filter fun t => BAD p t := by
        intro t ht
        rw [Finset.mem_filter]
        exact ⟨(Finset.mem_sdiff.1 ht).1, (hb t ht).2⟩
      exact_mod_cast Finset.card_le_card hsub
    · rw [if_neg hps]
      have hemp : TT \ TTp p = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro t ht
        exact hps (hb t ht).1
      rw [hemp]; simp
  have h2 : ∑ p ∈ Ps.filter (fun p => cl p = PClass.served),
        (if p ∈ sB then 4 * m * P.a * (Real.log p / p) * ((TT.filter fun t => BAD p t).card : ℝ)
          else 0) ≤
      ∑ p ∈ sB, 4 * m * P.a * (Real.log p / p) * ((TT.filter fun t => BAD p t).card : ℝ) := by
    rw [← Finset.sum_filter]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun p _ _ => mul_nonneg (hco p) (Nat.cast_nonneg _))
    intro p hp
    exact (Finset.mem_filter.1 hp).2
  have h3 := prime_log_sum_bound P.Xp sB hX hsB
  have h4 : 32 * P.β * m * P.a * TT.card * ∑ p ∈ sB, Real.log p / p ≤
      32 * P.β * m * P.a * TT.card * (Real.log P.Xp + Real.log 4) :=
    mul_le_mul_of_nonneg_left h3 (by positivity)
  unfold tBad
  linarith

lemma first_le {C₁ : ℝ}
    (hC₁ : ∀ (e J : ℕ) (Y X' ρ p₀ : ℝ) (s : Finset ℕ), 1 ≤ e → 1 ≤ J → 1 ≤ Y →
      0 ≤ ρ → ρ ≤ 1 / 2 → 8 ≤ p₀ → 2 ≤ X' →
      (∀ p ∈ s, p.Prime ∧ p ≠ 2 ∧
        (((p : ℝ) ≤ Y ∧ ∃ hl : Nat.Coprime p (4 * 2 ^ e), orderOf (Formalism.RankGapBounds.LocalQuadraticParts.hOf e p hl) ≤ J) ∨
          (p₀ ≤ p ∧ ∃ i : ℕ, 1 ≤ i ∧ X' * (1 - ρ) ≤ (p : ℝ) ^ i ∧ (p : ℝ) ^ i ≤ X' * (1 + ρ)))) →
      ∑ p ∈ s, Real.log p / p ≤
        C₁ * J * Real.log (2 ^ e * Y) ^ 2 / (2 : ℝ) ^ e +
          (⌊Real.log X'⌋₊ : ℝ) * ((4 * ρ + 1 / p₀) * Real.log (2 * X')))
    {P : Par} {e K : ℝ} (hCord : C₁ ≤ P.Cord) (hW : Windows P e K) (hL : LargeX P.x P.ε e K)
    (Ps : Finset ℕ) (cl : ℕ → PClass) (hPs : ∀ p ∈ Ps, p.Prime ∧ p ≠ 2) (hF : FirstHyp P Ps cl)
    (m T : ℝ) (hm : 0 ≤ m) (hT : 0 ≤ T) :
    4 * m * T * P.a * (∑ p ∈ Ps.filter (fun p => cl p = PClass.first), Real.log p / p) ≤
      tOrders P m T + tBand P m T := by
  obtain ⟨z, u, E, X, S, sb, v, w8, F⟩ := facts hW hL
  have hx := F.hx
  have hx2 : P.x ≤ P.x ^ 2 := by
    calc P.x = P.x ^ 1 := (pow_one _).symm
      _ ≤ P.x ^ 2 := pow_le_pow_right₀ F.x1 (by norm_num)
  have hx4 : P.x ≤ P.x ^ 4 := by
    calc P.x = P.x ^ 1 := (pow_one _).symm
      _ ≤ P.x ^ 4 := pow_le_pow_right₀ F.x1 (by norm_num)
  have he2 : 1 ≤ P.e₂ := by
    rw [Nat.one_le_iff_ne_zero]
    intro h0
    have h1 := F.n2x
    rw [h0, pow_zero] at h1
    linarith
  have hJo : 1 ≤ P.Jo := by
    unfold Par.Jo
    apply Nat.le_floor
    rw [Nat.cast_one]
    exact Real.one_le_rpow F.x1 (by have := hW.1; positivity)
  have hρ : P.ρ ≤ 1 / 2 := by
    have h1 : (P.x ^ 2)⁻¹ ≤ (100 : ℝ)⁻¹ := inv_anti₀ (by norm_num) (by linarith)
    have := F.ρx
    norm_num at h1
    linarith
  have hp8 : (8 : ℝ) ≤ (P.p₀ : ℝ) := by linarith [F.px]
  have hX2 : 2 ≤ P.Xp := by
    rw [F.hXp]
    have := F.one_le_threshold_mul_powers; have := F.hXB
    linarith
  have hIb : ⌊Real.log P.Xp⌋₊ = P.Ib := by
    rw [F.hXp, F.logX, F.hu]; rfl
  have h := hC₁ P.e₂ P.Jo (max P.Y P.Xpp) P.Xp P.ρ (P.p₀ : ℝ) (Ps.filter (fun p => cl p = PClass.first)) he2 hJo
    (F.Y1.trans (le_max_left _ _))
    F.ρ0 hρ hp8 hX2 (by
      intro p hp
      rw [Finset.mem_filter] at hp
      refine ⟨(hPs p hp.1).1, (hPs p hp.1).2, ?_⟩
      rcases hF p hp.1 hp.2 with ⟨a1, hl, a2⟩ | ⟨b1, b2⟩
      · exact Or.inl ⟨a1, hl, Nat.le_floor a2.le⟩
      · exact Or.inr ⟨by exact_mod_cast b1, b2⟩)
  rw [hIb] at h
  have hn0 : (0 : ℝ) < 2 ^ P.e₂ := by positivity
  have hJ0 : (0 : ℝ) ≤ P.Jo := Nat.cast_nonneg _
  have h2 : C₁ * P.Jo * Real.log (2 ^ P.e₂ * max P.Y P.Xpp) ^ 2 / (2 : ℝ) ^ P.e₂ ≤
      P.Cord * P.Jo * Real.log (2 ^ P.e₂ * max P.Y P.Xpp) ^ 2 / (2 : ℝ) ^ P.e₂ := by gcongr
  have hco : 0 ≤ 4 * m * T * P.a := by
    have := F.apos
    positivity
  have h3 := mul_le_mul_of_nonneg_left (h.trans (add_le_add_left h2 _)) hco
  unfold tOrders tBand
  linarith

theorem joint_size_bound_alt : WindowLossesBound := by
  obtain ⟨C₁, hC₁⟩ := first_kind_bound
  refine ⟨max C₁ 0, le_max_right _ _, ?_⟩
  intro P e K hCord hW hL ι κ τ U Ω _ π Ps s sB J TT BAD Sig io D hS
  obtain ⟨hTT, hPs, hπ0, hπ1, hs, hSig0, hSigm, hio, hsB, hTops, hAll⟩ := hS
  obtain ⟨z, u, E, X, S, sb, v, w8, F⟩ := facts hW hL
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, -⟩ :=
    side_condition_of_windows P e K hW hL
  have hm : (0 : ℝ) ≤ (J.card : ℝ) := Nat.cast_nonneg _
  have hT : (1 : ℝ) ≤ (TT.card : ℝ) := by exact_mod_cast Finset.card_pos.2 hTT
  have hT0 : (0 : ℝ) ≤ (TT.card : ℝ) := Nat.cast_nonneg _
  have ha0 : 0 ≤ P.a := F.apos.le
  have hdet : ∀ υ o, (D υ o).ASK P.d Ps J TT - (D υ o).Ga J ≤ tDet P J.card TT.card +
      ∑ p ∈ s, (if P.θ < Sig p o then 4 * ((J.card : ℝ) * TT.card * P.a) * Real.log p / p else 0) := by
    intro υ o
    obtain ⟨hLed, hFirst, hSecond, hBad⟩ := hAll υ o
    obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11⟩ := hLed
    have led := loss_bound ι κ τ (D υ o).W (D υ o).below (D υ o).l Ps (D υ o).cl J TT (D υ o).TTp
      (D υ o).Iex (D υ o).at_ (D υ o).wz (D υ o).Id (D υ o).wd P.d (D υ o).gainW (D υ o).tauW
      (D υ o).gain (D υ o).tau (D υ o).lo (D υ o).fl P.a P.th P.wpp P.Xpp P.Xp P.C P.f P.N P.Sk P.Q₁ P.Q₂
      P.lx P.La P.k P.K₀ (D υ o).L₁ P.p₀ l1 (fun p hp => (hPs p hp).1) s1 s2 s3 s4 s5 s6 s7 s8 s9 s10
      s11 s12 s13 s14 s15 s16 s17 s18 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11
    have bad := bad_le P Ps sB (D υ o).cl TT (D υ o).TTp BAD J.card hm ha0 F.β0 s7 hsB hTops hBad
    have first := first_le hC₁ (by rw [hCord]; exact le_max_left _ _) hW hL Ps (D υ o).cl hPs hFirst
      J.card TT.card hm hT0
    have second := second_term_le Ps s (D υ o).cl (fun p => Sig p o) P.θ J.card TT.card P.a hm hT0 ha0
      hSecond
    unfold LD.ASK LD.Ga tDet tFloors tCp tPrLow tPrHigh tOr tHigh tD
    linarith
  have hθ : 0 < P.θ := by rw [F.hθ]; exact inv_pos.2 F.zpos
  obtain ⟨o, o1, o2, o3⟩ := loss_choice_uniform Ω U π
    (fun υ o => (D υ o).ASK P.d Ps J TT - (D υ o).Ga J) s Sig io (fun _ => tDet P J.card TT.card)
    P.Y P.θ P.s₀ ((J.card : ℝ) * TT.card * P.a) hπ0 hπ1 hθ F.s0 (by positivity) F.Y1 hs hSig0 hSigm
    hdet hio
  refine ⟨o, o1, fun υ => ?_, fun υ => ?_⟩
  · have h1 := o2 υ
    have h2 := size_total_bound P e K J.card TT.card hW hL hm hT
    unfold tSecondIo at h2
    linarith
  · have h1 := o3 υ
    have h2 := secondIo_le_unit hW hL hm hT
    unfold tSecondIo at h2
    linarith

theorem joint_bound_eventually : WindowLossesEventual := by
  obtain ⟨Cord, h0, h⟩ := joint_size_bound_alt
  refine ⟨Cord, h0, ?_⟩
  intro ε e K hε hε4
  obtain ⟨x₀, hx₀⟩ := large_x_eventually ε e K hε hε4
  refine ⟨x₀, ?_⟩
  intro P hPε hPC hx hW
  exact h P e K hPC hW (by rw [hPε]; exact hx₀ _ hx)

open Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds in
theorem losses_of_setting : LeadingTermLossesOfWindow := by
  intro P ι κ τ U U0 Ω Ps s J TT io D o sel W Top _ m f Dd Cc hC hx hε hC0 dx dε db dT dm dA dG dI hc he
  obtain ⟨c1, c2⟩ := hC
  have hb : 0 < P.b := Real.exp_pos _
  have hU : 0 ≤ unitU P J.card TT.card := by unfold unitU; positivity
  have hy : 1 ≤ P.x ^ (Cc.eLoss * P.ε) := Real.one_le_rpow hx (mul_nonneg he hε)
  have hLo : Dd.LoP Cc = Cc.cLoss * unitU P J.card TT.card * P.x ^ (Cc.eLoss * P.ε) := by
    unfold Data.LoP Data.nT unitU
    rw [dx, dε, db, dT, dm]
    ring
  have hc0 : 0 ≤ Cc.cLoss := by linarith
  have h1 : (3 * P.C + 13) * unitU P J.card TT.card ≤ Dd.LoP Cc := by
    rw [hLo]
    calc (3 * P.C + 13) * unitU P J.card TT.card ≤ Cc.cLoss * unitU P J.card TT.card :=
          mul_le_mul_of_nonneg_right hc hU
      _ ≤ Cc.cLoss * unitU P J.card TT.card * P.x ^ (Cc.eLoss * P.ε) :=
          le_mul_of_one_le_right (mul_nonneg hc0 hU) hy
  have h2 : unitU P J.card TT.card ≤ (3 * P.C + 13) * unitU P J.card TT.card := by
    have : (1 : ℝ) ≤ 3 * P.C + 13 := by linarith
    exact le_mul_of_one_le_left hU this
  intro u0
  refine ⟨?_, ?_⟩
  · rw [dA, dG]; exact (c1 (sel u0)).trans h1
  · rw [dI]; exact (c2 (sel u0)).trans (h2.trans h1)

end Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
