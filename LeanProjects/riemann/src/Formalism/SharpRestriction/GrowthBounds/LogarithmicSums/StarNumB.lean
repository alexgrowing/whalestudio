import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.NumData

noncomputable section

open scoped BigOperators
open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.G Filter
open Formalism.MainNotions.AuxBlock8.Pf.G5.Nu

namespace Formalism.MainNotions.AuxBlock8.Pf.St.B

def cGE (eps : ℝ) : ℝ := (((2 + 8 * eps + 3) * 10 ^ (6 * rE eps + 1) + 1) + 5) * (6 * (rE eps : ℝ) + 1) * 2

def cNE (eps : ℝ) : ℝ := 18 * cGE eps + 2 * (2 + 8 * eps + 3) + 2

theorem cGE_nonneg (eps : ℝ) (he : 0 < eps) : 0 ≤ cGE eps := by unfold cGE; positivity

theorem inv_delta1 (s : Scale) : 1 / s.delta1 = s.x ^ (s.eps / 8) := by
  unfold Scale.delta1
  rw [Real.rpow_neg (sc_x_pos s).le, one_div, inv_inv]

theorem one_le_xpow (s : Scale) (y : ℝ) (hy : 0 ≤ y) : 1 ≤ s.x ^ y := Real.one_le_rpow s.one_lt_alt.le hy

theorem Gp_le (s : Scale) (hx : Real.exp 1 ≤ s.x) :
    (Gp s : ℝ) ≤ cGE s.eps * Real.log s.x * s.x ^ (s.eps / 8) := by
  have he := s.eps_pos
  have hx0 := sc_x_pos s
  have lx1 : 1 ≤ Real.log s.x := (Real.le_log_iff_exp_le hx0).2 hx
  have hy1 : 1 ≤ s.x ^ (s.eps / 8) := one_le_xpow s _ (by positivity)
  have hU : ((goodU s.delta1 : ℕ) : ℝ) ≤ 2 * s.x ^ (s.eps / 8) := by
    unfold goodU
    rw [inv_delta1]
    have := Nat.ceil_lt_add_one (le_trans zero_le_one hy1)
    linarith
  have hM : ((orbitSmallMultiplicity (rG s) (hG s) s.x : ℕ) : ℝ) ≤ ((2 + 8 * s.eps + 3) * 10 ^ (6 * rE s.eps + 1) + 1) * Real.log s.x := by
    unfold orbitSmallMultiplicity hG
    rw [rG_rE, zpow_neg, div_inv_eq_mul, zpow_natCast]
    have h0 : 0 ≤ (2 + 8 * s.eps + 3) * Real.log s.x * 10 ^ (6 * rE s.eps + 1) := by positivity
    have := Nat.ceil_lt_add_one h0
    nlinarith
  unfold Gp goodG' goodEll
  push_cast
  rw [rG_rE] at hM ⊢
  unfold cGE
  have h5 : ((orbitSmallMultiplicity (rE s.eps) (hG s) s.x : ℕ) : ℝ) + 5 ≤
      (((2 + 8 * s.eps + 3) * 10 ^ (6 * rE s.eps + 1) + 1) + 5) * Real.log s.x := by nlinarith
  have h6 : (6 * (rE s.eps : ℝ) + 1) * ((goodU s.delta1 : ℕ) : ℝ) ≤ (6 * (rE s.eps : ℝ) + 1) * (2 * s.x ^ (s.eps / 8)) :=
    mul_le_mul_of_nonneg_left hU (by positivity)
  calc (((orbitSmallMultiplicity (rE s.eps) (hG s) s.x : ℕ) : ℝ) + 5) * ((6 * (rE s.eps : ℝ) + 1) * ((goodU s.delta1 : ℕ) : ℝ))
      ≤ ((((2 + 8 * s.eps + 3) * 10 ^ (6 * rE s.eps + 1) + 1) + 5) * Real.log s.x) *
          ((6 * (rE s.eps : ℝ) + 1) * (2 * s.x ^ (s.eps / 8))) :=
        mul_le_mul h5 h6 (by positivity) (by positivity)
    _ = _ := by ring

theorem first_count_le_log (s : Scale) (hx : Real.exp 1 ≤ s.x) : (N1 s : ℝ) ≤ cNE s.eps * Real.log s.x := by
  have he := s.eps_pos
  have hx0 := sc_x_pos s
  have lx1 : 1 ≤ Real.log s.x := (Real.le_log_iff_exp_le hx0).2 hx
  have hGp := Gp_le s hx
  have hc := cGE_nonneg s.eps he
  have hd : s.x ^ (s.eps / 8) * s.delta1 = 1 := by
    unfold Scale.delta1
    rw [← Real.rpow_add hx0]; simp
  have hd0 := sc_delta1_pos s
  have h1 : (Gp s : ℝ) * s.delta1 ≤ cGE s.eps * Real.log s.x := by
    calc (Gp s : ℝ) * s.delta1 ≤ cGE s.eps * Real.log s.x * s.x ^ (s.eps / 8) * s.delta1 :=
          mul_le_mul_of_nonneg_right hGp hd0.le
      _ = cGE s.eps * Real.log s.x := by rw [mul_assoc, hd, mul_one]
  have he3 : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
  have h0 : 0 ≤ (Gp s : ℝ) * s.delta1 := by positivity
  have h2 : 6 * Real.exp 1 * (Gp s : ℝ) * s.delta1 ≤ 18 * cGE s.eps * Real.log s.x := by
    have : 6 * Real.exp 1 * ((Gp s : ℝ) * s.delta1) ≤ 18 * ((Gp s : ℝ) * s.delta1) :=
      mul_le_mul_of_nonneg_right (by linarith) h0
    nlinarith
  have h3 : (hG s + 3) * Real.logb 2 s.x ≤ 2 * (2 + 8 * s.eps + 3) * Real.log s.x := by
    unfold Formalism.MainNotions.G.hG Real.logb
    have hl2 : (1 / 2 : ℝ) ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
    have : Real.log s.x / Real.log 2 ≤ 2 * Real.log s.x := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    have h4 : 0 ≤ 2 + 8 * s.eps + 3 := by positivity
    nlinarith
  have hmax : max (6 * Real.exp 1 * (Gp s : ℝ) * s.delta1) ((hG s + 3) * Real.logb 2 s.x) ≤
      (18 * cGE s.eps + 2 * (2 + 8 * s.eps + 3)) * Real.log s.x := by
    have a1 : 0 ≤ 18 * cGE s.eps * Real.log s.x := by positivity
    have a2 : 0 ≤ 2 * (2 + 8 * s.eps + 3) * Real.log s.x := by positivity
    apply max_le <;> nlinarith
  have hpos : 0 ≤ max (6 * Real.exp 1 * (Gp s : ℝ) * s.delta1) ((hG s + 3) * Real.logb 2 s.x) :=
    le_max_of_le_left (by positivity)
  have hceil := Nat.ceil_lt_add_one hpos
  have hN : (N1 s : ℝ) = (⌈max (6 * Real.exp 1 * (Gp s : ℝ) * s.delta1) ((hG s + 3) * Real.logb 2 s.x)⌉₊ : ℝ) + 1 := by
    unfold N1 orbitWindowCount Gp
    push_cast
    rfl
  rw [hN]
  unfold cNE
  nlinarith

theorem hboB_arith (Y Pr1 G η c Nm kappaThresholdTwo Q DIf N k lb n' C31 lx DI v N1 Np : ℝ) (hY : 130 ≤ Y)
    (a1 : 0 ≤ Pr1) (b1 : Pr1 ≤ Y) (a2 : 0 ≤ G) (b2 : G ≤ Y) (a3 : 0 ≤ η) (b3 : η ≤ Y) (a4 : 0 ≤ c) (b4 : c ≤ Y)
    (a5 : 0 ≤ Nm) (b5 : Nm ≤ Y) (a6 : 0 ≤ kappaThresholdTwo) (b6 : kappaThresholdTwo ≤ Y) (a7 : 0 ≤ Q) (b7 : Q ≤ Y) (a8 : 0 ≤ DI) (b8 : DI ≤ Y)
    (a9 : 0 ≤ N) (b9 : N ≤ Y) (a10 : 0 ≤ k) (b10 : k ≤ Y) (a11 : 0 ≤ lb) (b11 : lb ≤ Y) (a12 : 0 ≤ n') (b12 : n' ≤ Y)
    (a13 : 0 ≤ C31) (b13 : C31 ≤ Y) (a14 : 0 ≤ lx) (b14 : lx ≤ Y) (a15 : 0 ≤ v) (b15 : v ≤ Y) (a16 : 0 ≤ N1)
    (b16 : N1 ≤ Y) (a17 : 0 ≤ Np) (b17 : Np ≤ Y) (a18 : 0 ≤ DIf)
    (hD : DIf ≤ DI * Np * v ^ 2 * (N1 ^ 5 + k ^ 3) * lb + 1) :
    Pr1 * G * (η + c + Nm) + kappaThresholdTwo * (Q * (8 * (DIf + 1) + kappaThresholdTwo * N * k * lb + 4 * N * c + 2 * n' * c) + k * Q +
      k * lb + c) + 2 * G * c + 40 * C31 * lx * (DI * v ^ 2 * (N1 ^ 5 + k ^ 3) * lb) + 3 ≤ Y ^ 13 := by
  have hY0 : 0 ≤ Y := by linarith
  have hY1 : 1 ≤ Y := by linarith
  have hD' : DIf ≤ Y * Y * Y ^ 2 * (Y ^ 5 + Y ^ 3) * Y + 1 := le_trans hD (by gcongr)
  have h1 : Pr1 * G * (η + c + Nm) + kappaThresholdTwo * (Q * (8 * (DIf + 1) + kappaThresholdTwo * N * k * lb + 4 * N * c + 2 * n' * c) + k * Q +
      k * lb + c) + 2 * G * c + 40 * C31 * lx * (DI * v ^ 2 * (N1 ^ 5 + k ^ 3) * lb) + 3 ≤
      Y * Y * (Y + Y + Y) + Y * (Y * (8 * ((Y * Y * Y ^ 2 * (Y ^ 5 + Y ^ 3) * Y + 1) + 1) + Y * Y * Y * Y + 4 * Y * Y +
        2 * Y * Y) + Y * Y + Y * Y + Y) + 2 * Y * Y + 40 * Y * Y * (Y * Y ^ 2 * (Y ^ 5 + Y ^ 3) * Y) + 3 := by gcongr
  have h2 : Y * Y * (Y + Y + Y) + Y * (Y * (8 * ((Y * Y * Y ^ 2 * (Y ^ 5 + Y ^ 3) * Y + 1) + 1) + Y * Y * Y * Y + 4 * Y * Y +
        2 * Y * Y) + Y * Y + Y * Y + Y) + 2 * Y * Y + 40 * Y * Y * (Y * Y ^ 2 * (Y ^ 5 + Y ^ 3) * Y) + 3 =
      8 * Y ^ 12 + 40 * Y ^ 11 + 8 * Y ^ 10 + 40 * Y ^ 9 + Y ^ 6 + 6 * Y ^ 4 + 5 * Y ^ 3 + 19 * Y ^ 2 + 3 := by ring
  have p : ∀ i : ℕ, i ≤ 12 → Y ^ i ≤ Y ^ 12 := fun i hi => pow_le_pow_right₀ hY1 hi
  have p11 := p 11 (by norm_num)
  have p10 := p 10 (by norm_num)
  have p9 := p 9 (by norm_num)
  have p6 := p 6 (by norm_num)
  have p4 := p 4 (by norm_num)
  have p3 := p 3 (by norm_num)
  have p2 := p 2 (by norm_num)
  have p0 : 1 ≤ Y ^ 12 := one_le_pow₀ hY1
  have p13 : 130 * Y ^ 12 ≤ Y ^ 13 := by
    calc 130 * Y ^ 12 ≤ Y * Y ^ 12 := mul_le_mul_of_nonneg_right hY (by positivity)
      _ = Y ^ 13 := by ring
  linarith

theorem hDII_arith (Y DII N1 r k lb : ℝ) (hY : 130 ≤ Y) (a1 : 0 ≤ DII) (b1 : DII ≤ Y) (a2 : 0 ≤ N1) (b2 : N1 ≤ Y)
    (a3 : 0 ≤ r) (b3 : r ≤ Y) (a4 : 0 ≤ k) (b4 : k ≤ Y) (a5 : 0 ≤ lb) (b5 : lb ≤ Y) :
    DII * (N1 ^ 3 + r ^ 5 + k ^ 2) * lb ≤ Y ^ 8 := by
  have hY0 : 0 ≤ Y := by linarith
  have hY1 : 1 ≤ Y := by linarith
  have h1 : DII * (N1 ^ 3 + r ^ 5 + k ^ 2) * lb ≤ Y * (Y ^ 3 + Y ^ 5 + Y ^ 2) * Y := by gcongr
  have h2 : Y * (Y ^ 3 + Y ^ 5 + Y ^ 2) * Y = Y ^ 5 + Y ^ 7 + Y ^ 4 := by ring
  have p5 : Y ^ 5 ≤ Y ^ 7 := pow_le_pow_right₀ hY1 (by norm_num)
  have p4 : Y ^ 4 ≤ Y ^ 7 := pow_le_pow_right₀ hY1 (by norm_num)
  have p8 : 130 * Y ^ 7 ≤ Y ^ 8 := by
    calc 130 * Y ^ 7 ≤ Y * Y ^ 7 := mul_le_mul_of_nonneg_right hY (by positivity)
      _ = Y ^ 8 := by ring
  have : 0 ≤ Y ^ 7 := by positivity
  linarith

structure Facts (D : D7) (L : SizeData₂ D) (K : Consts) (C31 bo : ℝ) : Prop where
  hkQ : ∀ p : ℕ, p.Prime → (p : ℝ) < L.sc.p0 D.R.k → (D.R.k : ℝ) * Qp L.sc p ≤ L.sc.b'
  hDII : ∀ p : ℕ, p.Prime →
    K.DII * ((N1 L.sc : ℝ) ^ 3 + (rG L.sc : ℝ) ^ 5 + (D.R.k : ℝ) ^ 2) * Real.logb p L.sc.a ≤ L.sc.b'
  hbo : ∀ p : ℕ, p.Prime → L.sc.p0 D.R.k ≤ (p : ℝ) → (p : ℝ) < L.sc.X' → ∀ n' : ℕ, n' ≤ D.R.n →
    K.Pr1 * (C31 * Real.log L.sc.x / L.sc.delta1) * (L.etaSz + cG L + Nm D) +
      K.kappaThresholdTwo * (Qp L.sc p * c6f K L p n' +
        (D.R.k : ℝ) * Qp L.sc p + (D.R.k : ℝ) * Real.logb p L.sc.a + cG L) +
      2 * (C31 * Real.log L.sc.x / L.sc.delta1) * cG L +
      40 * C31 * Real.log L.sc.x * (K.DI * (L.sc.x ^ (Scale.A / 2)) ^ 2 *
        ((N1 L.sc : ℝ) ^ 5 + (D.R.k : ℝ) ^ 3) * Real.logb p L.sc.a) + 3 ≤ bo

set_option maxHeartbeats 8000000 in
theorem facts_ev (eps : ℝ) (K : Consts) (hK : K.Nonneg) (C31 : ℝ) (hC31 : 0 < C31) :
    ∀ᶠ x : ℝ in atTop, ∀ (D : D7) (L : SizeData₂ D), L.sc.x = x → L.sc.eps = eps → Formalism.MainNotions.SizesAt L →
      ParameterChoice' D L → adm5 D L K (eps / 48) → Facts D L K C31 (L.sc.b ^ (x ^ (-(eps / 2)))) := by
  by_cases he : 0 < eps ∧ eps < 1 / 52
  swap
  · refine Filter.Eventually.of_forall fun x D L _ h2 => ?_
    exact absurd ⟨h2 ▸ L.sc.eps_pos, h2 ▸ L.sc.eps_lt⟩ he
  obtain ⟨he0, he1⟩ := he
  have hτ : 0 < 23 * eps / 48 := by positivity
  have F1 := ev_log 14 (23 * eps / 48) hτ
  have F2 := ev_const 130 (23 * eps / 48) hτ
  have G1 := ev_const K.Pr1 (23 * eps / 48) hτ
  have G2 := ev_const K.kappaThresholdTwo (23 * eps / 48) hτ
  have G3 := ev_const K.DI (23 * eps / 48) hτ
  have G4 := ev_const K.DII (23 * eps / 48) hτ
  have G5 := ev_const C31 (23 * eps / 48) hτ
  have G6 := ev_const (rE eps : ℝ) (23 * eps / 48) hτ
  have F4 := ev_log 1 eps he0
  have F5 := ev_pow 3 eps 1 (by linarith)
  have F6 := ev_pow 14 (23 * eps / 48) eps (by linarith)
  have F7 := ev_pow 4 (eps / 3) eps (by linarith)
  have F8 := ev_pow 13 (23 * eps / 48) (eps / 2) (by linarith)
  have F9 := ev_log C31 1 one_pos
  have WorkedExample := ev_log (cNE eps) 1 one_pos
  filter_upwards [F1, F2, G1, G2, G3, G4, G5, G6, F4, F5, F6, F7, F8, F9, WorkedExample, eventually_ge_atTop 40,
    eventually_ge_atTop (Real.exp 1)] with x f1 f2 g1 g2 g3 g4 g5 g6 f4 f5 f6 f7 f8 f9 f10 hx40 hxe D L hx heps hS P h5
  subst hx
  subst heps
  obtain ⟨_, _, _, _, hDII0, _, _, hDI0, _, htI20, _, _, _, hPr10, _⟩ := hK
  have hx0 := sc_x_pos L.sc
  have hx1 := L.sc.one_lt_alt
  have hlx0 : 0 ≤ Real.log L.sc.x := Real.log_nonneg hx1.le
  have hk1 := one_le_k D
  have hk6 := k_le_x_pow_six L hS
  have hk0 : (0 : ℝ) < (D.R.k : ℝ) := by linarith
  obtain ⟨_, hNmSc, hSc100⟩ := Nm_le_Sc P
  obtain ⟨hSN, -, -, -, -, -, -, -, -, -, -, -, -, hSEta, -, -, hSDel, -⟩ := hS
  unfold Formalism.MainNotions.SizeN Formalism.MainNotions.szTh at hSN
  unfold Formalism.MainNotions.SizeEta at hSEta
  unfold Formalism.MainNotions.SizeDel at hSDel
  rw [Real.rpow_one] at f5 f9 f10
  have mono : ∀ u v : ℝ, u ≤ v → L.sc.x ^ u ≤ L.sc.x ^ v := fun u v h => Real.rpow_le_rpow_of_exponent_le hx1.le h
  have nat3 : L.sc.x ^ (3 : ℝ) = L.sc.x ^ 3 := by rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have nat6 : L.sc.x ^ (6 : ℝ) = L.sc.x ^ 6 := by rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have natA2 : L.sc.x ^ (Scale.A / 2) = L.sc.x ^ 13 := by
    unfold Scale.A; rw [show (26 / 2 : ℝ) = ((13 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hn3 : (D.R.n : ℝ) ≤ L.sc.x ^ 3 := by rw [← nat3]; exact le_trans hSN.2 (mono _ _ (by linarith))
  rw [nat6] at hk6
  have hxe1 : 1 ≤ L.sc.x ^ L.sc.eps := Real.one_le_rpow hx1.le he0.le
  have hb : L.sc.b = Real.exp (L.sc.x ^ L.sc.eps) := rfl
  have ha : L.sc.a = L.sc.x * L.sc.b := rfl
  have hY130 : 130 ≤ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) := f2
  have hY0 : 0 < (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) := Real.exp_pos _
  have pY : ∀ q : ℝ, ∀ M : ℕ, q ≤ L.sc.x ^ M → M ≤ 14 → q ≤ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) := by
    intro q M hq hM
    refine le_trans hq ?_
    rw [← Real.rpow_natCast]
    apply xpow_le_exp _ _ _ hx0
    have : (M : ℝ) ≤ 14 := by exact_mod_cast hM
    exact le_trans (mul_le_mul_of_nonneg_right this hlx0) f1
  have e_eta : L.etaSz ≤ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) :=
    calc L.etaSz ≤ Real.exp (Real.log L.etaSz) := Real.le_exp_log _
      _ ≤ Real.exp (L.sc.x ^ (L.sc.eps / 4)) := Real.exp_le_exp.2 hSEta.2.2.1
      _ ≤ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) := Real.exp_le_exp.2 (mono _ _ (by linarith))
  have hT4 : L.sc.x ^ (L.sc.eps / 4) ≤ (L.sc.x ^ (23 * L.sc.eps / 48)) := mono _ _ (by linarith)
  have e_Del : (D.s.Del : ℝ) ≤ Real.exp ((L.sc.x ^ (23 * L.sc.eps / 48)) / 2) :=
    calc (D.s.Del : ℝ) ≤ Real.exp (Real.log (D.s.Del : ℝ)) := Real.le_exp_log _
      _ ≤ Real.exp (L.sc.x ^ (L.sc.eps / 4) / 2) := Real.exp_le_exp.2 hSDel.2.2.1
      _ ≤ _ := Real.exp_le_exp.2 (by linarith)
  have hDel0 : (0 : ℝ) ≤ (D.s.Del : ℝ) := by
    have h := L.Sc_eq
    by_contra hneg
    have : (D.R.k : ℝ) * (4 * (D.s.Del : ℝ)) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hk0.le (by linarith)
    linarith
  have h7 : L.sc.x * L.sc.x ^ 6 ≤ Real.exp ((L.sc.x ^ (23 * L.sc.eps / 48)) / 2) := by
    have : L.sc.x * L.sc.x ^ 6 = L.sc.x ^ ((7 : ℕ) : ℝ) := by rw [Real.rpow_natCast]; ring
    rw [this]
    apply xpow_le_exp _ _ _ hx0
    push_cast
    linarith
  have hcG0 : 0 ≤ cG L := by unfold cG; linarith
  have e_c : cG L ≤ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) :=
    calc cG L = (16 * (D.R.k : ℝ)) * (D.s.Del : ℝ) := by unfold cG; rw [L.Sc_eq]; ring
      _ ≤ (L.sc.x * L.sc.x ^ 6) * Real.exp ((L.sc.x ^ (23 * L.sc.eps / 48)) / 2) :=
          mul_le_mul (mul_le_mul (by linarith) hk6 hk0.le hx0.le) e_Del hDel0 (by positivity)
      _ ≤ Real.exp ((L.sc.x ^ (23 * L.sc.eps / 48)) / 2) * Real.exp ((L.sc.x ^ (23 * L.sc.eps / 48)) / 2) := mul_le_mul_of_nonneg_right h7 (Real.exp_pos _).le
      _ = (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) := by rw [← Real.exp_add]; congr 1; ring
  have e_Nm : Nm D ≤ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) := by
    have : Nm D ≤ cG L := by unfold Nm cG; linarith
    linarith
  have hNm0 : 0 ≤ Nm D := by unfold Nm; exact Nat.cast_nonneg _
  have e_n : (D.R.n : ℝ) ≤ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) := pY _ 3 hn3 (by norm_num)
  have e_k : (D.R.k : ℝ) ≤ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) := pY _ 6 hk6 (by norm_num)
  have e_v : L.sc.x ^ (Scale.A / 2) ≤ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) := pY _ 13 (le_of_eq natA2) (by norm_num)
  have hxY : L.sc.x ≤ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) := pY _ 1 (by rw [pow_one]) (by norm_num)
  have e_lx : Real.log L.sc.x ≤ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) := by linarith
  have hla : Real.log L.sc.a = Real.log L.sc.x + L.sc.x ^ L.sc.eps := by
    rw [ha, hb, Real.log_mul hx0.ne' (Real.exp_pos _).ne', Real.log_exp]
  have hla0 : 0 ≤ Real.log L.sc.a := by rw [hla]; positivity
  have hlaX : 2 * Real.log L.sc.a ≤ L.sc.x ^ 2 := by
    rw [hla]
    have : 2 * L.sc.x ≤ L.sc.x ^ 2 := by rw [pow_two]; exact mul_le_mul_of_nonneg_right (by linarith) hx0.le
    linarith
  have e_lb : ∀ p : ℕ, p.Prime → 0 ≤ Real.logb p L.sc.a ∧ Real.logb p L.sc.a ≤ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hl2 : (1 / 2 : ℝ) ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
    have hlp : (1 / 2 : ℝ) ≤ Real.log p := le_trans hl2 (Real.log_le_log (by norm_num) hp2)
    unfold Real.logb
    refine ⟨div_nonneg hla0 (by linarith), ?_⟩
    refine pY _ 2 (le_trans ?_ hlaX) (by norm_num)
    rw [div_le_iff₀ (by linarith)]
    calc Real.log L.sc.a = 2 * Real.log L.sc.a * (1 / 2) := by ring
      _ ≤ 2 * Real.log L.sc.a * Real.log p := mul_le_mul_of_nonneg_left hlp (by linarith)
  have hd : 1 / L.sc.delta1 = L.sc.x ^ (L.sc.eps / 8) := inv_delta1 L.sc
  have h8 : L.sc.x ^ (L.sc.eps / 8) ≤ L.sc.x := by
    have := mono (L.sc.eps / 8) 1 (by linarith)
    rwa [Real.rpow_one] at this
  have h80 : 0 ≤ L.sc.x ^ (L.sc.eps / 8) := Real.rpow_nonneg hx0.le _
  have hG0 : 0 ≤ C31 * Real.log L.sc.x / L.sc.delta1 := div_nonneg (mul_nonneg hC31.le hlx0) (sc_delta1_pos L.sc).le
  have e_G : C31 * Real.log L.sc.x / L.sc.delta1 ≤ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) := by
    refine pY _ 2 ?_ (by norm_num)
    calc C31 * Real.log L.sc.x / L.sc.delta1 = C31 * Real.log L.sc.x * (1 / L.sc.delta1) := by ring
      _ = C31 * Real.log L.sc.x * L.sc.x ^ (L.sc.eps / 8) := by rw [hd]
      _ ≤ L.sc.x * L.sc.x := mul_le_mul f9 h8 h80 hx0.le
      _ = L.sc.x ^ 2 := by ring
  have e_N1 : (N1 L.sc : ℝ) ≤ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) := le_trans (le_trans (first_count_le_log L.sc hxe) f10) hxY
  have hd1 : L.sc.delta1 ≤ 1 := by
    unfold Scale.delta1
    exact Real.rpow_le_one_of_one_le_of_nonpos hx1.le (by linarith)
  have e_Q : ∀ p : ℕ, p.Prime → (p : ℝ) < L.sc.X' → Qp L.sc p ≤ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) := by
    intro p hp hpX
    calc Qp L.sc p ≤ Real.exp (Real.log (Qp L.sc p)) := Real.le_exp_log _
      _ ≤ Real.exp (L.sc.x ^ (11 * L.sc.eps / 24 + L.sc.eps / 48)) := Real.exp_le_exp.2 ((h5.2.2 p hp).2 hpX)
      _ ≤ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) := Real.exp_le_exp.2 (mono _ _ (by linarith))
  have e_Q0 : ∀ p : ℕ, p.Prime → (p : ℝ) < L.sc.p0 D.R.k → Qp L.sc p ≤ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) := by
    intro p hp hpX
    calc Qp L.sc p ≤ Real.exp (Real.log (Qp L.sc p)) := Real.le_exp_log _
      _ ≤ Real.exp (L.sc.x ^ (L.sc.eps / 8 + L.sc.eps / 48)) := Real.exp_le_exp.2 ((h5.2.2 p hp).1 hpX)
      _ ≤ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) := Real.exp_le_exp.2 (mono _ _ (by linarith))
  have hQ0 : ∀ p : ℕ, 0 ≤ Qp L.sc p := fun p => by unfold Qp; positivity
  have e8 : (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) ^ 8 ≤ L.sc.b' := by
    have h2 : L.sc.b' = L.sc.x * Real.exp (L.sc.x ^ L.sc.eps - L.sc.x ^ (L.sc.eps / 3)) := by
      unfold Scale.b' Scale.a Scale.b Scale.X' Scale.L
      rw [Real.exp_sub]; ring
    rw [h2, ← Real.exp_nat_mul]
    calc Real.exp (((8 : ℕ) : ℝ) * (L.sc.x ^ (23 * L.sc.eps / 48))) ≤ Real.exp (L.sc.x ^ L.sc.eps - L.sc.x ^ (L.sc.eps / 3)) := by
          apply Real.exp_le_exp.2
          push_cast
          linarith
      _ = 1 * Real.exp (L.sc.x ^ L.sc.eps - L.sc.x ^ (L.sc.eps / 3)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hx1.le (Real.exp_pos _).le
  refine ⟨?_, ?_, ?_⟩
  · intro p hp hp0
    have h1 : (D.R.k : ℝ) * Qp L.sc p ≤ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) * (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) := mul_le_mul e_k (e_Q0 p hp hp0) (hQ0 p) hY0.le
    have h2 : (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) * (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) ≤ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) ^ 8 := by
      rw [← pow_two]; exact pow_le_pow_right₀ (by linarith) (by norm_num)
    linarith
  · intro p hp
    rw [rG_rE]
    exact le_trans (hDII_arith (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) K.DII _ _ _ _ hY130 hDII0 g4 (Nat.cast_nonneg _) e_N1 (Nat.cast_nonneg _) g6 hk0.le e_k
      (e_lb p hp).1 (e_lb p hp).2) e8
  · intro p hp _ hpX n' hn'
    have hbo : L.sc.b ^ (L.sc.x ^ (-(L.sc.eps / 2))) = Real.exp (L.sc.x ^ (L.sc.eps / 2)) := by
      rw [hb, ← Real.exp_mul, ← Real.rpow_add hx0]
      congr 2
      ring
    rw [hbo]
    have hn'R : (n' : ℝ) ≤ (D.R.n : ℝ) := by exact_mod_cast hn'
    have hNp0 : 0 ≤ NplusF L.sc n' := by
      unfold NplusF; exact mul_nonneg (by positivity) (sc_delta1_pos L.sc).le
    have hNp : NplusF L.sc n' ≤ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) := by
      refine pY _ 4 ?_ (by norm_num)
      unfold NplusF
      calc 40 * (n' : ℝ) * L.sc.delta1 ≤ L.sc.x * L.sc.x ^ 3 * 1 :=
            mul_le_mul (mul_le_mul hx40 (le_trans hn'R hn3) (Nat.cast_nonneg _) hx0.le) hd1
              (sc_delta1_pos L.sc).le (by positivity)
        _ = L.sc.x ^ 4 := by ring
    have hval0 : 0 ≤ K.DI * NplusF L.sc n' * (L.sc.x ^ (Scale.A / 2)) ^ 2 * ((N1 L.sc : ℝ) ^ 5 + (D.R.k : ℝ) ^ 3) *
        Real.logb p L.sc.a :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hDI0 hNp0) (by positivity)) (by positivity)) (e_lb p hp).1
    have hDIf : (DIf K L p n' : ℝ) ≤ K.DI * NplusF L.sc n' * (L.sc.x ^ (Scale.A / 2)) ^ 2 *
        ((N1 L.sc : ℝ) ^ 5 + (D.R.k : ℝ) ^ 3) * Real.logb p L.sc.a + 1 := by
      unfold DIf
      exact (Nat.ceil_lt_add_one hval0).le
    have h13 : (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) ^ 13 ≤ Real.exp (L.sc.x ^ (L.sc.eps / 2)) := by
      rw [← Real.exp_nat_mul]
      apply Real.exp_le_exp.2
      push_cast
      exact f8
    refine le_trans ?_ h13
    unfold c6f
    exact hboB_arith (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) K.Pr1 _ L.etaSz (cG L) (Nm D) K.kappaThresholdTwo (Qp L.sc p) _ (NplusF L.sc n') (D.R.k : ℝ) _ (n' : ℝ) C31 _ K.DI _
      (N1 L.sc : ℝ) (NplusF L.sc n') hY130 hPr10 g1 hG0 e_G L.etaSz_pos.le e_eta hcG0 e_c hNm0 e_Nm htI20 g2 (hQ0 p)
      (e_Q p hp hpX) hDI0 g3 hNp0 hNp hk0.le e_k (e_lb p hp).1 (e_lb p hp).2
      (Nat.cast_nonneg _) (le_trans hn'R e_n) hC31.le g5 hlx0 e_lx (Real.rpow_nonneg hx0.le _) e_v (Nat.cast_nonneg _) e_N1
      hNp0 hNp (Nat.cast_nonneg _) hDIf

end Formalism.MainNotions.AuxBlock8.Pf.St.B

end
