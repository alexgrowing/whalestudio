import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.SlopeEstimateOfLemmaBSlopeLine

noncomputable section

open scoped BigOperators
open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.G Filter

namespace Formalism.MainNotions.AuxBlock8.Pf

theorem ev_log (c α : ℝ) (hα : 0 < α) : ∀ᶠ x : ℝ in atTop, c * Real.log x ≤ x ^ α := by
  have h := (isLittleO_log_rpow_atTop hα).def (c := 1 / (|c| + 1)) (by positivity)
  filter_upwards [h, eventually_ge_atTop 1] with x hx h1
  have hl : 0 ≤ Real.log x := Real.log_nonneg h1
  have hp : 0 ≤ x ^ α := Real.rpow_nonneg (by linarith) _
  rw [Real.norm_of_nonneg hl, Real.norm_of_nonneg hp] at hx
  have h2 : (0 : ℝ) < |c| + 1 := by positivity
  have h3 : (|c| + 1) * Real.log x ≤ x ^ α := by
    calc (|c| + 1) * Real.log x ≤ (|c| + 1) * (1 / (|c| + 1) * x ^ α) := mul_le_mul_of_nonneg_left hx h2.le
      _ = x ^ α := by field_simp
  have h4 : c ≤ |c| + 1 := by linarith [le_abs_self c]
  nlinarith

theorem ev_pow (c α β : ℝ) (h : α < β) : ∀ᶠ x : ℝ in atTop, c * x ^ α ≤ x ^ β := by
  have h1 := (tendsto_rpow_atTop (sub_pos.2 h)).eventually_ge_atTop c
  filter_upwards [h1, eventually_gt_atTop 0] with x hx h0
  calc c * x ^ α ≤ x ^ (β - α) * x ^ α := mul_le_mul_of_nonneg_right hx (Real.rpow_nonneg h0.le _)
    _ = x ^ β := by rw [← Real.rpow_add h0]; congr 1; ring

def rE (eps : ℝ) : ℕ := ⌈8 * (2 + 8 * eps + 2) / eps⌉₊ + 1

theorem rG_rE (s : Scale) : rG s = rE s.eps := rfl

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

theorem pow7 (x : ℝ) (hx : 0 < x) (a b c d e f g : ℝ) :
    x ^ a * (x ^ b * x ^ c) * x ^ d * x ^ e * (x ^ f * x ^ g) = x ^ (a + b + c + d + e + f + g) := by
  simp only [Real.rpow_add hx]; ring

theorem tot_arith (x ε m T : ℝ) (hx : 1 < x) (hε : 0 < ε) (hm0 : 0 ≤ m) (hT0 : 0 ≤ T)
    (e2 : m ≤ x ^ (ε / 100) * x ^ (1 / 2 : ℝ)) (e3 : T ≤ 2 * x ^ (2 + 8 * ε + ε / 100))
    (f7 : 48 * x ^ (ε + ε / 100 + 1 / 2 + (2 + 8 * ε + ε / 100) + -12 + ε / 3 + ε / 3) ≤ x ^ (-9 : ℝ)) :
    (x ^ ε + 1) * m * T * x ^ (-12 : ℝ) * (x ^ (ε / 3) * (2 + x ^ (ε / 3))) ≤ x ^ (-9 : ℝ) / 4 := by
  have hx0 : 0 < x := by linarith
  have hp7 := pow7 x hx0 ε (ε / 100) (1 / 2) (2 + 8 * ε + ε / 100) (-12) (ε / 3) (ε / 3)
  rw [← hp7] at f7
  have q1 : 1 ≤ x ^ ε := Real.one_le_rpow hx.le hε.le
  have q5 : 1 ≤ x ^ (ε / 3) := Real.one_le_rpow hx.le (by positivity)
  generalize x ^ ε = A at *
  generalize x ^ (ε / 100) * x ^ (1 / 2 : ℝ) = B at *
  generalize x ^ (2 + 8 * ε + ε / 100) = C at *
  have p4 : 0 ≤ x ^ (-12 : ℝ) := Real.rpow_nonneg hx0.le _
  generalize x ^ (-12 : ℝ) = E at *
  generalize x ^ (ε / 3) = Y at *
  generalize x ^ (-9 : ℝ) = R at *
  have hB : 0 ≤ B := le_trans hm0 e2
  have hC : 0 ≤ C := by linarith
  have e1 : A + 1 ≤ 2 * A := by linarith
  have e4 : Y * (2 + Y) ≤ 3 * (Y * Y) := by nlinarith
  have step : (A + 1) * m * T * E * (Y * (2 + Y)) ≤ (2 * A) * B * (2 * C) * E * (3 * (Y * Y)) := by
    apply mul_le_mul _ e4 (by positivity) (by positivity)
    apply mul_le_mul_of_nonneg_right _ p4
    apply mul_le_mul _ e3 hT0 (by positivity)
    exact mul_le_mul e1 e2 hm0 (by positivity)
  have : (2 * A) * B * (2 * C) * E * (3 * (Y * Y)) = 12 * (A * B * C * E * (Y * Y)) := by ring
  linarith

theorem k_le_x_pow_six {D : D7} (L : SizeData₂ D) (hS : Formalism.MainNotions.SizesAt L) : (D.R.k : ℝ) ≤ L.sc.x ^ (6 : ℝ) := by
  have h := hS.2.2.1.2
  refine le_trans h (Real.rpow_le_rpow_of_exponent_le L.sc.one_lt_alt.le ?_)
  unfold Formalism.MainNotions.szTh
  have := L.sc.eps_lt
  have := L.sc.eps_pos
  linarith

theorem one_le_k (D : D7) : (1 : ℝ) ≤ (D.R.k : ℝ) := by
  have := D.R.m_add_three_le_k
  exact_mod_cast (by omega : 1 ≤ D.R.k)

theorem xpow_le_exp (x N y : ℝ) (hx : 0 < x) (h : N * Real.log x ≤ y) : x ^ N ≤ Real.exp y := by
  rw [Real.rpow_def_of_pos hx]
  exact Real.exp_le_exp.2 (by linarith [mul_comm N (Real.log x)])

theorem second_level_lt_good_of_log {D : D7} (L : SizeData₂ D) (hS : Formalism.MainNotions.SizesAt L) (hx : Real.exp 1 ≤ L.sc.x)
    (h : 514 * Real.log L.sc.x ≤ L.sc.x ^ (L.sc.eps / 8)) : L2 D L.sc < goodU L.sc.delta1 := by
  have hx0 := sc_x_pos L.sc
  have lx1 : 1 ≤ Real.log L.sc.x := (Real.le_log_iff_exp_le hx0).2 hx
  have hk1 := one_le_k D
  have hk6 := k_le_x_pow_six L hS
  have hlk : Real.log (D.R.k : ℝ) ≤ 6 * Real.log L.sc.x := by
    have := Real.log_le_log (by linarith) hk6
    rwa [Real.log_rpow hx0] at this
  have hlk0 : 0 ≤ Real.log (D.R.k : ℝ) := Real.log_nonneg hk1
  have hxA : 0 < L.sc.x ^ Scale.A := Real.rpow_pos_of_pos hx0 _
  have hZ : Real.log (((D.R.k : ℝ) * L.sc.x ^ Scale.A) ^ 4) = 4 * (Real.log (D.R.k : ℝ) + 26 * Real.log L.sc.x) := by
    rw [Real.log_pow, Real.log_mul (by linarith) hxA.ne', Real.log_rpow hx0]
    unfold Scale.A
    push_cast
    ring
  have hL1 : ∀ p : ℕ, p.Prime → L1 D L.sc p ≤ ⌈256 * Real.log L.sc.x⌉₊ := by
    intro p hp
    unfold L1
    apply Nat.ceil_mono
    unfold Real.logb
    rw [hZ]
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hl2 : (1 / 2 : ℝ) ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
    have hlp : (1 / 2 : ℝ) ≤ Real.log p := le_trans hl2 (Real.log_le_log (by norm_num) hp2)
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hsup : sSup {l | ∃ p : ℕ, p.Prime ∧ D.host.cls p = PrimeClass.inertClass ∧ l = L1 D L.sc p} ≤
      ⌈256 * Real.log L.sc.x⌉₊ := by
    rcases Set.eq_empty_or_nonempty {l | ∃ p : ℕ, p.Prime ∧ D.host.cls p = PrimeClass.inertClass ∧ l = L1 D L.sc p} with h0 | h0
    · rw [h0]; simp
    · apply csSup_le h0
      rintro l ⟨p, hp, _, rfl⟩
      exact hL1 p hp
  have hc := Nat.ceil_lt_add_one (by positivity : 0 ≤ 256 * Real.log L.sc.x)
  have hU : L.sc.x ^ (L.sc.eps / 8) ≤ (goodU L.sc.delta1 : ℝ) := by
    unfold goodU
    rw [inv_delta1]
    exact Nat.le_ceil _
  have h2 : ((L2 D L.sc : ℕ) : ℝ) ≤ 2 * (⌈256 * Real.log L.sc.x⌉₊ : ℝ) := by
    unfold L2
    push_cast
    have : ((sSup {l | ∃ p : ℕ, p.Prime ∧ D.host.cls p = PrimeClass.inertClass ∧ l = L1 D L.sc p} : ℕ) : ℝ) ≤
        (⌈256 * Real.log L.sc.x⌉₊ : ℝ) := by exact_mod_cast hsup
    linarith
  have : ((L2 D L.sc : ℕ) : ℝ) < (goodU L.sc.delta1 : ℝ) := by linarith
  exact_mod_cast this

theorem numMean_ev (eps : ℝ) (K : Consts) (hK : K.Nonneg) (Cm : ℝ) (hCm : 0 ≤ Cm) :
    ∀ᶠ x : ℝ in atTop, ∀ (D : D7) (L : SizeData₂ D), L.sc.x = x → L.sc.eps = eps → Formalism.MainNotions.SizesAt L →
      adm5 D L K (eps / 48) → NumMean D L K Cm := by
  by_cases he : 0 < eps ∧ eps < 1 / 52
  swap
  · refine Filter.Eventually.of_forall fun x D L _ h2 => ?_
    exact absurd ⟨h2 ▸ L.sc.eps_pos, h2 ▸ L.sc.eps_lt⟩ he
  obtain ⟨he0, he1⟩ := he
  have F1 := ev_pow (K.kII * (rE eps : ℝ) ^ 2) ((9 / 2 + 10 * eps + eps / 100) + -26) (-12) (by linarith)
  have F2 := ev_log (Cm * cNE eps) 1 one_pos
  have F3 := ev_log 514 (eps / 8) (by positivity)
  have F4 := ev_log (3 * cGE eps) (eps / 8) (by positivity)
  have F5 := ev_log 18 eps he0
  have F6 := ev_log 10 eps he0
  have F6' := ev_pow 2 (eps / 3) eps (by linarith)
  have F7 := ev_pow 48 (eps + eps / 100 + 1 / 2 + (2 + 8 * eps + eps / 100) + -12 + eps / 3 + eps / 3) (-9)
    (by linarith)
  filter_upwards [F1, F2, F3, F4, F5, F6, F6', F7, eventually_ge_atTop (Real.exp 1)] with
    x f1 f2 f3 f4 f5 f6 f6' f7 hxe D L hx heps hS h5
  subst hx
  subst heps
  have hx0 := sc_x_pos L.sc
  have hx1 := L.sc.one_lt_alt
  have lx1 : 1 ≤ Real.log L.sc.x := (Real.le_log_iff_exp_le hx0).2 hxe
  have hk1 := one_le_k D
  have hk6 := k_le_x_pow_six L hS
  have hkII : 0 ≤ K.kII := hK.2.2.1
  have hA13 : Scale.A / 2 = 13 := by unfold Scale.A; norm_num
  have hd1 : L.sc.delta1 ≤ 1 := by
    unfold Scale.delta1
    exact Real.rpow_le_one_of_one_le_of_nonpos hx1.le (by linarith)
  have hd0 := sc_delta1_pos L.sc
  have hL2 := second_level_lt_good_of_log L hS hxe f3
  obtain ⟨hSN, hSM, hSK, -, -, -, -, hSTT, -⟩ := hS
  unfold Formalism.MainNotions.SizeN Formalism.MainNotions.szTh at hSN
  unfold Formalism.MainNotions.SizeM Formalism.MainNotions.szTh at hSM
  unfold Formalism.MainNotions.SizeK Formalism.MainNotions.szTh at hSK
  unfold Formalism.MainNotions.SizeTT Formalism.MainNotions.szNst Formalism.MainNotions.szTh at hSTT
  have hb'k : (D.R.k : ℝ) ≤ L.sc.b' := by
    have h1 : L.sc.x ^ (5 : ℝ) ≤ Real.exp (L.sc.x ^ L.sc.eps - L.sc.x ^ (L.sc.eps / 3)) :=
      xpow_le_exp _ _ _ hx0 (by linarith)
    have h2 : L.sc.b' = L.sc.x * Real.exp (L.sc.x ^ L.sc.eps - L.sc.x ^ (L.sc.eps / 3)) := by
      unfold Scale.b' Scale.a Scale.b Scale.X' Scale.L
      rw [Real.exp_sub]; ring
    have h3 : L.sc.x ^ (6 : ℝ) = L.sc.x * L.sc.x ^ (5 : ℝ) := by
      rw [show (6 : ℝ) = 1 + 5 by norm_num, Real.rpow_add hx0, Real.rpow_one]
    rw [h2]
    calc (D.R.k : ℝ) ≤ L.sc.x * L.sc.x ^ (5 : ℝ) := h3 ▸ hk6
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 hx0.le
  refine ⟨?_, ?_, hL2, ?_, ?_, ?_, ?_⟩
  ·
    rw [rG_rE]
    have hA : -Scale.A = -26 := by unfold Scale.A; rfl
    rw [hA]
    have h26 : 0 ≤ L.sc.x ^ (-26 : ℝ) := Real.rpow_nonneg hx0.le _
    calc K.kII * (rE L.sc.eps : ℝ) ^ 2 * (D.R.k : ℝ) * L.sc.x ^ (-26 : ℝ)
        ≤ K.kII * (rE L.sc.eps : ℝ) ^ 2 * L.sc.x ^ (9 / 2 + 10 * L.sc.eps + L.sc.eps / 100) * L.sc.x ^ (-26 : ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hSK.2 (by positivity)) h26
      _ = K.kII * (rE L.sc.eps : ℝ) ^ 2 * L.sc.x ^ ((9 / 2 + 10 * L.sc.eps + L.sc.eps / 100) + -26) := by
          rw [mul_assoc, ← Real.rpow_add hx0]
      _ ≤ _ := f1
  ·
    rw [hA13, show (-12 : ℝ) = 1 - 13 by norm_num, Real.rpow_sub hx0]
    apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg hx0.le _)
    calc Cm * (N1 L.sc : ℝ) ≤ Cm * (cNE L.sc.eps * Real.log L.sc.x) :=
          mul_le_mul_of_nonneg_left (first_count_le_log L.sc hxe) hCm
      _ = Cm * cNE L.sc.eps * Real.log L.sc.x := by ring
      _ ≤ _ := f2
  ·
    have h8 : 0 ≤ L.sc.x ^ (L.sc.eps / 8) := Real.rpow_nonneg hx0.le _
    calc 3 * (Gp L.sc : ℝ) ≤ 3 * (cGE L.sc.eps * Real.log L.sc.x * L.sc.x ^ (L.sc.eps / 8)) :=
          mul_le_mul_of_nonneg_left (Gp_le L.sc hxe) (by norm_num)
      _ = (3 * cGE L.sc.eps * Real.log L.sc.x) * L.sc.x ^ (L.sc.eps / 8) := by ring
      _ ≤ L.sc.x ^ (L.sc.eps / 8) * L.sc.x ^ (L.sc.eps / 8) := mul_le_mul_of_nonneg_right f4 h8
      _ = L.sc.x ^ (L.sc.eps / 4) := by rw [← Real.rpow_add hx0]; congr 1; ring
  ·
    rw [hA13]
    have h13 : 0 < L.sc.x ^ (13 : ℝ) := Real.rpow_pos_of_pos hx0 _
    rw [one_le_div (by positivity)]
    have h1 : L.sc.x ^ (18 : ℝ) ≤ Real.exp (L.sc.x ^ L.sc.eps) := xpow_le_exp _ _ _ hx0 f5
    calc (D.R.k : ℝ) * L.sc.x ^ (13 : ℝ) ≤ L.sc.x ^ (6 : ℝ) * L.sc.x ^ (13 : ℝ) :=
          mul_le_mul_of_nonneg_right hk6 h13.le
      _ = L.sc.x * L.sc.x ^ (18 : ℝ) := by
          rw [← Real.rpow_add hx0, ← Real.rpow_one_add' hx0.le (by norm_num)]; norm_num
      _ ≤ L.sc.x * Real.exp (L.sc.x ^ L.sc.eps) := mul_le_mul_of_nonneg_left h1 hx0.le
      _ = L.sc.a := rfl
  ·
    rw [one_le_div (by linarith)]
    have hNs : 1 ≤ Nstar D L.sc := by
      unfold Nstar
      have h1 : L.sc.x ^ (2 + 8 * L.sc.eps - L.sc.eps / 100) * L.sc.delta1 ≤ (D.R.n : ℝ) * L.sc.delta1 :=
        mul_le_mul_of_nonneg_right hSN.1 hd0.le
      have h2 : 1 ≤ L.sc.x ^ (2 + 8 * L.sc.eps - L.sc.eps / 100) * L.sc.delta1 := by
        unfold Scale.delta1
        rw [← Real.rpow_add hx0]
        exact one_le_xpow L.sc _ (by linarith)
      nlinarith
    have hxe1 : 1 ≤ L.sc.x ^ L.sc.eps := one_le_xpow L.sc _ he0.le
    have hLa : 1 ≤ La K L.sc := le_trans (one_le_xpow L.sc _ (by linarith)) h5.1
    have hb0 : 0 ≤ L.sc.b' := sc_b'_nonneg L.sc
    have h3 : 1 ≤ Nstar D L.sc * L.sc.x ^ L.sc.eps * La K L.sc := by
      have := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hNs hxe1) hLa
      exact this
    calc (D.R.k : ℝ) ≤ 1 * L.sc.b' := by linarith
      _ ≤ _ := mul_le_mul_of_nonneg_right h3 hb0
  ·
    have e2 : (D.R.m : ℝ) ≤ L.sc.x ^ (L.sc.eps / 100) * L.sc.x ^ (1 / 2 : ℝ) := by
      refine le_trans hSM.2 (mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hx0.le _))
      rw [← Real.sqrt_eq_rpow]
      apply Real.sqrt_le_sqrt
      nlinarith
    have e3 : (D.host.TT.card : ℝ) ≤ 2 * L.sc.x ^ (2 + 8 * L.sc.eps + L.sc.eps / 100) := by
      have hn0 : (0 : ℝ) ≤ (D.R.n : ℝ) := Nat.cast_nonneg _
      have : 2 * (D.R.n : ℝ) * L.sc.delta1 ≤ 2 * (D.R.n : ℝ) := by nlinarith
      linarith [hSTT.2, hSN.2]
    exact tot_arith _ _ _ _ hx1 he0 (Nat.cast_nonneg _) (Nat.cast_nonneg _) e2 e3 f7

theorem b'_eq (s : Scale) : s.b' = s.x * Real.exp (s.x ^ s.eps - s.x ^ (s.eps / 3)) := by
  unfold Scale.b' Scale.a Scale.b Scale.X' Scale.L
  rw [Real.exp_sub]; ring

theorem big_le_b' (s : Scale) (n : ℕ) (u : ℝ) (h : n * Real.log s.x + u + s.x ^ (s.eps / 3) ≤ s.x ^ s.eps) :
    s.x ^ (n + 1) * Real.exp u ≤ s.b' := by
  have hx0 := sc_x_pos s
  rw [b'_eq, pow_succ, mul_comm (s.x ^ n) s.x, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hx0.le
  have : s.x ^ n = Real.exp (n * Real.log s.x) := by
    rw [Real.exp_nat_mul, Real.exp_log hx0]
  rw [this, ← Real.exp_add]
  exact Real.exp_le_exp.2 (by linarith)

theorem rpow_nat_lit (x : ℝ) (n : ℕ) : x ^ ((n : ℕ) : ℝ) = x ^ n := Real.rpow_natCast x n

theorem parameter_product_le_arith (x k Y2 Yb N La la X' : ℝ) (hx : 2 ≤ x) (hk0 : 0 ≤ k) (hYb0 : 0 ≤ Yb) (hN0 : 0 ≤ N) (hLa0 : 0 ≤ La)
    (hla0 : 0 ≤ la) (hk : k ≤ x ^ 6) (hY2 : Y2 = x ^ 26) (hYb : Yb ≤ x) (hN : N ≤ x ^ 3) (hLa : La ≤ x) (hla : la ≤ 2 * x)
    (hX : x ^ 39 ≤ X') : k * Y2 * Yb * N * La * la ≤ X' := by
  have hx0 : 0 ≤ x := by linarith
  subst hY2
  calc k * x ^ 26 * Yb * N * La * la ≤ x ^ 6 * x ^ 26 * x * x ^ 3 * x * (2 * x) := by gcongr
    _ = 2 * x ^ 38 := by ring
    _ ≤ x * x ^ 38 := mul_le_mul_of_nonneg_right hx (by positivity)
    _ = x ^ 39 := by ring
    _ ≤ X' := hX

theorem DI_arith (x DI Np Y2 N1 k lb : ℝ) (hx : 1 ≤ x) (hDI0 : 0 ≤ DI) (hNp0 : 0 ≤ Np) (hN10 : 0 ≤ N1) (hk0 : 0 ≤ k)
    (hlb0 : 0 ≤ lb) (hDI : 320 * DI + 1 ≤ x) (hNp : Np ≤ 40 * x ^ 3) (hY2 : Y2 = x ^ 26) (hN1 : N1 ≤ x) (hk : k ≤ x ^ 6)
    (hlb : lb ≤ 4 * x) : DI * Np * Y2 * (N1 ^ 5 + k ^ 3) * lb + 1 ≤ x ^ 49 := by
  have hx0 : 0 ≤ x := by linarith
  subst hY2
  have h5 : N1 ^ 5 ≤ x ^ 18 := by
    calc N1 ^ 5 ≤ x ^ 5 := by gcongr
      _ ≤ x ^ 18 := pow_le_pow_right₀ hx (by norm_num)
  have h3 : k ^ 3 ≤ x ^ 18 := by
    calc k ^ 3 ≤ (x ^ 6) ^ 3 := by gcongr
      _ = x ^ 18 := by ring
  have h48 : 1 ≤ x ^ 48 := one_le_pow₀ hx
  calc DI * Np * x ^ 26 * (N1 ^ 5 + k ^ 3) * lb + 1
      ≤ DI * (40 * x ^ 3) * x ^ 26 * (x ^ 18 + x ^ 18) * (4 * x) + 1 := by gcongr
    _ = 320 * DI * x ^ 48 + 1 := by ring
    _ ≤ 320 * DI * x ^ 48 + x ^ 48 := by linarith
    _ = (320 * DI + 1) * x ^ 48 := by ring
    _ ≤ x * x ^ 48 := mul_le_mul_of_nonneg_right hDI (by positivity)
    _ = x ^ 49 := by ring

theorem height_bound_product_arith (x kI k N n' Q4 DI c Y E1 E2 b' : ℝ) (hx : 7 ≤ x) (hkI0 : 0 ≤ kI) (hk0 : 0 ≤ k) (hN0 : 0 ≤ N)
    (hn0 : 0 ≤ n') (hQ0 : 0 ≤ Q4) (hDI0 : 0 ≤ DI) (hc0 : 0 ≤ c) (hE1 : 1 ≤ E1) (hkI : kI ≤ x) (hk : k ≤ x ^ 6)
    (hN : N ≤ x ^ 3) (hn : n' ≤ x ^ 3) (hQ : Q4 ≤ E2) (hDI : DI ≤ x ^ 49) (hc : c ≤ 16 * x ^ 6 * E1) (hY : Y = x ^ 13)
    (hb : x ^ 86 * (E2 * E1) ≤ b') :
    kI * k ^ 3 * N * Q4 * (8 * (DI + 1) + N * c + n' * c) * Y ≤ b' := by
  have hx0 : 0 ≤ x := by linarith
  have hx1 : 1 ≤ x := by linarith
  subst hY
  have hE2 : 0 ≤ E2 := le_trans hQ0 hQ
  have h3 : k ^ 3 ≤ x ^ 18 := by
    calc k ^ 3 ≤ (x ^ 6) ^ 3 := by gcongr
      _ = x ^ 18 := by ring
  have h49 : 1 ≤ x ^ 49 := one_le_pow₀ hx1
  have h9 : x ^ 9 ≤ x ^ 49 := pow_le_pow_right₀ hx1 (by norm_num)
  have hxx : 48 ≤ x ^ 2 := by nlinarith
  have inner : 8 * (DI + 1) + N * c + n' * c ≤ x ^ 51 * E1 := by
    have a1 : N * c ≤ x ^ 3 * (16 * x ^ 6 * E1) := by gcongr
    have a2 : n' * c ≤ x ^ 3 * (16 * x ^ 6 * E1) := by gcongr
    have a3 : 8 * (DI + 1) ≤ 16 * x ^ 49 * E1 := by nlinarith
    have a4 : x ^ 3 * (16 * x ^ 6 * E1) = 16 * x ^ 9 * E1 := by ring
    have a5 : 16 * x ^ 9 * E1 ≤ 16 * x ^ 49 * E1 := by gcongr
    have a6 : 48 * x ^ 49 * E1 ≤ x ^ 2 * x ^ 49 * E1 := by gcongr
    have a7 : x ^ 2 * x ^ 49 * E1 = x ^ 51 * E1 := by ring
    linarith
  have inner0 : 0 ≤ 8 * (DI + 1) + N * c + n' * c := by positivity
  calc kI * k ^ 3 * N * Q4 * (8 * (DI + 1) + N * c + n' * c) * x ^ 13
      ≤ x * x ^ 18 * x ^ 3 * E2 * (x ^ 51 * E1) * x ^ 13 := by gcongr
    _ = x ^ 86 * (E2 * E1) := by ring
    _ ≤ b' := hb

theorem ord_le_n (D : D7) (h : HH D) : addOrderOf h ≤ D.R.n := by
  have := addOrderOf_le_card_univ (x := h)
  rwa [Formalism.HC.Frame.card_A] at this

set_option maxHeartbeats 2000000 in

theorem restHypI_ev (eps : ℝ) (K : Consts) (hK : K.Nonneg) (Cm C31 : ℝ) :
    ∀ᶠ x : ℝ in atTop, ∀ (D : D7) (L : SizeData₂ D) (X : Inst D L), L.sc.x = x → L.sc.eps = eps → TypePrimeSizeConds D L K →
      adm5 D L K (eps / 48) → ArchimedeanSignatureMatching D L K → adm1 D L X C31 → NumMean D L K Cm → RestHypI X K := by
  by_cases he : 0 < eps ∧ eps < 1 / 52
  swap
  · refine Filter.Eventually.of_forall fun x D L _ _ h2 => ?_
    exact absurd ⟨h2 ▸ L.sc.eps_pos, h2 ▸ L.sc.eps_lt⟩ he
  obtain ⟨he0, he1⟩ := he
  have F1 := ev_pow 7 (-2) 0 (by norm_num)
  have F2 := ev_log (2 * cNE eps + 3) 1 one_pos
  have F3 := ev_log 128 (eps - eps / 48) (by linarith)
  have F4 := ev_pow (20 * K.kI) 0 eps he0
  have F5 := ev_log 39 (eps / 3) (by positivity)
  have F6 := ev_pow K.kI 4 (9 / 2) (by norm_num)
  have F7 := ev_log 340 eps he0
  have F8 := ev_pow 16 (11 * eps / 24 + eps / 48) eps (by linarith)
  have F9 := ev_pow 2 (eps / 4) eps (by linarith)
  have WorkedExample := ev_pow 4 (eps / 3) eps (by linarith)
  filter_upwards [F1, F2, F3, F4, F5, F6, F7, F8, F9, WorkedExample, eventually_ge_atTop (Real.exp 1), eventually_ge_atTop 7,
    eventually_ge_atTop (320 * K.DI + 1), eventually_ge_atTop K.kI] with
    x f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 hxe hx7 hxDI hxkI D L X hx heps hSz h5 h4 h1 NM
  clear F1 F2 F3 F4 F5 F6 F7 F8 F9 WorkedExample
  subst hx
  subst heps
  intro p hc hp0 t0 ht0
  obtain ⟨hS, hSc, _⟩ := hSz
  have hx0 := sc_x_pos L.sc
  have hx1 := L.sc.one_lt_alt
  have lx1 : 1 ≤ Real.log L.sc.x := (Real.le_log_iff_exp_le hx0).2 hxe
  have hk1 := one_le_k D
  have hk6r := k_le_x_pow_six L hS
  have hk6 : (D.R.k : ℝ) ≤ L.sc.x ^ 6 := by
    rwa [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at hk6r
  have hA13 : L.sc.x ^ (Scale.A / 2) = L.sc.x ^ 13 := by
    rw [show Scale.A / 2 = ((13 : ℕ) : ℝ) by unfold Scale.A; norm_num, Real.rpow_natCast]
  have hA26 : L.sc.x ^ Scale.A = L.sc.x ^ 26 := by
    rw [show Scale.A = ((26 : ℕ) : ℝ) by unfold Scale.A; norm_num, Real.rpow_natCast]
  have hd1 : L.sc.delta1 ≤ 1 := by
    unfold Scale.delta1
    exact Real.rpow_le_one_of_one_le_of_nonpos hx1.le (by linarith)
  have hd0 := sc_delta1_pos L.sc
  obtain ⟨hSN, -, hSK, -, -, -, -, -, -, -, -, -, -, -, -, -, hSDel, -⟩ := hS
  unfold Formalism.MainNotions.SizeN Formalism.MainNotions.szTh at hSN
  unfold Formalism.MainNotions.SizeK Formalism.MainNotions.szTh at hSK
  have hklo : L.sc.x ^ (9 / 2 : ℝ) ≤ (D.R.k : ℝ) :=
    le_trans (Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)) hSK.1
  have hn3 : (D.R.n : ℝ) ≤ L.sc.x ^ 3 := by
    have := le_trans hSN.2 (Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith : 2 + 8 * L.sc.eps + L.sc.eps / 100 ≤ (3 : ℝ)))
    rwa [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at this
  obtain ⟨hr, hg⟩ := mem_goodReps ht0
  have hord3 : 3 * Formalism.MainNotions.G.Gp L.sc ≤ addOrderOf (hP D p) := by
    have := le_trans NM.Gp hc.2.2.2.1
    exact_mod_cast this
  have hN40 := ((h1 p hc.1 hc.2.2.1 hc.2.2.2.1 NM.second_level_lt_good_bound hord3 t0 hr hg).1).2
  rw [Nv_eq X p hc.2.2.1 t0 hr] at hN40
  have hn'n : (addOrderOf (hP D p) : ℝ) ≤ (D.R.n : ℝ) := by
    exact_mod_cast ord_le_n D (hP D p)
  have hNn' : ((topsPos D p t0).card : ℝ) ≤ (addOrderOf (hP D p) : ℝ) := by
    have := Finset.card_le_univ (topsPos D p t0)
    rw [Fintype.card_fin] at this
    exact_mod_cast this
  generalize (topsPos D p t0).card = N at *
  generalize addOrderOf (hP D p) = n' at *
  have hn'3 : (n' : ℝ) ≤ L.sc.x ^ 3 := le_trans hn'n hn3
  have hN3 : (N : ℝ) ≤ L.sc.x ^ 3 := le_trans hNn' hn'3
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
  have hn'0 : (0 : ℝ) ≤ (n' : ℝ) := Nat.cast_nonneg _
  obtain ⟨hLalo, hLahi, hQ⟩ := h5
  have hLa1 : 1 ≤ La K L.sc := le_trans (one_le_xpow L.sc _ (by linarith)) hLalo
  have hLax : La K L.sc ≤ L.sc.x := by
    refine le_trans hLahi ?_
    have := Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith : L.sc.eps + L.sc.eps / 48 ≤ (1 : ℝ))
    rwa [Real.rpow_one] at this
  have hxex : L.sc.x ^ L.sc.eps ≤ L.sc.x := by
    have := Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith : L.sc.eps ≤ (1 : ℝ))
    rwa [Real.rpow_one] at this
  have hxe1 : 1 ≤ L.sc.x ^ L.sc.eps := one_le_xpow L.sc _ he0.le
  have hN1x : (N1 L.sc : ℝ) ≤ L.sc.x := by
    have h := first_count_le_log L.sc hxe
    have hc0 : 0 ≤ cNE L.sc.eps := by have := cGE_nonneg L.sc.eps he0; unfold cNE; positivity
    rw [Real.rpow_one] at f2
    nlinarith
  have hloga : Real.log L.sc.a = Real.log L.sc.x + L.sc.x ^ L.sc.eps := by
    unfold Scale.a Scale.b Scale.L
    rw [Real.log_mul hx0.ne' (Real.exp_pos _).ne', Real.log_exp]
  have hlx : Real.log L.sc.x ≤ L.sc.x := (Real.log_le_sub_one_of_pos hx0).trans (by linarith)
  have hloga2 : Real.log L.sc.a ≤ 2 * L.sc.x := by rw [hloga]; linarith
  have hloga0 : 0 ≤ Real.log L.sc.a := by rw [hloga]; linarith
  have hb0 := sc_b'_nonneg L.sc
  have ha0 : 0 < L.sc.a := lt_trans one_pos (sc_one_lt_a L.sc)
  have hX'0 : 0 < L.sc.X' := by unfold Scale.X'; exact Real.exp_pos _
  have hk0 : (0 : ℝ) < (D.R.k : ℝ) := by linarith
  have hrho := h4.1
  have hx2 : L.sc.x ^ (-2 : ℝ) ≤ 1 / 7 := by
    rw [Real.rpow_zero] at f1; linarith
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hc.1.two_le
  have hrho7 : rho D K L.sc ≤ 1 / 7 := le_trans hrho hx2
  have hrho1 : 4 * Nstar D L.sc * L.sc.x ^ L.sc.eps * La K L.sc / D.R.k ≤ 1 / 7 := by
    have h0 : 0 ≤ K.rho * (N1 L.sc : ℝ) * La K L.sc / D.R.k := by
      have : 0 ≤ K.rho := hK.2.1
      positivity
    have h7 := hrho7
    unfold rho at h7
    linarith only [h0, h7]
  have hkI0 : 0 ≤ K.kI := hK.2.2.2.2.2.2.2.2.2.2.1
  have hDI0 : 0 ≤ K.DI := hK.2.2.2.2.2.2.2.1
  unfold HypI
  dsimp only
  rw [hA13]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hN40, ?_⟩
  ·
    have : (D.R.k : ℝ) ^ 2 * (L.sc.x ^ 13) ^ 2 = L.sc.p0 D.R.k := by
      unfold Scale.p0; rw [hA26]; ring
    rw [this]; exact hp0
  ·
    have : L.sc.a / L.sc.b' = L.sc.X' := by
      unfold Scale.b'; field_simp
    rw [this]; exact hc.2.1
  · linarith only [hrho7]
  ·
    have h : 2 * (N1 L.sc : ℝ) + 3 ≤ (D.R.k : ℝ) := by
      have h := first_count_le_log L.sc hxe
      rw [Real.rpow_one] at f2
      have hxk : L.sc.x ≤ (D.R.k : ℝ) := by
        refine le_trans ?_ hklo
        have := Real.rpow_le_rpow_of_exponent_le hx1.le (by norm_num : (1 : ℝ) ≤ 9 / 2)
        rwa [Real.rpow_one] at this
      linarith only [h, f2, hxk, lx1]
    have h' : 2 * N1 L.sc + 3 ≤ D.R.k := by exact_mod_cast h
    omega
  ·
    rcases eq_or_lt_of_le hN0 with h0 | h0
    · rw [← h0]; simp; linarith
    · have hpos : 0 < (N : ℝ) * L.sc.x ^ 13 := by positivity
      have hle : (N : ℝ) * L.sc.x ^ 13 ≤ L.sc.x ^ 16 := by
        calc (N : ℝ) * L.sc.x ^ 13 ≤ L.sc.x ^ 3 * L.sc.x ^ 13 := by gcongr
          _ = L.sc.x ^ 16 := by ring
      have := Real.log_le_log hpos hle
      rw [Real.log_pow] at this
      push_cast at this
      linarith
  ·
    have h : L.sc.x ^ L.sc.eps / 20 * (N : ℝ) ≤ Nstar D L.sc * L.sc.x ^ L.sc.eps := by
      unfold Nstar
      have : (N : ℝ) ≤ 40 * (D.R.n : ℝ) * L.sc.delta1 := by
        refine le_trans hN40 ?_
        have := mul_le_mul_of_nonneg_right hn'n hd0.le
        nlinarith
      nlinarith
    have h2 : 0 ≤ La K L.sc * L.sc.b' / D.R.k := by positivity
    calc L.sc.x ^ L.sc.eps / 20 * (N : ℝ) * La K L.sc * L.sc.b' / D.R.k
        = (L.sc.x ^ L.sc.eps / 20 * (N : ℝ)) * (La K L.sc * L.sc.b' / D.R.k) := by ring
      _ ≤ (Nstar D L.sc * L.sc.x ^ L.sc.eps) * (La K L.sc * L.sc.b' / D.R.k) := mul_le_mul_of_nonneg_right h h2
      _ = _ := by ring
  ·
    have : 2 * (Nstar D L.sc * L.sc.x ^ L.sc.eps * La K L.sc * L.sc.b' / D.R.k) =
        (4 * Nstar D L.sc * L.sc.x ^ L.sc.eps * La K L.sc / D.R.k) * (L.sc.b' / 2) := by ring
    rw [this]
    nlinarith
  ·
    rw [Real.rpow_zero] at f4; linarith
  ·
    apply parameter_product_le_arith L.sc.x _ _ _ _ _ _ _ (by linarith) hk0.le (by positivity) hN0 (by linarith) hloga0 hk6 (by ring)
      (by linarith) hN3 hLax hloga2
    have := xpow_le_exp L.sc.x 39 _ hx0 f5
    rwa [show (39 : ℝ) = ((39 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at this
  ·
    have hLa2 : La K L.sc ^ 2 ≤ L.sc.x := by
      have h1 : La K L.sc ^ 2 ≤ (L.sc.x ^ (L.sc.eps + L.sc.eps / 48)) ^ 2 := by gcongr
      have h2 : (L.sc.x ^ (L.sc.eps + L.sc.eps / 48)) ^ 2 = L.sc.x ^ ((L.sc.eps + L.sc.eps / 48) * 2) := by
        rw [Real.rpow_mul hx0.le]; norm_cast
      have h3 := Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith : (L.sc.eps + L.sc.eps / 48) * 2 ≤ (1 : ℝ))
      rw [Real.rpow_one] at h3
      linarith
    have h4' : L.sc.x ^ (4 : ℝ) = L.sc.x ^ 4 := by
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [h4'] at f6
    calc K.kI * (N : ℝ) * La K L.sc ^ 2 ≤ K.kI * L.sc.x ^ 3 * L.sc.x := by gcongr
      _ = K.kI * L.sc.x ^ 4 := by ring
      _ ≤ _ := le_trans f6 hklo
  ·
    have h1 : L.sc.x ^ L.sc.eps * La K L.sc ≤ L.sc.x := by
      calc L.sc.x ^ L.sc.eps * La K L.sc ≤ L.sc.x ^ L.sc.eps * L.sc.x ^ (L.sc.eps + L.sc.eps / 48) := by gcongr
        _ = L.sc.x ^ (L.sc.eps + (L.sc.eps + L.sc.eps / 48)) := by rw [← Real.rpow_add hx0]
        _ ≤ L.sc.x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
        _ = L.sc.x := Real.rpow_one _
    have h2 : L.sc.x ^ 4 ≤ (D.R.k : ℝ) := by
      refine le_trans ?_ hklo
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hx1.le (by norm_num)
    have h3 : (L.sc.x ^ L.sc.eps * La K L.sc) * (N : ℝ) ≤ L.sc.x * L.sc.x ^ 3 := by gcongr
    have h4 : 0 < L.sc.x ^ 4 := by positivity
    have h5 : 2 * (L.sc.x ^ L.sc.eps / 20) * (N : ℝ) * La K L.sc = (L.sc.x ^ L.sc.eps * La K L.sc) * (N : ℝ) / 10 := by ring
    rw [h5]
    have h6 : L.sc.x * L.sc.x ^ 3 = L.sc.x ^ 4 := by ring
    linarith
  · exact hSc
  ·
    have hΔ : 0 < (D.s.Del : ℝ) := by
      have h := L.Sc_pos
      rw [L.Sc_eq] at h
      by_contra hn
      rw [not_lt] at hn
      nlinarith
    have hΔE : (D.s.Del : ℝ) ≤ Real.exp (L.sc.x ^ (L.sc.eps / 4) / 2) := by
      rw [← Real.exp_log hΔ]
      exact Real.exp_le_exp.2 hSDel.2.2.1
    have hQ0 : 0 < Qp L.sc p := by unfold Qp; positivity
    have hQE : Qp L.sc p ≤ Real.exp (L.sc.x ^ (11 * L.sc.eps / 24 + L.sc.eps / 48)) := by
      rw [← Real.exp_log hQ0]
      exact Real.exp_le_exp.2 ((hQ p hc.1).2 hc.2.1)
    have hlb0 : 0 ≤ Real.logb p L.sc.a := Real.logb_nonneg (by linarith) (sc_one_lt_a L.sc).le
    have hlb : Real.logb p L.sc.a ≤ 4 * L.sc.x := by
      unfold Real.logb
      have hl2 : (1 / 2 : ℝ) ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
      have hlp : (1 / 2 : ℝ) ≤ Real.log p := le_trans hl2 (Real.log_le_log (by norm_num) hp2)
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    have hNp0 : 0 ≤ NplusF L.sc n' := by unfold NplusF; positivity
    have hNp : NplusF L.sc n' ≤ 40 * L.sc.x ^ 3 := by
      unfold NplusF
      have := mul_le_mul hn'3 hd1 hd0.le (by positivity)
      nlinarith
    have hDIf : ((DIf K L p n' : ℕ) : ℝ) ≤ L.sc.x ^ 49 := by
      unfold DIf
      rw [hA13]
      have hW0 : 0 ≤ K.DI * NplusF L.sc n' * (L.sc.x ^ 13) ^ 2 * ((N1 L.sc : ℝ) ^ 5 + (D.R.k : ℝ) ^ 3) *
          Real.logb p L.sc.a := by positivity
      have h1 := Nat.ceil_lt_add_one hW0
      have h2 := DI_arith L.sc.x K.DI (NplusF L.sc n') ((L.sc.x ^ 13) ^ 2) (N1 L.sc : ℝ) (D.R.k : ℝ)
        (Real.logb p L.sc.a) hx1.le hDI0 hNp0 (Nat.cast_nonneg _) hk0.le hlb0 hxDI hNp (by ring) hN1x hk6 hlb
      linarith
    have hcG : cG L ≤ 16 * L.sc.x ^ 6 * Real.exp (L.sc.x ^ (L.sc.eps / 4) / 2) := by
      unfold cG
      rw [L.Sc_eq]
      have := mul_le_mul hk6 hΔE hΔ.le (by positivity)
      nlinarith
    have hcG0 : 0 ≤ cG L := by unfold cG; have := L.Sc_pos; linarith
    apply height_bound_product_arith L.sc.x K.kI _ _ _ _ _ _ _ (Real.exp (L.sc.x ^ (L.sc.eps / 4) / 2))
      (Real.exp (L.sc.x ^ (11 * L.sc.eps / 24 + L.sc.eps / 48)) ^ 4) _ hx7 hkI0 hk0.le hN0 hn'0 (by positivity)
      (Nat.cast_nonneg _) hcG0 (Real.one_le_exp (by positivity)) hxkI hk6 hN3 hn'3 (by gcongr) hDIf hcG rfl
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    apply big_le_b' L.sc 85
    push_cast
    linarith

theorem second_estimate_and_mean_along_family {eps : ℝ} (Fm : FamP eps) (K : Consts) (hK : K.Nonneg) (C31 Ce Cm : ℝ) (hCm : 0 ≤ Cm)
    (X : ∀ x (i : Fm.Ix x), Inst (Fm.D x i) (Fm.L x i)) (Y : ∀ x (i : Fm.Ix x), LatInst (Fm.D x i))
    (hA : AdmFam Fm K X Y C31 Ce Cm) :
    ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, Conclusion2 (Fm.D x i) (Fm.L x i) (X x i) K ∧ MeanEx (X x i) K := by
  have he : 0 < eps := by
    obtain ⟨i⟩ := Fm.Ix_zero
    have := (Fm.L 0 i).sc.eps_pos
    rwa [Fm.L_eps] at this
  obtain ⟨x1, _, H1⟩ := hA (eps / 48) (by positivity)
  obtain ⟨x2, H2⟩ := Filter.eventually_atTop.1 (numMean_ev eps K hK Cm hCm)
  obtain ⟨x3, H3⟩ := Filter.eventually_atTop.1 (restHypI_ev eps K hK Cm C31)
  refine ⟨max (Fm.x1 + 1) (max x1 (max x2 x3)), fun x hx i => ?_⟩
  have h0 : Fm.x1 < x := by have := le_trans (le_max_left _ _) hx; linarith
  have h1 : x ≥ x1 := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have h2 : x ≥ x2 := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hx
  have h3 : x ≥ x3 := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hx
  obtain ⟨a1, _, _, a4, a5, _, _, a8, _, _, _, aSz⟩ := H1 x h1 i
  have NM := H2 x h2 (Fm.D x i) (Fm.L x i) (Fm.L_x x i h0) (Fm.L_eps x i) aSz.1 a5
  have HI := H3 x h3 (Fm.D x i) (Fm.L x i) (X x i) (Fm.L_x x i h0) (Fm.L_eps x i) aSz a5 a4 a1 NM
  have p2 := slopeEstimate_of_lemmaB_slopeLine (X x i) K hK Cm a8 NM HI a4.2.2.1
  exact ⟨p2, meanEx_of (X x i) K hK Cm a8 NM HI a4.2.2.1 p2⟩

end Formalism.MainNotions.AuxBlock8.Pf

end
