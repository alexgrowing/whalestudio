import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.SecondConstantNonneg
import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.NumData

noncomputable section

open scoped BigOperators
open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.G Filter

namespace Formalism.MainNotions.AuxBlock8.Pf.G5

variable {D : D7} {L : SizeData₂ D}

structure NumT (D : D7) (L : SizeData₂ D) (C : ℝ) : Prop where
  t9 : (L.sc.X'' D.R.n * thS L + 2) * (Real.log (2 * L.sc.X'' D.R.n) * (thW D L.sc * L.sc.w'' D.R.n + L.Sc)) ≤
    L.sc.a * L.sc.x ^ (-16 : ℝ)
  t1 : c1 L C * (L.sc.X'' D.R.n + 2) ≤ L.sc.b * L.sc.x ^ (-100 : ℝ)
  t1' : cfl D L.sc C * (L.sc.X'' D.R.n + 2) ≤ L.sc.b * L.sc.x ^ (-100 : ℝ)

theorem inWin_of_boxT {K : Consts} {a b : HH D → ℤ} (ha : a ∈ box D (winA D L.sc)) (hb : b ∈ box D (winB D K L.sc)) :
    InWin L a b := by
  classical
  intro t ht
  unfold box at ha hb
  have h1 := Fintype.mem_piFinset.1 ha t
  have h2 := Fintype.mem_piFinset.1 hb t
  rw [if_pos ht] at h1 h2
  unfold winA at h1
  unfold winB at h2
  obtain ⟨h1a, h1b⟩ := Finset.mem_Icc.1 h1
  obtain ⟨h2a, _⟩ := Finset.mem_Icc.1 h2
  exact ⟨Int.ceil_le.1 h1a, Int.le_floor.1 h1b, Int.ceil_le.1 h2a⟩

theorem sum_le_count (S : Finset ℕ) (y c : ℝ) (hy : 0 ≤ y) (hc : 0 ≤ c) (f : ℕ → ℝ)
    (hS : ∀ p ∈ S, p.Prime ∧ (p : ℝ) ≤ y) (hf : ∀ p ∈ S, f p ≤ c) : ∑ p ∈ S, f p ≤ c * (y + 2) := by
  have hsub : S ⊆ prB (y + 1) := fun p hp => mem_prB.2 ⟨(hS p hp).1, by have := (hS p hp).2; linarith⟩
  have h1 : (S.card : ℝ) ≤ y + 2 := by
    have h2 : (S.card : ℝ) ≤ ((prB (y + 1)).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
    have h3 := card_prB_le (y + 1) (by linarith)
    linarith
  have h4 := Finset.sum_le_card_nsmul S f c hf
  rw [nsmul_eq_mul] at h4
  nlinarith

theorem third_estimate_of_numeric_facts (P : ParameterChoice' D L) (X : Inst D L) (K : Consts) (C : ℝ) (hC : 0 ≤ C) (N : NumT D L C) :
    WeightedPrimeSumBound D L X K C := by
  classical
  have hX1 : 1 ≤ L.sc.X'' D.R.n := by
    have := X'_le_X'' L.sc D.R.n (n_pos D); have := one_le_X' L.sc; linarith
  refine ⟨fun a ha b hb S hS => ?_, fun S hS => ⟨?_, ?_⟩⟩
  · have h := inWin_of_boxT ha hb
    obtain ⟨hS1, hS2⟩ := Sc_facts P
    obtain ⟨hth0, hth1⟩ := thS_bounds P
    have hm : (0 : ℝ) ≤ (D.R.m : ℝ) := Nat.cast_nonneg _
    have hN : (0 : ℝ) ≤ (D.host.TT.card : ℝ) := Nat.cast_nonneg _
    have hM : (0 : ℝ) ≤ (D.R.m : ℝ) * (D.host.TT.card : ℝ) := mul_nonneg hm hN
    obtain ⟨ht0, ht1⟩ := thW_bounds D L.sc
    have hw := sc_w''_pos L.sc D.R.n (n_pos D)
    have hl2 : 0 ≤ Real.log (2 * L.sc.X'' D.R.n) := Real.log_nonneg (by linarith)
    have hcoef : 0 ≤ Real.log (2 * L.sc.X'' D.R.n) *
        ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * (thW D L.sc * L.sc.w'' D.R.n + L.Sc)) := by positivity
    set R9 : Finset ℕ := Finset.Ioc ⌊L.sc.X'' D.R.n⌋₊ ⌈L.sc.X'' D.R.n * (1 + thS L)⌉₊ with hR9
    have hdd : ∀ p ∈ S, 0 ≤ (∑ j ∈ SizeData₂.lifts D, ∑ s ∈ D.host.TT, askG X a b p j s) ∧
        (∑ j ∈ SizeData₂.lifts D, ∑ s ∈ D.host.TT, askG X a b p j s) ≤ (D.R.m : ℝ) * ((D.host.TT.card : ℝ) *
        (if (p : ℝ) < L.sc.X'' D.R.n * (1 + thS L) then thW D L.sc * L.sc.w'' D.R.n + L.Sc else 0)) := by
      intro p hp
      have hpX := (hS p hp).2.2
      constructor
      · exact Finset.sum_nonneg (fun j hj => Finset.sum_nonneg (fun s hs => (ask_bounds P X h p (hS p hp).1 j hj s hs).1))
      · have hj : ∀ j ∈ SizeData₂.lifts D, ∑ s ∈ D.host.TT, askG X a b p j s ≤ (D.host.TT.card : ℝ) *
            (if (p : ℝ) < L.sc.X'' D.R.n * (1 + thS L) then thW D L.sc * L.sc.w'' D.R.n + L.Sc else 0) := by
          intro j hjl
          rw [← nsmul_eq_mul]
          apply Finset.sum_le_card_nsmul
          intro s hs
          exact ask_high P X h p hpX j hjl s hs
        have hs := Finset.sum_le_card_nsmul _ _ _ hj
        rw [lifts_card, nsmul_eq_mul] at hs
        exact hs
    have hpt : ∀ p ∈ S, Real.log p * (∑ j ∈ SizeData₂.lifts D, ∑ s ∈ D.host.TT, askG X a b p j s) ≤
        (if p ∈ R9 then (1 : ℝ) else 0) * (Real.log (2 * L.sc.X'' D.R.n) *
          ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * (thW D L.sc * L.sc.w'' D.R.n + L.Sc))) := by
      intro p hp
      have hpX := (hS p hp).2.2
      obtain ⟨hd0, hd⟩ := hdd p hp
      have hl : 0 ≤ Real.log p := Real.log_natCast_nonneg p
      by_cases hlt : (p : ℝ) < L.sc.X'' D.R.n * (1 + thS L)
      · rw [if_pos hlt] at hd
        have hmem : p ∈ R9 := by
          rw [hR9]
          refine Finset.mem_Ioc.2 ⟨(Nat.floor_lt (by linarith)).2 hpX, ?_⟩
          exact_mod_cast le_trans hlt.le (Nat.le_ceil _)
        rw [if_pos hmem, one_mul]
        have h1 : (∑ j ∈ SizeData₂.lifts D, ∑ s ∈ D.host.TT, askG X a b p j s) ≤
            (D.R.m : ℝ) * (D.host.TT.card : ℝ) * (thW D L.sc * L.sc.w'' D.R.n + L.Sc) := by linarith
        have h2 : Real.log p ≤ Real.log (2 * L.sc.X'' D.R.n) :=
          Real.log_le_log (by linarith) (by nlinarith)
        exact mul_le_mul h2 h1 hd0 hl2
      · rw [if_neg hlt] at hd
        have h1 : (∑ j ∈ SizeData₂.lifts D, ∑ s ∈ D.host.TT, askG X a b p j s) = 0 := le_antisymm (by linarith) hd0
        rw [h1, mul_zero]
        split_ifs
        · rw [one_mul]; exact hcoef
        · rw [zero_mul]
    refine le_trans (Finset.sum_le_sum hpt) ?_
    rw [← Finset.sum_mul]
    have b9 : ∑ p ∈ S, (if p ∈ R9 then (1 : ℝ) else 0) ≤ L.sc.X'' D.R.n * thS L + 2 := by
      refine le_trans (sum_ite_mem_le (fun _ => (1 : ℝ)) (fun _ _ => zero_le_one)) ?_
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      rw [hR9, Nat.card_Ioc]
      have hle : ⌊L.sc.X'' D.R.n⌋₊ ≤ ⌈L.sc.X'' D.R.n * (1 + thS L)⌉₊ :=
        le_trans (Nat.floor_le_floor (by nlinarith)) (Nat.floor_le_ceil _)
      rw [Nat.cast_sub hle]
      have h1 := Nat.ceil_lt_add_one (mul_nonneg (by linarith) (by linarith) : 0 ≤ L.sc.X'' D.R.n * (1 + thS L))
      have h2 := Nat.lt_floor_add_one (L.sc.X'' D.R.n)
      linarith
    refine le_trans (mul_le_mul_of_nonneg_right b9 hcoef) ?_
    have e1 := mul_le_mul_of_nonneg_left N.t9 hM
    linarith
  · refine le_trans (sum_le_count S (L.sc.X'' D.R.n) (c1 L C) (by linarith) (first_constant_nonneg L C hC) _ hS (fun p hp => ?_)) N.t1
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (hS p hp).1.one_lt
    have hl : 0 < Real.log p := Real.log_pos hp1
    apply le_of_eq
    unfold c1 Real.logb
    field_simp
  · exact le_trans (sum_le_count S (L.sc.X'' D.R.n) (cfl D L.sc C) (by linarith) (cfl_nonneg D L.sc C hC) _ hS
      (fun p hp => (fl_bounds D L.sc C hC p (hS p hp).1).2)) N.t1'

namespace Nu

theorem numeric_ninth_arith (Xpp θ lg w a x S Y X' z : ℝ) (hXw : Xpp * w = a) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hlg0 : 0 ≤ lg) (hlg : lg ≤ 2 * x) (hlgY : lg ≤ Y) (hw1 : 1 ≤ w) (hx : 0 < x)
    (hq1 : 8 * x * θ ^ 2 ≤ z) (hq2 : 16 * x * θ ≤ z * Xpp) (hS0 : 0 ≤ S) (hSY : S ≤ Y) (hY : 10 ≤ Y) (hX1 : 1 ≤ Xpp)
    (hXY : Xpp ≤ X' * Y) (hX'0 : 0 ≤ X') (e7 : Y ^ 7 * X' ≤ a * z) :
    (Xpp * (θ + 3 * S / w) + 2) * (lg * (θ * w + S)) ≤ a * z := by
  have hw0 : 0 < w := by linarith
  have hY0 : 0 ≤ Y := by linarith
  have hXp0 : 0 ≤ Xpp := by linarith
  have ha0 : 0 ≤ a := by rw [← hXw]; positivity
  have e : (Xpp * (θ + 3 * S / w) + 2) * (lg * (θ * w + S)) =
      lg * ((Xpp * w) * θ ^ 2) + lg * (2 * θ * w) +
        lg * ((Xpp * θ + 2) * S + 3 * S * Xpp * θ + 3 * S ^ 2 * (Xpp / w)) := by
    field_simp
    ring
  rw [e, hXw]
  have T1a : lg * (a * θ ^ 2) ≤ a * z / 4 := by
    calc lg * (a * θ ^ 2) ≤ (2 * x) * (a * θ ^ 2) := mul_le_mul_of_nonneg_right hlg (by positivity)
      _ = a * (8 * x * θ ^ 2) / 4 := by ring
      _ ≤ a * z / 4 := by
          have := mul_le_mul_of_nonneg_left hq1 ha0
          linarith
  have T1b : lg * (2 * θ * w) ≤ a * z / 4 := by
    calc lg * (2 * θ * w) ≤ (2 * x) * (2 * θ * w) := mul_le_mul_of_nonneg_right hlg (by positivity)
      _ = (16 * x * θ) * w / 4 := by ring
      _ ≤ (z * Xpp) * w / 4 := by
          have := mul_le_mul_of_nonneg_right hq2 hw0.le
          linarith
      _ = a * z / 4 := by rw [← hXw]; ring
  have hXw' : Xpp / w ≤ Xpp := div_le_self hXp0 hw1
  have hXw0 : 0 ≤ Xpp / w := by positivity
  have hYY : Y ≤ Y ^ 2 := by nlinarith
  have a0 : Xpp * θ ≤ Xpp := by nlinarith
  have a1 : (Xpp * θ + 2) * S ≤ (3 * Xpp) * Y := mul_le_mul (by linarith) hSY hS0 (by linarith)
  have a2 : 3 * S * Xpp * θ ≤ 3 * Y * Xpp := by
    have h1 : 3 * S * Xpp ≤ 3 * Y * Xpp := by gcongr
    have h2 : 3 * S * Xpp * θ ≤ 3 * S * Xpp * 1 := mul_le_mul_of_nonneg_left hθ1 (by positivity)
    linarith
  have a3 : 3 * S ^ 2 * (Xpp / w) ≤ 3 * Y ^ 2 * Xpp := by gcongr
  have a4 : Y * Xpp ≤ Y ^ 2 * Xpp := mul_le_mul_of_nonneg_right hYY hXp0
  have t2 : (Xpp * θ + 2) * S + 3 * S * Xpp * θ + 3 * S ^ 2 * (Xpp / w) ≤ 9 * Y ^ 2 * Xpp := by linarith
  have t20 : 0 ≤ (Xpp * θ + 2) * S + 3 * S * Xpp * θ + 3 * S ^ 2 * (Xpp / w) := by positivity
  have T2 : lg * ((Xpp * θ + 2) * S + 3 * S * Xpp * θ + 3 * S ^ 2 * (Xpp / w)) ≤ a * z / 80 := by
    have h3 : (1000 : ℝ) ≤ Y ^ 3 := by
      calc (1000 : ℝ) = 10 ^ 3 := by norm_num
        _ ≤ Y ^ 3 := pow_le_pow_left₀ (by norm_num) hY 3
    have h4 : 0 ≤ Y ^ 4 * X' := by positivity
    have h5 : 720 * (Y ^ 4 * X') ≤ Y ^ 7 * X' := by
      calc 720 * (Y ^ 4 * X') ≤ Y ^ 3 * (Y ^ 4 * X') := mul_le_mul_of_nonneg_right (by linarith) h4
        _ = Y ^ 7 * X' := by ring
    calc lg * ((Xpp * θ + 2) * S + 3 * S * Xpp * θ + 3 * S ^ 2 * (Xpp / w)) ≤ Y * (9 * Y ^ 2 * Xpp) :=
          mul_le_mul hlgY t2 t20 hY0
      _ ≤ Y * (9 * Y ^ 2 * (X' * Y)) := by gcongr
      _ = 9 * (Y ^ 4 * X') := by ring
      _ ≤ a * z / 80 := by linarith
  have haz : 0 ≤ a * z := le_trans (by positivity) e7
  linarith

theorem two_mul_le_sq (x : ℝ) (h : 16 ≤ x) : 2 * x ≤ x ^ 2 := by nlinarith

theorem sixteen_le (X' x n : ℝ) (hX : 1 ≤ X') (hx : 16 ≤ x) (hn : 1 ≤ n) : 16 ≤ X' * (x * n) := by
  have h1 : 16 ≤ x * n := by nlinarith
  nlinarith

theorem theta_power_bounds (x k θ Xpp : ℝ) (hx : 16 ≤ x) (hk4 : x ^ 4 ≤ k) (hθ : θ = 1 / (k * x ^ 13)) (hX : 16 ≤ Xpp) :
    0 ≤ θ ∧ 8 * x * θ ^ 2 ≤ (x ^ 16)⁻¹ ∧ 16 * x * θ ≤ (x ^ 16)⁻¹ * Xpp := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hk0 : 0 < k := lt_of_lt_of_le (by positivity) hk4
  have hkx : x ^ 17 ≤ k * x ^ 13 := by
    calc x ^ 17 = x ^ 4 * x ^ 13 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hk4 (pow_pos hx0 13).le
  have hθle : θ ≤ (x ^ 17)⁻¹ := by
    rw [hθ, one_div]
    exact inv_anti₀ (by positivity) hkx
  have hθ0 : 0 ≤ θ := by rw [hθ]; positivity
  have hx16p : 0 < x ^ 16 := by positivity
  have hx17p : 0 < x ^ 17 := by positivity
  refine ⟨hθ0, ?_, ?_⟩
  · have h1 : θ ^ 2 ≤ ((x ^ 17)⁻¹) ^ 2 := pow_le_pow_left₀ hθ0 hθle 2
    have h2 : 8 * x * ((x ^ 17)⁻¹) ^ 2 ≤ (x ^ 16)⁻¹ := by
      have e1 : 8 * x * ((x ^ 17)⁻¹) ^ 2 = (8 * (x ^ 17)⁻¹) * (x ^ 16)⁻¹ := by field_simp
      rw [e1]
      have h3 : (8 : ℝ) ≤ x ^ 17 := le_trans (by linarith) (le_self_pow₀ hx1 (by norm_num))
      have h4 : 8 * (x ^ 17)⁻¹ ≤ 1 := by
        rw [← div_eq_mul_inv, div_le_one hx17p]; exact h3
      calc (8 * (x ^ 17)⁻¹) * (x ^ 16)⁻¹ ≤ 1 * (x ^ 16)⁻¹ := mul_le_mul_of_nonneg_right h4 (by positivity)
        _ = _ := one_mul _
    exact le_trans (mul_le_mul_of_nonneg_left h1 (by positivity)) h2
  · have h1 : 16 * x * θ ≤ 16 * x * (x ^ 17)⁻¹ := mul_le_mul_of_nonneg_left hθle (by positivity)
    have h2 : 16 * x * (x ^ 17)⁻¹ = (x ^ 16)⁻¹ * 16 := by field_simp
    calc 16 * x * θ ≤ (x ^ 16)⁻¹ * 16 := by rw [← h2]; exact h1
      _ ≤ _ := mul_le_mul_of_nonneg_left hX (by positivity)

set_option maxHeartbeats 8000000 in
theorem numT_ev (eps : ℝ) (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ x : ℝ in atTop, ∀ (D : D7) (L : SizeData₂ D), L.sc.x = x → L.sc.eps = eps → Formalism.MainNotions.SizesAt L →
      ParameterChoice' D L → NumT D L C := by
  by_cases he : 0 < eps ∧ eps < 1 / 52
  swap
  · refine Filter.Eventually.of_forall fun x D L _ h2 => ?_
    exact absurd ⟨h2 ▸ L.sc.eps_pos, h2 ▸ L.sc.eps_lt⟩ he
  obtain ⟨he0, he1⟩ := he
  have hτ : 0 < 23 * eps / 48 := by positivity
  have F1 := ev_log 14 (23 * eps / 48) hτ
  have F2 := ev_const C (23 * eps / 48) hτ
  have F3 := ev_const 10 (23 * eps / 48) hτ
  have F4 := ev_log 1 eps he0
  have F5 := ev_pow 3 eps 1 (by linarith)
  have F6 := ev_pow 14 (23 * eps / 48) eps (by linarith)
  have F7 := ev_pow 4 (eps / 3) eps (by linarith)
  have F8 := ev_pow 4 (eps / 4) eps (by linarith)
  have F9 := ev_pow 4 (eps / 2) eps (by linarith)
  have WorkedExample := ev_pow 8 0 eps he0
  have LargeParameterEstimates := ev_log 40 (eps / 3) (by positivity)
  have F12 := ev_log (2 * (Real.log 4 * C * (rE eps : ℝ))) 1 one_pos
  have InertPlaceConditions := ev_log (2 * (Real.log 4 * C)) 1 one_pos
  have F14 := ev_log (40 * C) 1 one_pos
  have F15 := ev_log (4 * C) 1 one_pos
  have F16 := ev_pow 120 eps 1 (by linarith)
  have F17 := ev_log 5 1 one_pos
  have F18 := ev_log 400 eps he0
  filter_upwards [F1, F2, F3, F4, F5, F6, F7, F8, F9, WorkedExample, LargeParameterEstimates, F12, InertPlaceConditions, F14, F15, F16, F17, F18,
    eventually_ge_atTop 16, eventually_ge_atTop 120] with x f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 hx16
    hx120 D L hx heps hS P
  subst hx
  subst heps
  have hx0 := sc_x_pos L.sc
  have hx1 := L.sc.one_lt_alt
  have hlx0 : 0 ≤ Real.log L.sc.x := Real.log_nonneg hx1.le
  have hk1 := one_le_k D
  have hk6 := k_le_x_pow_six L hS
  have hk0 : (0 : ℝ) < (D.R.k : ℝ) := by linarith
  obtain ⟨_, hNmSc, hSc100⟩ := Nm_le_Sc P
  obtain ⟨hSN, hSM, hSK, -, -, -, -, hSTT, -, -, -, -, -, hSEta, -, -, hSDel, -⟩ := hS
  unfold Formalism.MainNotions.SizeN Formalism.MainNotions.szTh at hSN
  unfold Formalism.MainNotions.SizeK Formalism.MainNotions.szTh at hSK
  unfold Formalism.MainNotions.SizeTT Formalism.MainNotions.szNst Formalism.MainNotions.szTh at hSTT
  unfold Formalism.MainNotions.SizeEta at hSEta
  unfold Formalism.MainNotions.SizeDel at hSDel
  rw [Real.rpow_one] at f5 f12 f13 f14 f15 f16 f17
  rw [Real.rpow_zero] at f10
  have mono : ∀ u v : ℝ, u ≤ v → L.sc.x ^ u ≤ L.sc.x ^ v := fun u v h => Real.rpow_le_rpow_of_exponent_le hx1.le h
  have nat4 : L.sc.x ^ (4 : ℝ) = L.sc.x ^ 4 := by rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have nat3 : L.sc.x ^ (3 : ℝ) = L.sc.x ^ 3 := by rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have nat2 : L.sc.x ^ (2 : ℝ) = L.sc.x ^ 2 := by rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have nat6 : L.sc.x ^ (6 : ℝ) = L.sc.x ^ 6 := by rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have natA : L.sc.x ^ Scale.A = L.sc.x ^ 26 := by
    unfold Scale.A; rw [show (26 : ℝ) = ((26 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have natA2 : L.sc.x ^ (Scale.A / 2) = L.sc.x ^ 13 := by
    unfold Scale.A; rw [show (26 / 2 : ℝ) = ((13 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hn3 : (D.R.n : ℝ) ≤ L.sc.x ^ 3 := by rw [← nat3]; exact le_trans hSN.2 (mono _ _ (by linarith))
  have hn2 : L.sc.x ^ 2 ≤ (D.R.n : ℝ) := by rw [← nat2]; exact le_trans (mono _ _ (by linarith)) hSN.1
  have hk4 : L.sc.x ^ 4 ≤ (D.R.k : ℝ) := by rw [← nat4]; exact le_trans (mono _ _ (by linarith)) hSK.1
  rw [nat6] at hk6
  have hn0 : (0 : ℝ) < (D.R.n : ℝ) := lt_of_lt_of_le (by positivity) hn2
  have hxe1 : 1 ≤ L.sc.x ^ L.sc.eps := Real.one_le_rpow hx1.le he0.le
  have hb : L.sc.b = Real.exp (L.sc.x ^ L.sc.eps) := rfl
  have hb0 : 0 < L.sc.b := by rw [hb]; exact Real.exp_pos _
  have ha : L.sc.a = L.sc.x * L.sc.b := rfl
  have ha0 : 0 < L.sc.a := by rw [ha]; positivity
  have hax : L.sc.a / L.sc.x = L.sc.b := by rw [ha]; field_simp
  have hXd : L.sc.X' = Real.exp (L.sc.x ^ (L.sc.eps / 3)) := rfl
  have hX0 : 0 < L.sc.X' := by rw [hXd]; exact Real.exp_pos _
  have hX1 : 1 ≤ L.sc.X' := by rw [hXd]; exact Real.one_le_exp (Real.rpow_nonneg hx0.le _)
  have hb'X : L.sc.b' * L.sc.X' = L.sc.x * L.sc.b := by
    unfold Scale.b'; rw [div_mul_cancel₀ _ hX0.ne', ha]
  have hb'0 := sc_b'_nonneg L.sc
  have hXpp : L.sc.X'' D.R.n = L.sc.X' * (L.sc.x * (D.R.n : ℝ)) := by
    unfold Scale.X'' Scale.w'' Scale.b'
    field_simp
  have hlogX : Real.log L.sc.X' = L.sc.x ^ (L.sc.eps / 3) := by rw [hXd, Real.log_exp]

  have hY10 : 10 ≤ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) := f3
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
          mul_le_mul (mul_le_mul hx16 hk6 hk0.le hx0.le) e_Del hDel0 (by positivity)
      _ ≤ Real.exp ((L.sc.x ^ (23 * L.sc.eps / 48)) / 2) * Real.exp ((L.sc.x ^ (23 * L.sc.eps / 48)) / 2) := mul_le_mul_of_nonneg_right h7 (Real.exp_pos _).le
      _ = (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) := by rw [← Real.exp_add]; congr 1; ring
  have e_Nm : Nm D ≤ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) := by
    have : Nm D ≤ cG L := by unfold Nm cG; linarith
    linarith
  have hNm0 : 0 ≤ Nm D := by unfold Nm; exact Nat.cast_nonneg _
  have e_xn : L.sc.x * (D.R.n : ℝ) ≤ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) := pY _ 4 (le_trans (mul_le_mul_of_nonneg_left hn3 hx0.le) (le_of_eq (by ring))) (by norm_num)
  have e_f : (D.R.f : ℝ) ≤ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) := by
    have hf : (D.R.f : ℝ) = 2 * (D.R.n : ℝ) := by unfold Ranks.f; push_cast; ring
    rw [hf]
    exact le_trans (mul_le_mul_of_nonneg_right (by linarith) hn0.le) e_xn
  have hla : Real.log L.sc.a = Real.log L.sc.x + L.sc.x ^ L.sc.eps := by
    rw [ha, hb, Real.log_mul hx0.ne' (Real.exp_pos _).ne', Real.log_exp]
  have hxY : L.sc.x ≤ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) := pY _ 1 (by rw [pow_one]) (by norm_num)
  have e_la : Real.log L.sc.a ≤ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) := by rw [hla]; linarith
  have hla0 : 0 ≤ Real.log L.sc.a := by rw [hla]; positivity
  have e_la2 : Real.log (2 * L.sc.a) ≤ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) := by
    rw [Real.log_mul (by norm_num) ha0.ne', hla]
    have := Real.log_two_lt_d9
    linarith
  have hla20 : 0 ≤ Real.log (2 * L.sc.a) := Real.log_nonneg (by have := sc_one_lt_a L.sc; linarith)
  have hz100 : 0 < L.sc.x ^ (-100 : ℝ) := Real.rpow_pos_of_pos hx0 _
  have e7 : (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) ^ 7 * L.sc.X' ≤ L.sc.b * L.sc.x ^ (-100 : ℝ) := by
    have hxe : L.sc.x ^ (-100 : ℝ) = Real.exp (-100 * Real.log L.sc.x) := by
      rw [Real.rpow_def_of_pos hx0]; congr 1; ring
    rw [hb, hXd, hxe, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.2
    push_cast
    linarith
  refine ⟨?_, ?_, ?_⟩
  ·
    have hw0 := sc_w''_nonneg L.sc D.R.n
    obtain ⟨hw1, hw2⟩ := w''_le L.sc D.R.n D.R.toFrame.ord_pos
    have hab := two_b'_le_a L.sc
    have hwpos : 0 < L.sc.w'' D.R.n := by
      unfold Scale.w'' Scale.b'; positivity
    have hXw : L.sc.X'' D.R.n * L.sc.w'' D.R.n = L.sc.a := by
      unfold Scale.X''; exact div_mul_cancel₀ _ hwpos.ne'
    have hq : 480 * L.sc.x ^ 2 ≤ (D.R.k : ℝ) * L.sc.x ^ 13 := by
      have h0 : 480 ≤ L.sc.x * L.sc.x := by nlinarith
      have h1 : 480 * L.sc.x ^ 2 ≤ (L.sc.x * L.sc.x) * L.sc.x ^ 2 := mul_le_mul_of_nonneg_right h0 (by positivity)
      have h2 : (L.sc.x * L.sc.x) * L.sc.x ^ 2 = L.sc.x ^ 4 := by ring
      have h3 : L.sc.x ^ 4 ≤ L.sc.x ^ 13 := pow_le_pow_right₀ hx1.le (by norm_num)
      calc 480 * L.sc.x ^ 2 ≤ L.sc.x ^ 4 := by rw [← h2]; exact h1
        _ ≤ 1 * L.sc.x ^ 13 := by rw [one_mul]; exact h3
        _ ≤ _ := mul_le_mul_of_nonneg_right hk1 (pow_pos hx0 13).le
    have hq1 : 1 ≤ (D.R.k : ℝ) * L.sc.x ^ 13 := one_le_mul_of_one_le_of_one_le hk1 (one_le_pow₀ hx1.le)
    have hθ : thW D L.sc = 1 / ((D.R.k : ℝ) * L.sc.x ^ 13) := by unfold thW; rw [natA2]
    have hlg : Real.log (2 * L.sc.X'' D.R.n) ≤ 2 * L.sc.x := by
      rw [hXpp, show 2 * (L.sc.X' * (L.sc.x * (D.R.n : ℝ))) = L.sc.X' * (2 * (L.sc.x * (D.R.n : ℝ))) by ring,
        Real.log_mul hX0.ne' (by positivity), hlogX]
      have h1 : 2 * (L.sc.x * (D.R.n : ℝ)) ≤ L.sc.x ^ ((5 : ℕ) : ℝ) := by
        rw [Real.rpow_natCast]
        have h0 := mul_le_mul_of_nonneg_left hn3 hx0.le
        calc 2 * (L.sc.x * (D.R.n : ℝ)) ≤ L.sc.x * (L.sc.x * L.sc.x ^ 3) :=
              mul_le_mul (by linarith) h0 (by positivity) hx0.le
          _ = L.sc.x ^ 5 := by ring
      have h2 := Real.log_le_log (by positivity) h1
      rw [Real.log_rpow hx0] at h2
      push_cast at h2
      have h3 : L.sc.x ^ (L.sc.eps / 3) ≤ L.sc.x := by
        have := mono (L.sc.eps / 3) 1 (by linarith)
        rwa [Real.rpow_one] at this
      linarith
    have hlg0 : 0 ≤ Real.log (2 * L.sc.X'' D.R.n) := by
      apply Real.log_nonneg
      rw [hXpp]
      have hn1 : (1 : ℝ) ≤ (D.R.n : ℝ) := le_trans (one_le_pow₀ hx1.le) hn2
      have := one_le_mul_of_one_le_of_one_le hX1 (one_le_mul_of_one_le_of_one_le hx1.le hn1)
      linarith
    obtain ⟨hSc1, hSc2⟩ := Sc_facts P
    have hXpp1 : 1 ≤ L.sc.X'' D.R.n := by
      rw [hXpp]
      have hn1 : (1 : ℝ) ≤ (D.R.n : ℝ) := le_trans (one_le_pow₀ hx1.le) hn2
      exact one_le_mul_of_one_le_of_one_le hX1 (one_le_mul_of_one_le_of_one_le hx1.le hn1)
    have h2xY : 2 * L.sc.x ≤ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) :=
      pY _ 2 (two_mul_le_sq _ hx16) (by norm_num)
    have hz16 : L.sc.x ^ (-16 : ℝ) = (L.sc.x ^ 16)⁻¹ := by
      rw [Real.rpow_neg hx0.le, show (16 : ℝ) = ((16 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hn1' : (1 : ℝ) ≤ (D.R.n : ℝ) := le_trans (one_le_pow₀ hx1.le) hn2
    have hXpp16 : 16 ≤ L.sc.X'' D.R.n := by
      rw [hXpp]; exact sixteen_le _ _ _ hX1 hx16 hn1'
    obtain ⟨hθ0, hr1, hr2⟩ := theta_power_bounds L.sc.x (D.R.k : ℝ) (thW D L.sc) (L.sc.X'' D.R.n) hx16 hk4 hθ hXpp16
    rw [← hz16] at hr1 hr2
    have e7a : (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) ^ 7 * L.sc.X' ≤ L.sc.a * L.sc.x ^ (-16 : ℝ) := by
      refine le_trans e7 ?_
      have h1 : L.sc.b ≤ L.sc.a := by rw [ha]; exact le_mul_of_one_le_left hb0.le hx1.le
      exact mul_le_mul h1 (mono _ _ (by norm_num)) hz100.le ha0.le
    unfold thS
    exact numeric_ninth_arith _ _ _ _ L.sc.a L.sc.x L.Sc (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) L.sc.X' _ hXw
      hθ0 (by rw [hθ, div_le_one (by linarith)]; exact hq1) hlg0 hlg (le_trans hlg h2xY)
      (by linarith) hx0 hr1 hr2 (by linarith)
      (by unfold cG at e_c; linarith) hY10 hXpp1
      (by rw [hXpp]; exact mul_le_mul_of_nonneg_left e_xn hX0.le) hX0.le e7a
  ·
    rw [hXpp]
    unfold c1
    exact first_bound_arith C (cG L) L.etaSz _ _ _ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) _ hC hcG0 L.etaSz_pos.le hla20 (by positivity) f2 e_c e_eta e_la2 e_xn
      hX1 hY10 e7
  ·
    rw [hXpp]
    unfold cfl
    exact n1'_arith C _ (Nm D) _ _ _ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) _ hC (Nat.cast_nonneg _) hNm0 hla0 (by positivity) f2 e_f e_Nm e_la e_xn
      hX1 hY10 e7

end Nu

theorem third_estimate_along_family {eps : ℝ} (Fm : FamP eps) (K : Consts) (_hK : K.Nonneg) (C31 Ce Cm : ℝ) (C : ℝ)
    (hC : 0 ≤ C) (X : ∀ x (i : Fm.Ix x), Inst (Fm.D x i) (Fm.L x i)) (Y : ∀ x (i : Fm.Ix x), LatInst (Fm.D x i))
    (hA : AdmFam Fm K X Y C31 Ce Cm) :
    ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, WeightedPrimeSumBound (Fm.D x i) (Fm.L x i) (X x i) K C := by
  obtain ⟨x1, _, H1⟩ := hA 1 one_pos
  obtain ⟨x2, H2⟩ := Filter.eventually_atTop.1 (Nu.numT_ev eps C hC)
  refine ⟨max (Fm.x1 + 1) (max x1 x2), fun x hx i => ?_⟩
  have h0 : Fm.x1 < x := by have := le_trans (le_max_left _ _) hx; linarith
  have h1 : x ≥ x1 := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have h2 : x ≥ x2 := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, aSz⟩ := H1 x h1 i
  exact third_estimate_of_numeric_facts (Fm.params x h0 i) (X x i) K C hC
    (H2 x h2 (Fm.D x i) (Fm.L x i) (Fm.L_x x i h0) (Fm.L_eps x i) aSz.1 (Fm.params x h0 i))

end Formalism.MainNotions.AuxBlock8.Pf.G5

end
