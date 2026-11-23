import Formalism.PolynomialDimension.DigitSumValuationBound

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.CountingSumsFrames

lemma window_parameter_bounds {p N N₁ r : ℕ} {Y a b' Q La : ℝ} (h : HypSeg p N N₁ (r + 1) Y a b' Q La) :
    1 ≤ Y ∧ ((r : ℝ) + 1) ^ 2 * Y ^ 2 ≤ p ∧ ((r : ℝ) + 1) * Y ^ 2 * Real.log a ≤ a / b' ∧
    (N : ℝ) ≤ (r : ℝ) + 1 ∧ (N₁ : ℝ) ^ 4 ≤ (r : ℝ) + 1 ∧ Real.log a ≤ (r : ℝ) + 1 ∧ 0 ≤ La ∧
    La ≤ (r : ℝ) + 1 ∧ ((r : ℝ) + 1) ^ 3 * Q * Y ≤ b' ∧ b' ≤ a ∧ (p : ℝ) < a / b' ∧
    (3 : ℝ) ≤ (r : ℝ) + 1 ∧ (1 : ℝ) ≤ N ∧ (1 : ℝ) ≤ N₁ ∧ 1 ≤ Q ∧ 0 < b' := by
  obtain ⟨hY, hp, h2, hN, hN1, hlog, hLa0, hLa, h4, hba, h6, hk, hN', hN1', hQ, hb0⟩ := h
  push_cast at hp h2 hlog hLa h4
  exact ⟨hY, hp, h2, by exact_mod_cast hN, by exact_mod_cast hN1, hlog, hLa0, hLa, h4, hba, h6,
    by exact_mod_cast hk, by exact_mod_cast hN', by exact_mod_cast hN1', hQ, hb0⟩

lemma derived_parameter_bounds {K Y a b' Q pp : ℝ} (hY : 1 ≤ Y) (hp : K ^ 2 * Y ^ 2 ≤ pp) (h4 : K ^ 3 * Q * Y ≤ b')
    (hba : b' ≤ a) (h6 : pp < a / b') (hK : 3 ≤ K) (hQ : 1 ≤ Q) (hb0 : 0 < b') :
    9 ≤ pp ∧ 27 ≤ b' ∧ pp * b' < a ∧ 243 < a ∧ pp < a ∧ 9 * (K * Q) ≤ a ∧ K ≤ a ∧
      9 * (K * Q * Y) ≤ a ∧ 3 * (K ^ 2 * Q * Y) ≤ a := by
  have hK2 : (9 : ℝ) ≤ K ^ 2 := by
    calc (9 : ℝ) = 3 ^ 2 := by norm_num
      _ ≤ K ^ 2 := by gcongr
  have hK3 : (27 : ℝ) ≤ K ^ 3 := by
    calc (27 : ℝ) = 3 ^ 3 := by norm_num
      _ ≤ K ^ 3 := by gcongr
  have hK0 : 0 < K := by linarith
  have hY2 : 1 ≤ Y ^ 2 := one_le_pow₀ hY
  have hp9 : 9 ≤ pp := by
    calc (9 : ℝ) = 9 * 1 := by norm_num
      _ ≤ K ^ 2 * Y ^ 2 := by gcongr
      _ ≤ pp := hp
  have hb27 : 27 ≤ b' := by
    calc (27 : ℝ) = 27 * 1 * 1 := by norm_num
      _ ≤ K ^ 3 * Q * Y := by gcongr
      _ ≤ b' := h4
  have hpb : pp * b' < a := (lt_div_iff₀ hb0).mp h6
  have h243 : (243 : ℝ) ≤ pp * b' := by
    calc (243 : ℝ) = 9 * 27 := by norm_num
      _ ≤ pp * b' := by gcongr
  have hppa : pp ≤ pp * b' := le_mul_of_one_le_right (by linarith) (by linarith)
  have hKQY : 9 * (K * Q * Y) ≤ a := by
    calc 9 * (K * Q * Y) ≤ K ^ 2 * (K * Q * Y) := by gcongr
      _ = K ^ 3 * Q * Y := by ring
      _ ≤ a := by linarith
  have hKQ : K * Q ≤ K * Q * Y := le_mul_of_one_le_right (by positivity) hY
  have hKK : K ≤ K * Q := le_mul_of_one_le_right hK0.le hQ
  have hK2QY : 3 * (K ^ 2 * Q * Y) ≤ a := by
    calc 3 * (K ^ 2 * Q * Y) ≤ K * (K ^ 2 * Q * Y) := by gcongr
      _ = K ^ 3 * Q * Y := by ring
      _ ≤ a := by linarith
  have hKQ0 : 0 < K * Q := by positivity
  exact ⟨hp9, hb27, hpb, by linarith, by linarith, by linarith, by linarith, hKQY, hK2QY⟩

lemma log_bounds_of_nine_le {pp a : ℝ} (hp : 9 ≤ pp) (ha : pp < a) :
    2 ≤ Real.log pp ∧ 1 < Real.logb pp a ∧ 2 ≤ Real.log a := by
  have h9 : (2 : ℝ) ≤ Real.log 9 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have h1 := Real.exp_one_lt_d9
    have h0 := Real.exp_pos 1
    have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [this]; nlinarith
  have hlp : Real.log 9 ≤ Real.log pp := Real.log_le_log (by norm_num) hp
  have hla : Real.log pp < Real.log a := Real.log_lt_log (by linarith) ha
  refine ⟨by linarith, ?_, by linarith⟩
  unfold Real.logb
  rw [one_lt_div (by linarith)]
  exact hla

lemma log_seg_le_four_logb {p r : ℕ} {a : ℝ} (hp : (9 : ℝ) ≤ p) (hpa : (p : ℝ) < a) (hr : (r : ℝ) ≤ a) :
    0 ≤ lgSeg p a r ∧ lgSeg p a r ≤ 4 * Real.logb p a := by
  have hp1 : (1 : ℝ) < p := by linarith
  have ha0 : 0 < a := by linarith
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  obtain ⟨_, hl1, _⟩ := log_bounds_of_nine_le hp hpa
  have h0 : 0 ≤ Real.logb p (8 * a + r) := Real.logb_nonneg hp1 (by linarith)
  have h1 : Real.logb p (8 * a + r) ≤ Real.logb p (p * a) := by
    apply Real.logb_le_logb_of_le hp1 (by linarith)
    nlinarith
  have h2 : Real.logb p (p * a) = 1 + Real.logb p a := by
    rw [Real.logb_mul (by linarith) ha0.ne', Real.logb_self_eq_one hp1]
  unfold lgSeg
  constructor <;> linarith

lemma depth_real_bound {T S M R Y lg κ fl : ℝ} (hY : 1 ≤ Y) (hR : 2 ≤ R) (hM : 1 ≤ M) (hT0 : 0 ≤ T)
    (hTS : T ≤ S) (hSM : S ≤ M) (hlg : 0 ≤ lg) (hκdef : κ = 3 * (S + 2) * R ^ 2 * lg)
    (hfl : fl ≤ Y * (T * (Y * κ + κ) + κ)) :
    fl + 3 * (S + 1) * lg + 2 * ((T + 1) * (R + 1) * lg) ≤ 45 * Y ^ 2 * M ^ 2 * (R + 1) ^ 2 * lg := by
  have hY0 : 0 < Y := by linarith
  have hS0 : 0 ≤ S := by linarith
  have hκ0 : 0 ≤ κ := by rw [hκdef]; positivity
  have hκ : κ ≤ 9 * M * (R + 1) ^ 2 * lg := by
    rw [hκdef]
    have h1 : 3 * (S + 2) ≤ 9 * M := by linarith
    have h2 : R ^ 2 ≤ (R + 1) ^ 2 := by gcongr; linarith
    gcongr
  have hκY : κ ≤ Y * κ := le_mul_of_one_le_left hκ0 hY
  have hD1 : T * (Y * κ + κ) + κ ≤ 2 * (T + 1) * (Y * κ) := by
    have h1 : T * (Y * κ + κ) ≤ T * (2 * (Y * κ)) := by gcongr; linarith
    linarith
  have hYD : Y * (T * (Y * κ + κ) + κ) ≤ 36 * Y ^ 2 * M ^ 2 * (R + 1) ^ 2 * lg := by
    calc Y * (T * (Y * κ + κ) + κ) ≤ Y * (2 * (T + 1) * (Y * κ)) := by gcongr
      _ ≤ Y * (2 * (2 * M) * (Y * (9 * M * (R + 1) ^ 2 * lg))) := by gcongr; linarith
      _ = 36 * Y ^ 2 * M ^ 2 * (R + 1) ^ 2 * lg := by ring
  have h3 : 3 * (S + 1) * lg + 2 * ((T + 1) * (R + 1) * lg) ≤ κ := by
    rw [hκdef]
    have hc : 3 * (S + 1) + 2 * ((T + 1) * (R + 1)) ≤ 3 * (S + 2) * R ^ 2 := by
      have e1 : (T + 1) * (R + 1) ≤ (S + 1) * (R + 1) := by gcongr
      have e2 : 2 * R + 5 ≤ 3 * R ^ 2 := by nlinarith
      have e3 : (S + 1) * (2 * R + 5) ≤ (S + 1) * (3 * R ^ 2) := by gcongr
      have e4 : 0 ≤ R ^ 2 := by positivity
      linarith
    calc 3 * (S + 1) * lg + 2 * ((T + 1) * (R + 1) * lg)
        = (3 * (S + 1) + 2 * ((T + 1) * (R + 1))) * lg := by ring
      _ ≤ 3 * (S + 2) * R ^ 2 * lg := by gcongr
  have h4 : κ ≤ 9 * Y ^ 2 * M ^ 2 * (R + 1) ^ 2 * lg := by
    have hY2 : 1 ≤ Y ^ 2 := one_le_pow₀ hY
    calc κ ≤ 9 * M * (R + 1) ^ 2 * lg := hκ
      _ = 9 * 1 * (M * 1) * (R + 1) ^ 2 * lg := by ring
      _ ≤ 9 * Y ^ 2 * (M * M) * (R + 1) ^ 2 * lg := by gcongr
      _ = 9 * Y ^ 2 * M ^ 2 * (R + 1) ^ 2 * lg := by ring
  linarith

lemma depth_le_square_bound {p N N₁ r s t : ℕ} {Y a : ℝ} (hY : 1 ≤ Y) (hr : (3 : ℝ) ≤ (r : ℝ) + 1)
    (hN1 : (1 : ℝ) ≤ N₁) (hts : t ≤ s) (hs : s ≤ N₁) (hlg : 0 ≤ lgSeg p a r) :
    DjSeg p N r s t Y a ≤
      45 * Y ^ 2 * (N₁ : ℝ) ^ 2 * ((r : ℝ) + 1) ^ 2 * lgSeg p a r + kap0I p N (r + 1) a := by
  have h := depth_real_bound (T := t) (S := s) (M := N₁) (R := r) (Y := Y) (lg := lgSeg p a r)
    (κ := kapSeg p a r s) (fl := ((⌊Y * firstDepth t Y (kapSeg p a r s)⌋ : ℤ) : ℝ)) hY (by linarith) hN1
    (Nat.cast_nonneg _) (by exact_mod_cast hts) (by exact_mod_cast hs) hlg rfl (Int.floor_le _)
  unfold DjSeg uSeg
  linarith

theorem segment_depth_sum_bound : SegDepthSum := by
  intro p N N₁ r Y a b' Q La h Jn s t hJ hst
  obtain ⟨hY, hp, h2, hN, hN1, hlog, hLa0, hLa, h4, hba, h6, hK, hN', hN1', hQ, hb0⟩ := window_parameter_bounds h
  obtain ⟨hp9, hb27, hpb, h243, hpa, hKQ, hKa, hKQY, hK2QY⟩ := derived_parameter_bounds hY hp h4 hba h6 hK hQ hb0
  obtain ⟨hlp, hl1, hla⟩ := log_bounds_of_nine_le hp9 hpa
  obtain ⟨hlg0, hlg4⟩ := log_seg_le_four_logb (r := r) hp9 hpa (by linarith)
  have hj : ∀ j, DjSeg p N r (s j) (t j) Y a ≤
      45 * Y ^ 2 * (N₁ : ℝ) ^ 2 * ((r : ℝ) + 1) ^ 2 * lgSeg p a r + kap0I p N (r + 1) a :=
    fun j => depth_le_square_bound hY hK hN1' (hst j).1 (hst j).2 hlg0
  have hk0 : kap0I p N (r + 1) a = 2 * N * ((r : ℝ) + 1) * Real.logb p a := by
    unfold kap0I; push_cast; ring
  rw [hk0] at hj
  generalize lgSeg p a r = lg at *
  generalize Real.logb p a = L at *
  generalize (r : ℝ) + 1 = K at *
  have hK0 : 0 < K := by linarith
  have hL0 : 0 < L := by linarith
  have hY2 : 1 ≤ Y ^ 2 := one_le_pow₀ hY
  have hM2 : (N₁ : ℝ) ^ 2 ≤ K :=
    le_trans (pow_le_pow_right₀ hN1' (by norm_num)) hN1
  have e1 : 45 * Y ^ 2 * (N₁ : ℝ) ^ 2 * K ^ 2 * lg ≤ 45 * Y ^ 2 * K * K ^ 2 * (4 * L) := by gcongr
  have e2 : 2 * (N : ℝ) * K * L ≤ 2 * Y ^ 2 * K ^ 3 * L := by
    calc 2 * (N : ℝ) * K * L ≤ 2 * K * K * L := by gcongr
      _ = 2 * 1 * (K ^ 2 * 1) * L := by ring
      _ ≤ 2 * Y ^ 2 * (K ^ 2 * K) * L := by gcongr; linarith
      _ = 2 * Y ^ 2 * K ^ 3 * L := by ring
  have hB : 45 * Y ^ 2 * (N₁ : ℝ) ^ 2 * K ^ 2 * lg + 2 * N * K * L ≤ 182 * Y ^ 2 * K ^ 3 * L := by
    have : 45 * Y ^ 2 * K * K ^ 2 * (4 * L) = 180 * Y ^ 2 * K ^ 3 * L := by ring
    linarith
  have hJ' : (Jn : ℝ) ≤ N := by exact_mod_cast hJ
  calc ∑ j, DjSeg p N r (s j) (t j) Y a ≤ ∑ _j : Fin Jn, 182 * Y ^ 2 * K ^ 3 * L :=
        Finset.sum_le_sum (fun j _ => (hj j).trans hB)
    _ = Jn * (182 * Y ^ 2 * K ^ 3 * L) := by simp
    _ ≤ N * (182 * Y ^ 2 * K ^ 3 * L) := by gcongr
    _ = 182 * N * Y ^ 2 * K ^ 3 * L := by ring

theorem segment_initial_kappa : SegKap0 := by
  intro p N N₁ r s Y a b' Q La ap h hs hap1 hap2
  obtain ⟨hY, hp, h2, hN, hN1, hlog, hLa0, hLa, h4, hba, h6, hK, hN', hN1', hQ, hb0⟩ := window_parameter_bounds h
  obtain ⟨hp9, hb27, hpb, h243, hpa, hKQ, hKa, hKQY, hK2QY⟩ := derived_parameter_bounds hY hp h4 hba h6 hK hQ hb0
  obtain ⟨hlp, hl1, hla⟩ := log_bounds_of_nine_le hp9 hpa
  have hk0 : kap0I p N (r + 1) a = 2 * N * (((r : ℝ) + 1) * Real.logb p a) := by
    unfold kap0I; push_cast; ring
  rw [hk0]
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have ha0 : 0 < a := by linarith
  have hKY : 0 < ((r : ℝ) + 1) * Y := by positivity
  have hx : 0 < 2 / (((r : ℝ) + 1) * Y) := by positivity
  have e1 : Real.log ap ≤ Real.log a + 2 / (((r : ℝ) + 1) * Y) := by
    calc Real.log ap ≤ Real.log (a * (1 + 2 / (((r : ℝ) + 1) * Y))) :=
          Real.log_le_log (by linarith) hap2
      _ = Real.log a + Real.log (1 + 2 / (((r : ℝ) + 1) * Y)) :=
          Real.log_mul ha0.ne' (by positivity)
      _ ≤ Real.log a + 2 / (((r : ℝ) + 1) * Y) := by
          have := Real.log_le_sub_one_of_pos (x := 1 + 2 / (((r : ℝ) + 1) * Y)) (by positivity)
          linarith
  have e2 : (r : ℝ) * (2 / (((r : ℝ) + 1) * Y)) ≤ 2 := by
    rw [← mul_div_assoc, div_le_iff₀ hKY]
    nlinarith
  have e3 : (r : ℝ) * Real.log ap ≤ ((r : ℝ) + 1) * Real.log a := by
    have : (r : ℝ) * Real.log ap ≤ (r : ℝ) * (Real.log a + 2 / (((r : ℝ) + 1) * Y)) := by gcongr
    linarith
  have e4 : (r : ℝ) * Real.logb p ap ≤ ((r : ℝ) + 1) * Real.logb p a := by
    unfold Real.logb
    rw [← mul_div_assoc, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right e3 (by linarith)
  have e5 : 0 ≤ (r : ℝ) * Real.logb p ap :=
    mul_nonneg hr0 (Real.logb_nonneg (by linarith) (by linarith))
  have hs' : (s : ℝ) + 1 ≤ N := by exact_mod_cast hs
  calc (2 * (s : ℝ) + 2) * (r : ℝ) * Real.logb p ap
      = (2 * (s : ℝ) + 2) * ((r : ℝ) * Real.logb p ap) := by ring
    _ ≤ 2 * N * (((r : ℝ) + 1) * Real.logb p a) :=
        mul_le_mul (by linarith) e4 e5 (by positivity)

theorem segment_top_room : SegSTopRoom := by
  intro p N N₁ r Y a b' Q La P Qj A0 sg C h hP hPQ hpP hA0 hsg hC
  obtain ⟨hY, hp, h2, hN, hN1, hlog, hLa0, hLa, h4, hba, h6, hK, hN', hN1', hQ, hb0⟩ := window_parameter_bounds h
  obtain ⟨hp9, hb27, hpb, h243, hpa, hKQ, hKa, hKQY, hK2QY⟩ := derived_parameter_bounds hY hp h4 hba h6 hK hQ hb0
  generalize (r : ℝ) + 1 = K at *
  have hK0 : 0 < K := by linarith
  have ha0 : 0 < a := by linarith
  have h9P : 9 * P ≤ Qj := le_trans (by gcongr) hpP
  have hQj : 0 < Qj := by linarith
  have haP : 0 < a / P := by positivity
  have h1 : a / Qj ≤ a / P / 9 := by
    rw [div_div, mul_comm P 9]
    gcongr
  have h2' : La * A0 ≤ K * (a / P / 9) := by
    calc La * A0 ≤ La * (a / P / 9) := by gcongr; linarith
      _ ≤ K * (a / P / 9) := by gcongr
  have h3 : sg ≤ 2 / 9 * (a / P) := by
    calc sg ≤ 2 * La * A0 / K := hsg
      _ = 2 * (La * A0) / K := by ring
      _ ≤ 2 * (K * (a / P / 9)) / K := by gcongr
      _ = 2 / 9 * (a / P) := by field_simp
  have h4' : K ≤ 1 / 9 * (a / P) := by
    have h9 : 9 * (K * P) ≤ a := le_trans (by gcongr) hKQ
    rw [← mul_div_assoc, le_div_iff₀ hP]
    linarith
  exact ⟨h3, by linarith, by linarith⟩

theorem segment_top_room₂ : SegmentTopRoom := by
  intro p N N₁ r Y a b' Q La P A c o h hP hA0 hA hc ho
  obtain ⟨hY, hp, h2, hN, hN1, hlog, hLa0, hLa, h4, hba, h6, hK, hN', hN1', hQ, hb0⟩ := window_parameter_bounds h
  obtain ⟨hp9, hb27, hpb, h243, hpa, hKQ, hKa, hKQY, hK2QY⟩ := derived_parameter_bounds hY hp h4 hba h6 hK hQ hb0
  generalize (r : ℝ) + 1 = K at *
  generalize (p : ℝ) = pp at *
  have hK0 : 0 < K := by linarith
  have ha0 : 0 < a := by linarith
  have haP : 0 < a / P := by positivity
  have hb9 : b' ≤ a / 9 := by
    have : 9 * b' ≤ pp * b' := by gcongr
    linarith
  have hbP : b' / P ≤ a / P / 9 := by
    calc b' / P ≤ a / 9 / P := by gcongr
      _ = a / P / 9 := by ring
  have hp2 : (81 : ℝ) ≤ pp ^ 2 := by
    calc (81 : ℝ) = 9 ^ 2 := by norm_num
      _ ≤ pp ^ 2 := by gcongr
  have h4p : 4 / pp ^ 2 ≤ 4 / 81 := by gcongr
  have c1 : A * (1 + 4 / pp ^ 2) ≤ 0.25 * (a / P) := by
    calc A * (1 + 4 / pp ^ 2) ≤ (3 * b' / (2 * P)) * (1 + 4 / 81) := by gcongr
      _ = 85 / 54 * (b' / P) := by field_simp; ring
      _ ≤ 85 / 54 * (a / P / 9) := by gcongr
      _ ≤ 0.25 * (a / P) := by norm_num; linarith
  have c2 : a / (pp * P) + (3 * b' / 2) / ((pp ^ 2 - 1) * P) ≤ 0.12 * (a / P) := by
    have d1 : a / (pp * P) ≤ a / (9 * P) := by gcongr
    have d2 : (3 * b' / 2) / ((pp ^ 2 - 1) * P) ≤ (3 * b' / 2) / (80 * P) := by
      gcongr; linarith
    have d3 : a / (9 * P) = a / P / 9 := by field_simp
    have d4 : (3 * b' / 2) / (80 * P) = 3 / 160 * (b' / P) := by field_simp; ring
    have d5 : 3 / 160 * (b' / P) ≤ 3 / 160 * (a / P / 9) := by gcongr
    norm_num
    linarith
  refine ⟨c1, c2, ?_⟩
  have c3 : La * c / K ≤ 0.12 * (a / P) := by
    rw [div_le_iff₀ hK0]
    calc La * c ≤ La * (0.12 * (a / P)) := by gcongr; linarith
      _ ≤ K * (0.12 * (a / P)) := by gcongr
      _ = 0.12 * (a / P) * K := by ring
  norm_num at c1 c3 ⊢
  linarith

lemma clog_le_logb_add_one (p n : ℕ) (x : ℝ) (hp : 2 ≤ p) (hx : 1 ≤ x) (hn : (n : ℝ) ≤ x) :
    (Nat.clog p n : ℝ) ≤ Real.logb p x + 1 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
  rcases Nat.lt_or_ge 1 n with h | h
  · have hlt : p ^ (Nat.clog p n).pred < n := Nat.pow_pred_clog_lt_self (by omega) h
    have hlt' : (p : ℝ) ^ (Nat.clog p n).pred ≤ x := by
      have : ((p ^ (Nat.clog p n).pred : ℕ) : ℝ) < n := by exact_mod_cast hlt
      push_cast at this; linarith
    have h1 : (((Nat.clog p n).pred : ℕ) : ℝ) = Real.logb p ((p : ℝ) ^ (Nat.clog p n).pred) := by
      rw [Real.logb_pow, Real.logb_self_eq_one hp1]; ring
    have h2 : Real.logb p ((p : ℝ) ^ (Nat.clog p n).pred) ≤ Real.logb p x :=
      Real.logb_le_logb_of_le hp1 (by positivity) hlt'
    have h3 : Nat.clog p n ≤ (Nat.clog p n).pred + 1 := by
      simp only [Nat.pred_eq_sub_one]; omega
    have h3' : (Nat.clog p n : ℝ) ≤ ((Nat.clog p n).pred : ℕ) + 1 := by exact_mod_cast h3
    linarith
  · rw [Nat.clog_of_right_le_one h]
    have := Real.logb_nonneg hp1 hx
    simp; linarith

theorem segment_size_bound : SegSize := by
  intro p N N₁ r Y a b' Q La ap P h hap hP
  obtain ⟨hY, hp, h2, hN, hN1, hlog, hLa0, hLa, h4, hba, h6, hK, hN', hN1', hQ, hb0⟩ := window_parameter_bounds h
  obtain ⟨hp9, hb27, hpb, h243, hpa, hKQ, hKa, hKQY, hK2QY⟩ := derived_parameter_bounds hY hp h4 hba h6 hK hQ hb0
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hS : SbdSeg p a b' P ≤ 3 * a := by
    unfold SbdSeg
    rw [div_le_iff₀ (by linarith)]
    have h81 : (4 : ℝ) ≤ (p : ℝ) ^ 2 := by nlinarith
    have : 4 * a / (p : ℝ) ^ 2 ≤ a := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    nlinarith
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, ?_⟩
  intro n hn
  have hp9' : 9 ≤ p := by exact_mod_cast hp9
  exact clog_le_logb_add_one p n (8 * a + r) (by omega) (by linarith) hn

lemma dimPol_succ_mul (r x : ℕ) :
    ((r : ℝ) + 1) * dimPol (r + 1) x = ((x : ℝ) + r + 1) * dimPol r x := by
  unfold dimPol
  have h := Nat.add_one_mul_choose_eq (x + r) r
  have h2 := congrArg (Nat.cast : ℕ → ℝ) h
  push_cast at h2
  rw [show x + (r + 1) = x + r + 1 from rfl]
  linarith

lemma dimPol_ratio_le_pow (r x x' : ℕ) (E : ℝ) (hx : 1 ≤ x) (hxx : x ≤ x') (hE : (x' : ℝ) ≤ E * x) :
    (dimPol r x' : ℝ) ≤ E ^ r * dimPol r x := by
  have hx0 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hxx' : (x : ℝ) ≤ x' := by exact_mod_cast hxx
  have hE1 : 1 ≤ E := by
    by_contra hcon
    have hcon' : E < 1 := not_le.mp hcon
    nlinarith
  induction r with
  | zero => simp [dimPol]
  | succ r ih =>
    have h1 := dimPol_succ_mul r x
    have h2 := dimPol_succ_mul r x'
    have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
    have hr : 0 < (r : ℝ) + 1 := by linarith
    have hfac : (x' : ℝ) + r + 1 ≤ E * ((x : ℝ) + r + 1) := by nlinarith
    have hD0 : (0 : ℝ) ≤ dimPol r x' := Nat.cast_nonneg _
    have hmain : ((r : ℝ) + 1) * dimPol (r + 1) x' ≤ ((r : ℝ) + 1) * (E ^ (r + 1) * dimPol (r + 1) x) := by
      calc ((r : ℝ) + 1) * dimPol (r + 1) x' = ((x' : ℝ) + r + 1) * dimPol r x' := h2
        _ ≤ (E * ((x : ℝ) + r + 1)) * (E ^ r * dimPol r x) :=
            mul_le_mul hfac ih hD0 (by positivity)
        _ = E ^ (r + 1) * (((x : ℝ) + r + 1) * dimPol r x) := by ring
        _ = E ^ (r + 1) * (((r : ℝ) + 1) * dimPol (r + 1) x) := by rw [h1]
        _ = ((r : ℝ) + 1) * (E ^ (r + 1) * dimPol (r + 1) x) := by ring
    exact le_of_mul_le_mul_left hmain hr

theorem binomial_ratio_exp_bound : BinomRatioExp := by
  intro r x x' hx hxx
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  have hE : (x' : ℝ) ≤ Real.exp (((x' : ℝ) - x) / x) * x := by
    have h1 := Real.add_one_le_exp (((x' : ℝ) - x) / x)
    have h2 : (((x' : ℝ) - x) / x + 1) * x = x' := by field_simp; ring
    calc (x' : ℝ) = (((x' : ℝ) - x) / x + 1) * x := h2.symm
      _ ≤ Real.exp (((x' : ℝ) - x) / x) * x := by gcongr
  have h := dimPol_ratio_le_pow r x x' _ hx hxx hE
  rw [← Real.exp_nat_mul] at h
  have e : (r : ℝ) * (((x' : ℝ) - x) / x) = (r : ℝ) * ((x' : ℝ) - x) / x := by ring
  rwa [e] at h

lemma window_dim_ratio_le_exp (r C C' : ℕ) (lo hi c : ℝ) (hlo : 0 < lo) (hc : 0 ≤ c)
    (h : (r : ℝ) * (hi - lo) ≤ c * lo) (h1 : lo ≤ C) (h2 : lo ≤ C') (h3 : (C : ℝ) ≤ hi)
    (h4 : (C' : ℝ) ≤ hi) :
    (r : ℝ) * |(C' : ℝ) - C| / min (C : ℝ) C' ≤ c ∧
      (dimPol r C' : ℝ) ≤ Real.exp c * dimPol r C := by
  have hmin : lo ≤ min (C : ℝ) C' := le_min h1 h2
  have habs : |(C' : ℝ) - C| ≤ hi - lo := by rw [abs_le]; constructor <;> linarith
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  constructor
  · rw [div_le_iff₀ (by linarith)]
    calc (r : ℝ) * |(C' : ℝ) - C| ≤ (r : ℝ) * (hi - lo) := by gcongr
      _ ≤ c * lo := h
      _ ≤ c * min (C : ℝ) C' := by gcongr
  · rcases le_total C C' with hle | hle
    · have hC0 : (0 : ℝ) < C := by linarith
      have hC1 : 1 ≤ C := by exact_mod_cast hC0
      refine (binomial_ratio_exp_bound r C C' hC1 hle).trans ?_
      have harg : (r : ℝ) * ((C' : ℝ) - C) / C ≤ c := by
        rw [div_le_iff₀ hC0]
        calc (r : ℝ) * ((C' : ℝ) - C) ≤ (r : ℝ) * (hi - lo) := by gcongr
          _ ≤ c * lo := h
          _ ≤ c * C := by gcongr
      gcongr
    · have hm : dimPol r C' ≤ dimPol r C := Nat.choose_le_choose r (by omega)
      have hm' : (dimPol r C' : ℝ) ≤ dimPol r C := by exact_mod_cast hm
      have he : 1 ≤ Real.exp c := Real.one_le_exp hc
      have hD0 : (0 : ℝ) ≤ dimPol r C := Nat.cast_nonneg _
      calc (dimPol r C' : ℝ) ≤ 1 * dimPol r C := by linarith
        _ ≤ Real.exp c * dimPol r C := by gcongr

lemma window_numeric_bound {R Y a P W w : ℝ} (hK : 3 ≤ R + 1) (hY : 1 ≤ Y) (hP : 0 < P) (hW0 : 0 ≤ W)
    (hW : (R + 1) * Y * W ≤ w * a) (hw0 : 0 ≤ w) (hw : w ≤ 5) (h3 : 3 * ((R + 1) ^ 2 * P * Y) ≤ a)
    (h9 : 9 * ((R + 1) * P) ≤ a) :
    0 < a / P - (R + 1) ∧
      R * ((a + W) / P - (a / P - (R + 1))) ≤ (w + 1) / Y * (a / P - (R + 1)) := by
  have hY0 : 0 < Y := by linarith
  have hKP : 0 < (R + 1) * P := by positivity
  have ha0 : 0 < a := by linarith
  have e0 : a / P - (R + 1) = (a - (R + 1) * P) / P := by field_simp
  have e1 : (a + W) / P - (a / P - (R + 1)) = (W + (R + 1) * P) / P := by field_simp; ring
  rw [e1, e0]
  refine ⟨div_pos (by linarith) hP, ?_⟩
  have hmain : R * (W + (R + 1) * P) * Y ≤ (w + 1) * (a - (R + 1) * P) := by
    have f1 : R * (W + (R + 1) * P) * Y ≤ (R + 1) * (W + (R + 1) * P) * Y := by
      gcongr; linarith
    have f2 : (R + 1) * (W + (R + 1) * P) * Y = (R + 1) * Y * W + (R + 1) ^ 2 * P * Y := by ring
    have f3 : (w + 1) * (8 / 9 * a) ≤ (w + 1) * (a - (R + 1) * P) := by gcongr; linarith
    have f4 : 0 ≤ (5 - w) * a := mul_nonneg (by linarith) ha0.le
    nlinarith
  have g1 : R * ((W + (R + 1) * P) / P) = R * (W + (R + 1) * P) / P := by ring
  have g2 : (w + 1) / Y * ((a - (R + 1) * P) / P) = (w + 1) * (a - (R + 1) * P) / Y / P := by ring
  rw [g1, g2]
  apply div_le_div_of_nonneg_right _ hP.le
  rw [le_div_iff₀ hY0]
  exact hmain

theorem segment_window_ratio : SegWindowRatio := by
  intro p N N₁ r Y a b' Q La P C C' h hP hPQ hC hC' hCh hCh'
  obtain ⟨hY, hp, h2, hN, hN1, hlog, hLa0, hLa, h4, hba, h6, hK, hN', hN1', hQ, hb0⟩ := window_parameter_bounds h
  obtain ⟨hp9, hb27, hpb, h243, hpa, hKQ, hKa, hKQY, hK2QY⟩ := derived_parameter_bounds hY hp h4 hba h6 hK hQ hb0
  have hY0 : 0 < Y := by linarith
  have hK0 : 0 < (r : ℝ) + 1 := by linarith
  have ha0 : 0 < a := by linarith
  have hP0 : 0 < P := by linarith
  have hW : ((r : ℝ) + 1) * Y * (a / (((r : ℝ) + 1) * Y)) ≤ 1 * a := by
    rw [mul_div_cancel₀ _ (by positivity)]; linarith
  have h3 : 3 * (((r : ℝ) + 1) ^ 2 * P * Y) ≤ a := le_trans (by gcongr) hK2QY
  have h9 : 9 * (((r : ℝ) + 1) * P) ≤ a := le_trans (by gcongr) hKQ
  obtain ⟨hlo, hnum⟩ := window_numeric_bound (R := r) (w := 1) hK hY hP0 (by positivity) hW (by norm_num)
    (by norm_num) h3 h9
  have e : ((1 : ℝ) + 1) / Y = 2 / Y := by norm_num
  rw [e] at hnum
  exact window_dim_ratio_le_exp r C C' _ _ (2 / Y) hlo (by positivity) hnum hC hC' hCh hCh'

theorem segment_window_dimensions : SegWindowDims := by
  intro p N N₁ r s A0 Y a b' Q La P A Clo Chi h hs hNY hP hlo hhi
  have hY : 1 ≤ Y := h.1
  have hY0 : 0 < Y := by linarith
  have hi : ∀ i, (dimPol r (Chi i) : ℝ) ≤ Real.exp (2 / Y) * dimPol r (Clo i) := fun i =>
    (segment_window_ratio p N N₁ r Y a b' Q La (P i) (Clo i) (Chi i) h (hP i).1 (hP i).2 (hlo i).1
      (hhi i).1 (hlo i).2 (hhi i).2).2
  have main : (dimMM r A0 A Chi : ℝ) ≤ Real.exp (2 * s / Y) * dimMM r A0 A Clo := by
    unfold dimMM
    push_cast
    have hprod : ∏ i, ((dimPol r (A i) : ℝ) * dimPol r (Chi i)) ≤
        ∏ i, (Real.exp (2 / Y) * ((dimPol r (A i) : ℝ) * dimPol r (Clo i))) := by
      apply Finset.prod_le_prod
      · intro i _; positivity
      · intro i _
        calc (dimPol r (A i) : ℝ) * dimPol r (Chi i)
            ≤ (dimPol r (A i) : ℝ) * (Real.exp (2 / Y) * dimPol r (Clo i)) := by
              gcongr; exact hi i
          _ = Real.exp (2 / Y) * ((dimPol r (A i) : ℝ) * dimPol r (Clo i)) := by ring
    have e : ∏ i, (Real.exp (2 / Y) * ((dimPol r (A i) : ℝ) * dimPol r (Clo i))) =
        Real.exp (2 * s / Y) * ∏ i, ((dimPol r (A i) : ℝ) * dimPol r (Clo i)) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        ← Real.exp_nat_mul]
      congr 2
      ring
    rw [e] at hprod
    calc (dimPol r A0 : ℝ) * ∏ i, ((dimPol r (A i) : ℝ) * dimPol r (Chi i))
        ≤ (dimPol r A0 : ℝ) *
            (Real.exp (2 * s / Y) * ∏ i, ((dimPol r (A i) : ℝ) * dimPol r (Clo i))) := by gcongr
      _ = Real.exp (2 * s / Y) *
            ((dimPol r A0 : ℝ) * ∏ i, ((dimPol r (A i) : ℝ) * dimPol r (Clo i))) := by ring
  refine ⟨main, main.trans ?_⟩
  have hsY : (s : ℝ) ≤ Y := le_trans (by exact_mod_cast hs) hNY
  have harg : 2 * (s : ℝ) / Y ≤ 2 := by rw [div_le_iff₀ hY0]; linarith
  gcongr

theorem segment_ratio_usage : UseSegRatio := by
  intro r s A0 A C i Cp a L P ha hP hKP hCCp hCpL hlo
  have hCCp' : (C i : ℝ) ≤ Cp := by exact_mod_cast hCCp
  have hLP : 0 ≤ L / P := by linarith
  have hL : 0 ≤ L := by
    have := mul_nonneg hLP hP.le
    rwa [div_mul_cancel₀ _ hP.ne'] at this
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hE1 : 1 ≤ Real.exp (((r : ℝ) + 1) * L / a) := Real.one_le_exp (by positivity)
  have key : (dimPol r Cp : ℝ) ≤ Real.exp (((r : ℝ) + 1) * L / a) * dimPol r (C i) := by
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · simpa [dimPol] using hE1
    · have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
      have haP : ((r : ℝ) + 1) ^ 2 ≤ a / P := by rw [le_div_iff₀ hP]; exact hKP
      have hlo' : 0 < a / P - ((r : ℝ) + 1) := by nlinarith
      have hC0 : (0 : ℝ) < C i := by linarith
      have hC1 : 1 ≤ C i := by exact_mod_cast hC0
      refine (binomial_ratio_exp_bound r (C i) Cp hC1 hCCp).trans ?_
      have harg : (r : ℝ) * ((Cp : ℝ) - C i) / C i ≤ ((r : ℝ) + 1) * L / a := by
        rw [div_le_div_iff₀ hC0 ha]
        have m1 : (r : ℝ) * (L / P) * a ≤ ((r : ℝ) + 1) * L * (a / P - ((r : ℝ) + 1)) := by
          have g1 : (r : ℝ) * (L / P) * a = (r : ℝ) * L * a / P := by ring
          have g2 : ((r : ℝ) + 1) * L * (a / P - ((r : ℝ) + 1)) =
              ((r : ℝ) + 1) * L * (a - ((r : ℝ) + 1) * P) / P := by field_simp
          rw [g1, g2]
          apply div_le_div_of_nonneg_right _ hP.le
          nlinarith [mul_nonneg hL (sub_nonneg.mpr hKP)]
        calc (r : ℝ) * ((Cp : ℝ) - C i) * a ≤ (r : ℝ) * (L / P) * a := by gcongr; linarith
          _ ≤ ((r : ℝ) + 1) * L * (a / P - ((r : ℝ) + 1)) := m1
          _ ≤ ((r : ℝ) + 1) * L * C i := by gcongr
      gcongr
  generalize Real.exp (((r : ℝ) + 1) * L / a) = E at *
  unfold dimMM
  push_cast
  have hprod : ∏ j, ((dimPol r (A j) : ℝ) * dimPol r (Function.update C i Cp j)) ≤
      ∏ j, ((if j = i then E else 1) * ((dimPol r (A j) : ℝ) * dimPol r (C j))) := by
    apply Finset.prod_le_prod
    · intro j _; positivity
    · intro j _
      by_cases hj : j = i
      · subst hj
        simp only [Function.update_self, if_true]
        calc (dimPol r (A j) : ℝ) * dimPol r Cp ≤ (dimPol r (A j) : ℝ) * (E * dimPol r (C j)) := by
              gcongr
          _ = E * ((dimPol r (A j) : ℝ) * dimPol r (C j)) := by ring
      · simp [hj]
  have e : ∏ j, ((if j = i then E else 1) * ((dimPol r (A j) : ℝ) * dimPol r (C j))) =
      E * ∏ j, ((dimPol r (A j) : ℝ) * dimPol r (C j)) := by
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq']
    simp
  rw [e] at hprod
  calc (dimPol r A0 : ℝ) * ∏ j, ((dimPol r (A j) : ℝ) * dimPol r (Function.update C i Cp j))
      ≤ (dimPol r A0 : ℝ) * (E * ∏ j, ((dimPol r (A j) : ℝ) * dimPol r (C j))) := by gcongr
    _ = E * ((dimPol r A0 : ℝ) * ∏ j, ((dimPol r (A j) : ℝ) * dimPol r (C j))) := by ring

theorem segment_extension_window : SegExtWindow := by
  intro p N N₁ r Y a b' Q La x h h2' hx0 hx
  obtain ⟨hY, hp, h2, hN, hN1, hlog, hLa0, hLa, h4, hba, h6, hK, hN', hN1', hQ, hb0⟩ := window_parameter_bounds h
  obtain ⟨hp9, hb27, hpb, h243, hpa, hKQ, hKa, hKQY, hK2QY⟩ := derived_parameter_bounds hY hp h4 hba h6 hK hQ hb0
  obtain ⟨hlp, hl1, hla⟩ := log_bounds_of_nine_le hp9 hpa
  have hY0 : 0 < Y := by linarith
  have hK0 : 0 < (r : ℝ) + 1 := by linarith
  have ha0 : 0 < a := by linarith
  have hl0 : 0 < Real.log a := by linarith
  have hKY0 : 0 < ((r : ℝ) + 1) * Y := by positivity
  have hKY3 : 3 ≤ ((r : ℝ) + 1) * Y := by
    calc (3 : ℝ) = 3 * 1 := by norm_num
      _ ≤ ((r : ℝ) + 1) * Y := by gcongr
  have hU0 : 0 < a / (((r : ℝ) + 1) * Y) := by positivity
  have e0 : ((r : ℝ) + 1) * Y ^ 2 * La * Real.log a * b' ≤ a := (le_div_iff₀ hb0).mp h2'
  have e1 : La * b' ≤ a / (((r : ℝ) + 1) * Y ^ 2 * Real.log a) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have c1 : x ≤ 2 * a / (((r : ℝ) + 1) ^ 2 * Y ^ 2 * Real.log a) := by
    calc x ≤ 2 * (La * b' / ((r : ℝ) + 1)) := hx
      _ ≤ 2 * (a / (((r : ℝ) + 1) * Y ^ 2 * Real.log a) / ((r : ℝ) + 1)) := by gcongr
      _ = 2 * a / (((r : ℝ) + 1) ^ 2 * Y ^ 2 * Real.log a) := by field_simp
  have c2' : 2 * a / (((r : ℝ) + 1) ^ 2 * Y ^ 2 * Real.log a) ≤ 2 / 3 * (a / (((r : ℝ) + 1) * Y)) := by
    rw [div_le_iff₀ (by positivity)]
    have g : 2 / 3 * (a / (((r : ℝ) + 1) * Y)) * (((r : ℝ) + 1) ^ 2 * Y ^ 2 * Real.log a) =
        2 / 3 * a * (((r : ℝ) + 1) * Y * Real.log a) := by field_simp
    rw [g]
    have g3 : 3 ≤ ((r : ℝ) + 1) * Y * Real.log a := by
      calc (3 : ℝ) = 3 * 1 := by norm_num
        _ ≤ ((r : ℝ) + 1) * Y * Real.log a := by gcongr; linarith
    have g4 : 2 / 3 * a * 3 ≤ 2 / 3 * a * (((r : ℝ) + 1) * Y * Real.log a) := by gcongr
    linarith
  have c2'' : x ≤ 2 / 3 * (a / (((r : ℝ) + 1) * Y)) := c1.trans c2'
  have c2 : x ≤ a / (((r : ℝ) + 1) * Y) := by linarith
  have eU : a * (1 + 2 / (((r : ℝ) + 1) * Y)) = a + 2 * (a / (((r : ℝ) + 1) * Y)) := by ring
  have hU3 : a / (((r : ℝ) + 1) * Y) ≤ a / 3 := by gcongr
  have c5 : 1 / Y + ((r : ℝ) + 1) * x / a ≤ 1 / (3 * Y / 5) := by
    have g1 : ((r : ℝ) + 1) * x / a ≤ ((r : ℝ) + 1) * (2 / 3 * (a / (((r : ℝ) + 1) * Y))) / a := by
      gcongr
    have g2 : ((r : ℝ) + 1) * (2 / 3 * (a / (((r : ℝ) + 1) * Y))) / a = 2 / 3 * (1 / Y) := by
      field_simp
    have g3 : 1 / (3 * Y / 5) = 5 / 3 * (1 / Y) := by field_simp
    rw [g3]
    linarith
  refine ⟨c1, c2, by rw [eU]; linarith, by rw [eU]; linarith, c5, ?_⟩
  intro P C C' hP hPQ hC hC' hCh hCh'
  have hP0 : 0 < P := by linarith
  have hW : ((r : ℝ) + 1) * Y * (a / (((r : ℝ) + 1) * Y) + x) ≤ 2 * a := by
    have g1 : ((r : ℝ) + 1) * Y * (a / (((r : ℝ) + 1) * Y) + x) ≤
        ((r : ℝ) + 1) * Y * (a / (((r : ℝ) + 1) * Y) + a / (((r : ℝ) + 1) * Y)) := by gcongr
    have g2 : ((r : ℝ) + 1) * Y * (a / (((r : ℝ) + 1) * Y) + a / (((r : ℝ) + 1) * Y)) = 2 * a := by
      field_simp; ring
    linarith
  have h3 : 3 * (((r : ℝ) + 1) ^ 2 * P * Y) ≤ a := le_trans (by gcongr) hK2QY
  have h9 : 9 * (((r : ℝ) + 1) * P) ≤ a := le_trans (by gcongr) hKQ
  obtain ⟨hlo, hnum⟩ := window_numeric_bound (R := r) (w := 2) hK hY hP0 (by positivity) hW (by norm_num)
    (by norm_num) h3 h9
  have e : ((2 : ℝ) + 1) / Y = 3 / Y := by norm_num
  rw [e, ← add_assoc] at hnum
  exact window_dim_ratio_le_exp r C C' _ _ (3 / Y) hlo (by positivity) hnum hC hC' hCh hCh'

theorem segment_extension_bound : SegExtB := by
  intro C La k N₁ b' bLo bHi x hC hLa hk hN hb h1 h2 hde hx
  have hq : 0 ≤ La / k := div_nonneg hLa hk.le
  have hw : 0 ≤ (bHi - bLo) / b' := div_nonneg (by linarith) hb.le
  have e1 : C * N₁ * La / k = C * N₁ * (La / k) := by ring
  have e2 : 2 * (bHi - bLo) / b' = 2 * ((bHi - bLo) / b') := by ring
  rw [e1, e2] at hde
  have hCN : 4 ≤ C * N₁ := by nlinarith
  have h4 : 4 * (La / k) ≤ C * N₁ * (La / k) := mul_le_mul_of_nonneg_right hCN hq
  have hw12 : (bHi - bLo) / b' < 1 / 12 := by linarith
  have hq24 : La / k < 1 / 24 := by linarith
  have hdiff : bHi - bLo < b' / 12 := by
    rw [div_lt_iff₀ hb] at hw12; linarith
  have hx' : x ≤ b' / 12 := by
    have : La * b' / k = (La / k) * b' := by ring
    rw [this] at hx
    nlinarith
  exact ⟨hw12, hq24, by linarith, by linarith, by linarith, by linarith⟩

end Formalism.CountingSumsFrames
