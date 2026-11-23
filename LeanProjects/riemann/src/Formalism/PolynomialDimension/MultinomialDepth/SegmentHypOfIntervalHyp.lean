import Formalism.PolynomialDimension.DigitSumValuationBound

open scoped BigOperators
open Finset

namespace Formalism.CountingSumsFrames

theorem segment_hyp_of_interval_hyp : HypSegOfHypI := by
  intro C C₀ hC hC₀ p N N₁ k n' G' Y Yb a b' Ib cl D cStar h
  obtain ⟨hY, hp, hN, hN1, hk, hLa8, hIb1, hIb2, hYb, h2Yb, hab, hde, hpab, hkLa, hcl0, hcl, hD, hcS, hb, hb0⟩ := h
  set La := C₀ * (N₁ : ℝ) ^ 2 * Real.log a with hLadef
  set Q := (p : ℝ) ^ G' with hQdef
  set S := cStar + N * cl + n' * cl with hSdef
  have hC0 : 0 < C := by linarith
  have hC₀0 : 0 < C₀ := by linarith
  have hY0 : 0 < Y := by linarith
  have hNr : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hN1r : (1:ℝ) ≤ N₁ := by exact_mod_cast hN1
  have hkr : (5:ℝ) ≤ k := by exact_mod_cast (by omega : 5 ≤ k)
  have hk0 : (0:ℝ) < k := by linarith
  have hY2 : 1 ≤ Y ^ 2 := one_le_pow₀ hY
  have hk2 : (25:ℝ) ≤ (k:ℝ) ^ 2 := by
    calc (25:ℝ) = 5 ^ 2 := by norm_num
      _ ≤ (k:ℝ) ^ 2 := by gcongr
  have hk3 : (125:ℝ) ≤ (k:ℝ) ^ 3 := by
    calc (125:ℝ) = 5 ^ 3 := by norm_num
      _ ≤ (k:ℝ) ^ 3 := by gcongr
  have hpr : (25:ℝ) ≤ p := by
    calc (25:ℝ) = 25 * 1 := by norm_num
      _ ≤ (k:ℝ) ^ 2 * Y ^ 2 := by gcongr
      _ ≤ p := hp
  have hp0 : (0:ℝ) < p := by linarith
  have hpb : (p:ℝ) * b' < a := (lt_div_iff₀ hb0).mp hpab
  have ha0 : 0 < a := by
    have : 0 < (p:ℝ) * b' := by positivity
    linarith
  have hlogNY : 0 ≤ Real.log (N * Y) := Real.log_nonneg (one_le_mul_of_one_le_of_one_le hNr hY)
  have hLa0 : 0 ≤ La := by linarith
  have hc1 : 1 ≤ C₀ * (N₁ : ℝ) ^ 2 := by
    have : 1 ≤ (N₁:ℝ) ^ 2 := one_le_pow₀ hN1r
    exact one_le_mul_of_one_le_of_one_le hC₀ this
  have hlog0 : 0 ≤ Real.log a := (mul_nonneg_iff_of_pos_left (by linarith : 0 < C₀ * (N₁ : ℝ) ^ 2)).mp hLa0
  have hlogb0 : 0 ≤ Real.logb p a := div_nonneg hlog0 (Real.log_nonneg (by linarith))
  have hD0 : 0 ≤ D := le_trans (mul_nonneg (by positivity) hlogb0) hD
  have hcS8 : 8 ≤ cStar := by linarith
  have hQ1 : 1 ≤ Q := one_le_pow₀ (by linarith)
  have hQ0 : 0 < Q := by linarith
  have hQ4 : Q ≤ Q ^ 4 := le_self_pow₀ hQ1 (by norm_num)
  have hS8 : 8 ≤ S := by
    have h1 : 0 ≤ (N:ℝ) * cl := by positivity
    have h2 : 0 ≤ (n':ℝ) * cl := by positivity
    linarith
  have hS0 : 0 < S := by linarith
  have hkQY : (k:ℝ) ^ 3 * Q * Y ≤ b' := by
    calc (k:ℝ) ^ 3 * Q * Y = 1 * (k:ℝ) ^ 3 * 1 * Q * 1 * Y := by ring
      _ ≤ C * (k:ℝ) ^ 3 * N * Q ^ 4 * S * Y := by gcongr; linarith
      _ ≤ b' := hb
  have hb1000 : 1000 ≤ b' := by
    calc (1000:ℝ) = 1 * 125 * 1 * 1 * 8 * 1 := by norm_num
      _ ≤ C * (k:ℝ) ^ 3 * N * Q ^ 4 * S * Y := by gcongr; linarith
      _ ≤ b' := hb
  have ha25 : 25000 < a := by
    have : (25:ℝ) * 1000 ≤ (p:ℝ) * b' := mul_le_mul hpr hb1000 (by norm_num) (by linarith)
    linarith
  have hlog1 : 1 ≤ Real.log a := by
    rw [Real.le_log_iff_exp_le ha0]
    have := Real.exp_one_lt_d9
    linarith
  have hLalog : Real.log a ≤ La := le_mul_of_one_le_left hlog0 hc1
  have hLa1 : 1 ≤ La := by linarith
  have hLa2 : La ≤ La ^ 2 := le_self_pow₀ hLa1 (by norm_num)
  have hba : b' ≤ a := by
    have : b' ≤ (p:ℝ) * b' := le_mul_of_one_le_left hb0.le (by linarith)
    linarith
  have hLak : La ^ 2 ≤ k := by
    calc La ^ 2 = 1 * 1 * La ^ 2 := by ring
      _ ≤ C * N * La ^ 2 := by gcongr
      _ ≤ k := hkLa
  have hYb1 : 1 ≤ Yb := by linarith
  refine ⟨⟨hY, hp, ?_, ?_, ?_, by linarith, hLa0, by linarith, hkQY, hba, hpab, by omega, hN, hN1, hQ1, hb0⟩, ?_, ?_⟩
  · calc (k:ℝ) * Y ^ 2 * Real.log a = (k:ℝ) * Y ^ 2 * 1 * 1 * 1 * Real.log a := by ring
      _ ≤ (k:ℝ) * Y ^ 2 * Yb * N * La * Real.log a := by gcongr
      _ ≤ a / b' := hab
  · have : (N:ℝ) ≤ k := by
      calc (N:ℝ) = 1 * N * 1 := by ring
        _ ≤ C * N * La ^ 2 := by gcongr; linarith
        _ ≤ k := hkLa
    exact_mod_cast this
  · have h1 : (N₁:ℝ) ^ 2 ≤ La := by
      calc (N₁:ℝ) ^ 2 = 1 * (N₁:ℝ) ^ 2 * 1 := by ring
        _ ≤ C₀ * (N₁:ℝ) ^ 2 * Real.log a := by gcongr
    have h2 : (N₁:ℝ) ^ 4 ≤ La ^ 2 := by
      calc (N₁:ℝ) ^ 4 = ((N₁:ℝ) ^ 2) ^ 2 := by ring
        _ ≤ La ^ 2 := by gcongr
    have : (N₁:ℝ) ^ 4 ≤ k := by linarith
    exact_mod_cast this
  · have : a / (k * Y) ≤ a := div_le_self ha0.le (one_le_mul_of_one_le_of_one_le (by linarith) hY)
    linarith
  · intro bLo bHi h1 h2 h3
    constructor <;> linarith

lemma segment_parameter_bounds {p N N₁ r : ℕ} {Y a b' Q La : ℝ} (h : HypSeg p N N₁ (r + 1) Y a b' Q La) :
    1 ≤ Y ∧ ((r:ℝ)+1)^2 * Y^2 ≤ p ∧ ((r:ℝ)+1) * Y^2 * Real.log a ≤ a / b' ∧ Real.log a ≤ (r:ℝ)+1 ∧
    ((r:ℝ)+1)^3 * Q * Y ≤ b' ∧ b' ≤ a ∧ (p:ℝ) < a / b' ∧ (2:ℝ) ≤ r ∧ 1 ≤ Q ∧ 0 < b' ∧ (9:ℝ) ≤ p ∧
    27 ≤ b' ∧ (p:ℝ) * b' < a ∧ 1 ≤ Real.log a ∧ (1:ℝ) ≤ N₁ ∧ (r:ℝ) + 1 ≤ b' := by
  obtain ⟨hY, hp, h2, hN, hN1, hlog, hLa0, hLa, h4, hba, h6, hk, hN', hN1', hQ, hb0⟩ := h
  push_cast at hp h2 hlog h4
  have hr : (2:ℝ) ≤ r := by exact_mod_cast (by omega : 2 ≤ r)
  have hk2 : (9:ℝ) ≤ ((r:ℝ)+1)^2 := by
    calc (9:ℝ) = 3 ^ 2 := by norm_num
      _ ≤ _ := by gcongr; linarith
  have hk3 : (27:ℝ) ≤ ((r:ℝ)+1)^3 := by
    calc (27:ℝ) = 3 ^ 3 := by norm_num
      _ ≤ _ := by gcongr; linarith
  have hY2 : 1 ≤ Y ^ 2 := one_le_pow₀ hY
  have hpr : (9:ℝ) ≤ p := by
    calc (9:ℝ) = 9 * 1 := by norm_num
      _ ≤ ((r:ℝ)+1) ^ 2 * Y ^ 2 := by gcongr
      _ ≤ p := hp
  have hb27 : 27 ≤ b' := by
    calc (27:ℝ) = 27 * 1 * 1 := by norm_num
      _ ≤ ((r:ℝ)+1) ^ 3 * Q * Y := by gcongr
      _ ≤ b' := h4
  have hkb : (r:ℝ) + 1 ≤ b' := by
    have h1 : (r:ℝ) + 1 ≤ ((r:ℝ)+1)^3 := le_self_pow₀ (by linarith) (by norm_num)
    calc (r:ℝ) + 1 = ((r:ℝ) + 1) * 1 * 1 := by ring
      _ ≤ ((r:ℝ)+1) ^ 3 * Q * Y := by gcongr
      _ ≤ b' := h4
  have hpb : (p:ℝ) * b' < a := (lt_div_iff₀ hb0).mp h6
  have ha : 243 < a := by
    have : (9:ℝ) * 27 ≤ (p:ℝ) * b' := mul_le_mul hpr hb27 (by norm_num) (by linarith)
    linarith
  have hlog1 : 1 ≤ Real.log a := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hN1r : (1:ℝ) ≤ N₁ := by exact_mod_cast hN1'
  exact ⟨hY, hp, h2, hlog, h4, hba, h6, hr, hQ, hb0, hpr, hb27, hpb, hlog1, hN1r, hkb⟩

theorem segment_log_bound : SegLg := by
  intro p N N₁ r Y a b' Q La h
  obtain ⟨hY, hp, h2, hlog, h4, hba, h6, hr, hQ, hb0, hp9, hb27, hpb, hL1, hN1, hkb⟩ := segment_parameter_bounds h
  have hp1 : (1:ℝ) < p := by linarith
  have hp0 : (0:ℝ) < p := by linarith
  have ha0 : 0 < a := by linarith
  have hpa : (p:ℝ) < a := by
    have : (p:ℝ) * 1 ≤ (p:ℝ) * b' := mul_le_mul_of_nonneg_left (by linarith) hp0.le
    linarith
  have h1 : 1 < Real.logb p a := by
    rw [Real.lt_logb_iff_rpow_lt hp1 ha0, Real.rpow_one]; exact hpa
  have h8 : 0 < 8 * a + r := by linarith
  have h1' : 1 < Real.logb p (8 * a + r) := by
    rw [Real.lt_logb_iff_rpow_lt hp1 h8, Real.rpow_one]; linarith
  have h9 : 8 * a + r ≤ (p:ℝ) * a := by
    have : 9 * a ≤ (p:ℝ) * a := mul_le_mul_of_nonneg_right hp9 ha0.le
    linarith
  have h2' : Real.logb p (8 * a + r) ≤ 1 + Real.logb p a := by
    calc Real.logb p (8 * a + r) ≤ Real.logb p ((p:ℝ) * a) := Real.logb_le_logb_of_le hp1 h8 h9
      _ = 1 + Real.logb p a := by
        rw [Real.logb_mul hp0.ne' ha0.ne', Real.logb_self_eq_one hp1]
  have hlp : 1 ≤ Real.log p := by
    rw [Real.le_log_iff_exp_le hp0]
    have := Real.exp_one_lt_d9
    linarith
  have h5 : Real.logb p a ≤ Real.log a := by
    rw [← Real.log_div_log]
    exact div_le_self (by linarith) hlp
  unfold lgSeg
  refine ⟨h1, by linarith, by linarith, by linarith, h5, by linarith⟩

lemma geom_sum_filter_le {s : ℕ} (i : Fin s) (q : ℝ) (hq0 : 0 ≤ q) :
    (1 - q) * ∑ l ∈ univ.filter (fun l : Fin s => l ≤ i), q ^ ((i:ℕ) - (l:ℕ)) ≤ 1 ∨ 1 < q := by
  rcases lt_or_ge 1 q with hq1 | hq1
  · exact Or.inr hq1
  left
  have h1 : ∑ l ∈ univ.filter (fun l : Fin s => l ≤ i), q ^ ((i:ℕ) - (l:ℕ))
      = ∑ e ∈ (univ.filter (fun l : Fin s => l ≤ i)).image (fun l : Fin s => (i:ℕ) - (l:ℕ)), q ^ e := by
    rw [Finset.sum_image]
    intro x hx y hy hxy
    have hx' : (x:ℕ) ≤ i := (mem_filter.1 hx).2
    have hy' : (y:ℕ) ≤ i := (mem_filter.1 hy).2
    apply Fin.ext
    simp only at hxy
    omega
  have h2 : (univ.filter (fun l : Fin s => l ≤ i)).image (fun l : Fin s => (i:ℕ) - (l:ℕ)) ⊆ range ((i:ℕ)+1) := by
    intro e he
    simp only [mem_image, mem_filter, mem_univ, true_and] at he
    obtain ⟨l, hl, rfl⟩ := he
    simp only [mem_range]; omega
  have h3 : (1 - q) * ∑ e ∈ range ((i:ℕ)+1), q^e ≤ 1 := by
    rw [mul_neg_geom_sum]
    have hpow : 0 ≤ q ^ ((i:ℕ)+1) := by positivity
    linarith
  rw [h1]
  exact (mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg h2 (fun _ _ _ => by positivity))
    (by linarith)).trans h3

theorem segment_degree_sum_bound : SegDegreeSum := by
  intro p s P A C a ap b' i hp ha hap hP hPl hC hA
  have hpr : (2:ℝ) ≤ p := by exact_mod_cast hp
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = ((p:ℝ)^2)⁻¹ := ⟨_, rfl⟩
  have hp2 : (4:ℝ) ≤ (p:ℝ)^2 := by nlinarith
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  have hq4 : q ≤ 1/4 := by
    calc q = ((p:ℝ)^2)⁻¹ := hq
      _ ≤ (4:ℝ)⁻¹ := inv_anti₀ (by norm_num) hp2
      _ = 1/4 := by norm_num
  have hPi : 0 < (P i)⁻¹ := inv_pos.2 (hP i)
  have hb : 0 ≤ b' := by
    have := (le_div_iff₀ (by have := hP i; positivity : 0 < 2 * P i)).1 ((Nat.cast_nonneg (A i)).trans (hA i))
    linarith
  have hinv : ∀ l, l ≤ i → (P l)⁻¹ ≤ q ^ ((i:ℕ)-(l:ℕ)) * (P i)⁻¹ := by
    intro l hl
    rcases hl.lt_or_eq with h | h
    · have h' := hPl l h
      have e : q ^ ((i:ℕ)-(l:ℕ)) * (P i)⁻¹ = ((p:ℝ)^(2*((i:ℕ)-(l:ℕ))) * P i)⁻¹ := by
        rw [hq, inv_pow, ← pow_mul, mul_inv]
      rw [e]; exact inv_anti₀ (mul_pos (by positivity) (hP i)) h'
    · subst h; simp
  have hCs : (∑ l ∈ univ.filter (fun l => l < i), (C l:ℝ)) ≤
      2*a*(P i)⁻¹ * ∑ l ∈ univ.filter (fun l => l < i), q^((i:ℕ)-(l:ℕ)) := by
    rw [mul_sum]; apply sum_le_sum; intro l hl
    have hl' : l < i := (mem_filter.1 hl).2
    calc (C l:ℝ) ≤ ap / P l := hC l
      _ = ap * (P l)⁻¹ := div_eq_mul_inv _ _
      _ ≤ 2*a * (P l)⁻¹ := mul_le_mul_of_nonneg_right hap (inv_nonneg.2 (hP l).le)
      _ ≤ 2*a*(q^((i:ℕ)-(l:ℕ)) * (P i)⁻¹) := mul_le_mul_of_nonneg_left (hinv l hl'.le) (by linarith)
      _ = _ := by ring
  have hAs : (∑ l ∈ univ.filter (fun l => l ≤ i), (A l:ℝ)) ≤
      3/2*b'*(P i)⁻¹ * ∑ l ∈ univ.filter (fun l => l ≤ i), q^((i:ℕ)-(l:ℕ)) := by
    rw [mul_sum]; apply sum_le_sum; intro l hl
    have hl' : l ≤ i := (mem_filter.1 hl).2
    calc (A l:ℝ) ≤ 3 * b' / (2 * P l) := hA l
      _ = 3/2*b' * (P l)⁻¹ := by rw [div_eq_mul_inv, mul_inv]; ring
      _ ≤ 3/2*b'*(q^((i:ℕ)-(l:ℕ)) * (P i)⁻¹) := mul_le_mul_of_nonneg_left (hinv l hl') (by linarith)
      _ = _ := by ring
  have hins : univ.filter (fun l : Fin s => l ≤ i) = insert i (univ.filter (fun l => l < i)) := by
    ext l; simp [le_iff_eq_or_lt]
  have hsum : ∑ l ∈ univ.filter (fun l => l ≤ i), q^((i:ℕ)-(l:ℕ)) =
      1 + ∑ l ∈ univ.filter (fun l => l < i), q^((i:ℕ)-(l:ℕ)) := by
    rw [hins, sum_insert (by simp)]; simp
  have hg := (geom_sum_filter_le i q hq0).resolve_right (by linarith)
  rw [hsum] at hg hAs
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = ∑ l ∈ univ.filter (fun l => l < i), q^((i:ℕ)-(l:ℕ)) := ⟨_, rfl⟩
  rw [← hT] at hg hAs hCs
  have hT0 : 0 ≤ T := by rw [hT]; exact sum_nonneg (fun _ _ => by positivity)
  have hTq : T ≤ 4/3 * q := by nlinarith [mul_nonneg (sub_nonneg.2 hq4) hT0]
  have hT1 : 1 + T ≤ 4/3 := by linarith
  have hC2 : 2*a*(P i)⁻¹ * T ≤ 2*a*(P i)⁻¹ * (4/3*q) := mul_le_mul_of_nonneg_left hTq (by positivity)
  have hA2 : 3/2*b'*(P i)⁻¹ * (1+T) ≤ 3/2*b'*(P i)⁻¹ * (4/3) := mul_le_mul_of_nonneg_left hT1 (by positivity)
  have haq : 0 ≤ a * (P i)⁻¹ * q := by positivity
  rw [Int.le_floor]; push_cast; unfold SbdSeg
  have e : (4*a/(p:ℝ)^2+2*b')/P i = (4*a*q + 2*b')*(P i)⁻¹ := by rw [hq]; ring
  rw [e]
  nlinarith

theorem segment_window_class : SegWindowClass := by
  intro a n P sg hP hsg
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hsg
  obtain ⟨c, hc⟩ : ∃ c, c = (d + P - 1) / P := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e, e = (d + n + P - 1) / P := ⟨_, rfl⟩
  have hce : c ≤ e := by rw [hc, he]; exact Nat.div_le_div_right (by omega)
  have key : ∀ m, c ≤ m ↔ d ≤ P * m := by
    intro m
    rw [hc, ← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul hP]
    have : (m+1) * P = P * m + P := by ring
    rw [Nat.succ_eq_add_one, this]; omega
  have key2 : ∀ m, m < e ↔ P * m < d + n := by
    intro m
    rw [he, ← Nat.succ_le_iff, Nat.le_div_iff_mul_le hP]
    have : (m+1) * P = P * m + P := by ring
    rw [Nat.succ_eq_add_one, this]; omega
  have hdiv : ∀ x, sg + d ≤ x → x % P = sg % P → P * ((x - sg) / P) = x - sg := by
    intro x hx hm
    have : P ∣ x - sg := (Nat.modEq_iff_dvd' (by omega)).1 (show sg ≡ x [MOD P] from hm.symm)
    exact Nat.mul_div_cancel' this
  have himg : ((Ico (sg + d) (sg + d + n)).filter (fun x => x % P = sg % P)).image (fun x => (x - sg) / P)
      = Ico c (c + (e - c)) := by
    ext m
    simp only [mem_image, mem_filter, mem_Ico]
    constructor
    · rintro ⟨x, ⟨⟨hx1, hx2⟩, hx3⟩, rfl⟩
      have h := hdiv x hx1 hx3
      refine ⟨(key _).2 (by omega), ?_⟩
      have : (x - sg) / P < e := (key2 _).2 (by omega)
      omega
    · rintro ⟨h1, h2⟩
      have h1' := (key m).1 h1
      have h2' := (key2 m).1 (by omega)
      refine ⟨sg + P * m, ⟨⟨by omega, by omega⟩, Nat.add_mul_mod_self_left _ _ _⟩, ?_⟩
      rw [Nat.add_sub_cancel_left, Nat.mul_div_cancel_left m hP]
  refine ⟨c, e - c, himg, ?_, ?_, ?_⟩
  · rw [← Finset.card_image_of_injOn (f := fun x => (x - sg) / P), himg]
    · simp
    · intro x hx y hy hxy
      have hx' := mem_filter.1 hx
      have hy' := mem_filter.1 hy
      have hx1 := (mem_Ico.1 hx'.1).1
      have hy1 := (mem_Ico.1 hy'.1).1
      have ex := hdiv x hx1 hx'.2
      have ey := hdiv y hy1 hy'.2
      simp only at hxy
      rw [hxy] at ex
      omega
  · have h1 : d + n + P - 1 = (d + P - 1) + n := by omega
    rw [he, hc, h1, Nat.add_div hP]
    generalize (d + P - 1) / P = u
    generalize n / P = v
    split_ifs <;> omega
  · have h1 : d + n + P - 1 = (d + P - 1) + n := by omega
    rw [he, hc, h1, Nat.add_div hP]
    generalize (d + P - 1) / P = u
    generalize n / P = v
    split_ifs <;> omega

theorem segment_terms_above_bound : SegTermsAboveS := by
  intro p N N₁ r Y a b' Q La h
  obtain ⟨hY, hp, h2, hlog, h4, hba, h6, hr, hQ, hb0, hp9, hb27, hpb, hL1, hN1, hkb⟩ := segment_parameter_bounds h
  have ha0 : 0 < a := by linarith
  have hk2 : (9:ℝ) ≤ ((r:ℝ)+1)^2 := by
    calc (9:ℝ) = 3 ^ 2 := by norm_num
      _ ≤ _ := by gcongr; linarith
  have hkQ0 : 0 ≤ ((r:ℝ)+1) * Q := by positivity
  have hkQ : 9 * (((r:ℝ)+1) * Q) ≤ b' := by
    calc 9 * (((r:ℝ)+1) * Q) = 9 * (((r:ℝ)+1) * Q) * 1 := by ring
      _ ≤ ((r:ℝ)+1)^2 * (((r:ℝ)+1) * Q) * Y := by gcongr
      _ = ((r:ℝ)+1)^3 * Q * Y := by ring
      _ ≤ b' := h4
  have hp81 : (81:ℝ) ≤ (p:ℝ)^2 := by
    calc (81:ℝ) = 9 ^ 2 := by norm_num
      _ ≤ _ := by gcongr
  have h81 : 4/(p:ℝ)^2 ≤ 4/81 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp81
  have ha9 : 9 * b' < a := by
    have : 9 * b' ≤ (p:ℝ) * b' := mul_le_mul_of_nonneg_right hp9 hb0.le
    linarith
  have hz : a * (4/(p:ℝ)^2) ≤ a * (4/81) := mul_le_mul_of_nonneg_left h81 ha0.le
  have hfirst : 4 * b' + ((r : ℝ) + 1) * Q ≤ a * (1 - 4 / (p : ℝ) ^ 2) := by
    have : a * (1 - 4 / (p : ℝ) ^ 2) = a - a * (4/(p:ℝ)^2) := by ring
    rw [this]; linarith
  refine ⟨hfirst, ?_⟩
  intro P C A j hP1 hPQ hC hA hj
  have hP0 : 0 < P := by linarith
  have hfl : ((⌊SbdSeg p a b' P⌋ : ℤ) : ℝ) ≤ SbdSeg p a b' P := Int.floor_le _
  have hCP : a - ((r:ℝ)+1) * P ≤ C * P := by
    have := mul_le_mul_of_nonneg_right hC hP0.le
    have e : (a / P - ((r:ℝ)+1)) * P = a - ((r:ℝ)+1) * P := by
      rw [sub_mul, div_mul_cancel₀ _ hP0.ne']
    linarith
  have hAP : (A:ℝ) * P ≤ 3 * b' / 2 := by
    have := (le_div_iff₀ (by positivity : 0 < 2 * P)).1 hA
    linarith
  have hjA : (j:ℝ) * P ≤ A * P := by
    have : (j:ℝ) ≤ A := by exact_mod_cast hj
    exact mul_le_mul_of_nonneg_right this hP0.le
  have hkP : ((r:ℝ)+1) * P ≤ ((r:ℝ)+1) * Q := mul_le_mul_of_nonneg_left hPQ (by linarith)
  have hS : SbdSeg p a b' P ≤ (C:ℝ) - j := by
    unfold SbdSeg
    rw [div_le_iff₀ hP0]
    have e1 : a * (1 - 4 / (p : ℝ) ^ 2) = a - 4 * a / (p:ℝ)^2 := by ring
    rw [e1] at hfirst
    have e2 : ((C:ℝ) - j) * P = C * P - j * P := by ring
    rw [e2]; linarith
  have : ((⌊SbdSeg p a b' P⌋ : ℤ) : ℝ) ≤ (((C:ℤ) - (j:ℤ) : ℤ) : ℝ) := by push_cast; linarith
  exact_mod_cast this

theorem segment_no_short_window : SegNoShortWindow := by
  intro p N N₁ r a Y b' Q La h
  obtain ⟨hY, hp, h2, hlog, h4, hba, h6, hr, hQ, hb0, hp9, hb27, hpb, hL1, hN1, hkb⟩ := segment_parameter_bounds h
  obtain ⟨k, hk⟩ : ∃ k : ℝ, k = (r:ℝ) + 1 := ⟨_, rfl⟩
  rw [← hk] at h4 ⊢
  have hk3 : 3 ≤ k := by linarith
  have hkY : 0 < k * Y := by positivity
  have h1 : k^2 * Q ≤ (a:ℝ)/(k*Y) := by
    rw [le_div_iff₀ hkY]
    calc k^2*Q*(k*Y) = k^3*Q*Y := by ring
      _ ≤ b' := h4
      _ ≤ a := hba
  refine ⟨h1, ?_⟩
  intro P hP1 hPQ
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = ⌊(a:ℝ)/(k*Y)⌋₊ + 1 := ⟨_, rfl⟩
  rw [← hM]
  have hlt : (a:ℝ)/(k*Y) < M := by rw [hM]; push_cast; exact Nat.lt_floor_add_one _
  have hPM : P ≤ M := by
    have : (P:ℝ) ≤ M := by
      have h9 : (1:ℝ) ≤ k^2 := one_le_pow₀ (by linarith)
      have : 1 * Q ≤ k^2*Q := mul_le_mul_of_nonneg_right h9 (by linarith)
      linarith
    exact_mod_cast this
  refine ⟨hPM, ?_⟩
  intro Y' hY'
  have hP0 : 0 < P := hP1
  have hq1 : 1 ≤ M / P := (Nat.one_le_div_iff hP0).2 hPM
  have hlt2 : M < P * (M/P + 1) := Nat.lt_mul_div_succ M hP0
  have hle : P * (M/P + 1) ≤ P * (2 * Y') := Nat.mul_le_mul_left _ (by omega)
  have hMr : (M:ℝ) ≤ P * (2 * Y') := by exact_mod_cast (hlt2.le.trans hle)
  refine ⟨by omega, ?_⟩
  have hPr : (0:ℝ) < P := by exact_mod_cast hP0
  rw [div_le_iff₀ (by positivity)]
  have ha := (div_lt_iff₀ hkY).1 hlt
  have := mul_le_mul_of_nonneg_right hMr hkY.le
  calc (a:ℝ) ≤ M * (k*Y) := ha.le
    _ ≤ P * (2 * Y') * (k*Y) := this
    _ = Y' * (2 * k * Y * P) := by ring

theorem segment_short_window_free : SegShortWindowNoTie := by
  intro p k Y a b' P hY hk hp hb0 h2 hL haP
  have hkr : (2:ℝ) ≤ k := by exact_mod_cast hk
  have hY0 : 0 < Y := by linarith
  have hL0 : 0 < Real.log a := by linarith
  have hk0 : (0:ℝ) < k := by linarith
  have ha0 : 0 < a := by
    by_contra hneg
    have hneg := not_lt.1 hneg
    have h1 : a / b' ≤ 0 := div_nonpos_of_nonpos_of_nonneg hneg hb0.le
    have h3 : 0 < (k:ℝ)*Y^2*Real.log a := by positivity
    linarith
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = (k:ℝ) * Y := ⟨_, rfl⟩
  have hw2 : 2 ≤ w := by
    rw [hw]
    calc (2:ℝ) = 2 * 1 := by norm_num
      _ ≤ (k:ℝ) * Y := by gcongr
  have hw0 : 0 < w := by linarith
  rw [← hw] at haP
  have hP0 : 0 < P := lt_trans (div_pos ha0 hw0) haP
  have hpw : w^2 ≤ (p:ℝ) := by rw [hw, mul_pow]; exact hp
  have hp2 : 8 * w ≤ (p:ℝ)^2 := by
    have h8 : (8:ℝ) ≤ w^3 := by
      calc (8:ℝ) = 2^3 := by norm_num
        _ ≤ w^3 := by gcongr
    calc 8 * w ≤ w^3 * w := by gcongr
      _ = (w^2)^2 := by ring
      _ ≤ (p:ℝ)^2 := by gcongr
  have hp20 : 0 < (p:ℝ)^2 := by linarith
  have hA : 4 * a / (p:ℝ)^2 ≤ a / (2*w) := by
    rw [div_le_div_iff₀ hp20 (by positivity)]
    have := mul_le_mul_of_nonneg_left hp2 ha0.le
    linarith
  have hB : 2 * b' < a / (2*w) := by
    rw [lt_div_iff₀ (by positivity)]
    have h3 := (le_div_iff₀ hb0).1 h2
    have h4 : (k:ℝ) * Y * b' ≤ (k:ℝ) * Y^2 * b' := by
      have : Y ≤ Y^2 := le_self_pow₀ hY (by norm_num)
      gcongr
    have h5 : (k:ℝ) * Y^2 * b' * 4 < (k:ℝ) * Y^2 * b' * Real.log a :=
      mul_lt_mul_of_pos_left hL (by positivity)
    rw [hw]
    nlinarith
  have hsum : a / (2*w) + a / (2*w) = a / w := by field_simp; ring
  rw [Int.floor_eq_zero_iff]; unfold SbdSeg
  refine ⟨by positivity, ?_⟩
  rw [div_lt_one hP0]
  linarith

lemma segment_ratio_le {k Y L a b' : ℝ} (_hk : 0 < k) (hY : 0 < Y) (hL : 0 < L) (ha : 0 < a) (hb : 0 < b')
    (h2 : k*Y^2*L ≤ a/b') : k * Y * b' / a ≤ 1 / (Y * L) := by
  rw [div_le_div_iff₀ ha (by positivity)]
  have := (le_div_iff₀ hb).1 h2
  calc k*Y*b'*(Y*L) = k*Y^2*L*b' := by ring
    _ ≤ a := this
    _ = 1*a := by ring

lemma segment_ratio_le_prime {k Y p : ℝ} (hk : 0 < k) (hY : 0 < Y) (hp : k^2*Y^2 ≤ p) :
    k*Y/p^2 ≤ 1/(k^3*Y^3) := by
  have hp0 : 0 < p := lt_of_lt_of_le (by positivity) hp
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  calc k*Y*(k^3*Y^3) = (k^2*Y^2)^2 := by ring
    _ ≤ p^2 := by gcongr
    _ = 1*p^2 := by ring

lemma segment_sum_ratio_le {k Y L a b' p P S Y' : ℝ} (hk : 0 < k) (hY : 0 < Y) (hL : 0 < L) (ha : 0 < a) (hb : 0 < b')
    (hp : k^2*Y^2 ≤ p) (h2 : k*Y^2*L ≤ a/b') (hP : 0 < P) (hS0 : 0 ≤ S)
    (hS : S ≤ (4*a/p^2+2*b')/P) (hY' : a/(2*k*Y*P) ≤ Y') :
    S / Y' ≤ 8/(k^3*Y^3) + 4/(Y*L) := by
  have hp0 : 0 < p := lt_of_lt_of_le (by positivity) hp
  have hw : 0 < a/(2*k*Y*P) := by positivity
  calc S / Y' ≤ S / (a/(2*k*Y*P)) := div_le_div_of_nonneg_left hS0 hw hY'
    _ ≤ ((4*a/p^2+2*b')/P) / (a/(2*k*Y*P)) := div_le_div_of_nonneg_right hS hw.le
    _ = 8 * (k*Y/p^2) + 4*(k*Y*b'/a) := by field_simp; ring
    _ ≤ 8*(1/(k^3*Y^3)) + 4*(1/(Y*L)) := by
        have h1 := segment_ratio_le_prime hk hY hp
        have h3 := segment_ratio_le hk hY hL ha hb h2
        linarith
    _ = _ := by ring

lemma forty_eight_le_kappa {p r s : ℕ} {a : ℝ} (hr : (2:ℝ) ≤ r) (hlg : 2 < lgSeg p a r) : 48 ≤ kapSeg p a r s := by
  unfold kapSeg
  have hs2 : (2:ℝ) ≤ (s:ℝ)+2 := by have := Nat.cast_nonneg (α:=ℝ) s; linarith
  have hlg' := hlg.le
  calc (48:ℝ) = 3*2*2^2*2 := by norm_num
    _ ≤ 3 * ((s : ℝ) + 2) * (r : ℝ) ^ 2 * lgSeg p a r := by gcongr

lemma first_depth_bounds {t : ℕ} {Y κ : ℝ} (hY : 1 ≤ Y) (hκ : 0 ≤ κ) :
    firstDepth t Y κ ≤ 2 * ((t : ℝ) + 1) * Y * κ ∧ κ ≤ firstDepth t Y κ := by
  unfold firstDepth
  have ht : (0:ℝ) ≤ t := Nat.cast_nonneg _
  have h1 : 0 ≤ (t:ℝ) * κ * (Y - 1) := mul_nonneg (mul_nonneg ht hκ) (by linarith)
  have h2 : 0 ≤ κ * (Y - 1) := mul_nonneg hκ (by linarith)
  have h3 : 0 ≤ (t:ℝ) * (Y * κ + κ) := by positivity
  have h4 : 0 ≤ κ * Y := by positivity
  constructor
  · nlinarith
  · linarith

theorem segment_epsilon_bound : SegEps := by
  intro p N N₁ r s Y a b' Q La P S Y' h hP hS0 hS hY'
  obtain ⟨hl1, hl2, hl3, hl4, hl5, hl6⟩ := segment_log_bound p N N₁ r Y a b' Q La h
  obtain ⟨hY, hp, h2, hlog, h4, hba, h6, hr, hQ, hb0, hp9, hb27, hpb, hL1, hN1, hkb⟩ := segment_parameter_bounds h
  have hκ := forty_eight_le_kappa (s := s) hr hl2
  obtain ⟨k, hk⟩ : ∃ k : ℝ, k = (r:ℝ) + 1 := ⟨_, rfl⟩
  obtain ⟨lg, hlg⟩ : ∃ x : ℝ, x = lgSeg p a r := ⟨_, rfl⟩
  obtain ⟨L, hLd⟩ : ∃ x : ℝ, x = Real.log a := ⟨_, rfl⟩
  obtain ⟨κ, hκd⟩ : ∃ x : ℝ, x = kapSeg p a r s := ⟨_, rfl⟩
  rw [← hk] at hp h2 hl6 hY'
  rw [← hlg] at hl2 hl4 hl6 ⊢
  rw [← hLd] at h2 hL1 hl5
  rw [← hκd] at hκ ⊢
  unfold SbdSeg at hS
  have hk3 : 3 ≤ k := by linarith
  have hk0 : 0 < k := by linarith
  have hY0 : 0 < Y := by linarith
  have hL0 : 0 < L := by linarith
  have ha0 : 0 < a := by linarith
  have hlgL : lg ≤ 4 * L := by linarith
  have hlg0 : 0 ≤ lg := by linarith
  have hu := segment_sum_ratio_le hk0 hY0 hL0 ha0 hb0 hp h2 hP hS0 hS hY'
  have hY'0 : 0 < Y' := lt_of_lt_of_le (by positivity) hY'
  obtain ⟨u, hud⟩ : ∃ x : ℝ, x = S / Y' := ⟨_, rfl⟩
  rw [← hud] at hu
  have hu0 : 0 ≤ u := by rw [hud]; positivity
  have hY3 : Y ≤ Y^3 := le_self_pow₀ hY (by norm_num)
  have hk21 : 1 ≤ k^2 := one_le_pow₀ (by linarith)
  have hk31 : 1 ≤ k^3 := one_le_pow₀ (by linarith)
  have hYk3 : Y ≤ k^3*Y^3 := by
    calc Y = 1 * Y := by ring
      _ ≤ k^3*Y^3 := mul_le_mul hk31 hY3 hY0.le (by positivity)
  have hYk2 : Y ≤ k^2*Y^3 := by
    calc Y = 1 * Y := by ring
      _ ≤ k^2*Y^3 := mul_le_mul hk21 hY3 hY0.le (by positivity)
  have hYL : Y ≤ Y * L := le_mul_of_one_le_right hY0.le hL1
  have hα : 8/(k^3*Y^3) ≤ 8/Y := div_le_div_of_nonneg_left (by norm_num) hY0 hYk3
  have hβ : 4/(Y*L) ≤ 4/Y := div_le_div_of_nonneg_left (by norm_num) hY0 hYL
  have e12 : 8/Y + 4/Y = 12/Y := by ring
  have c1 : u ≤ 12 / Y := by linarith
  have hα2 : 8/(k^3*Y^3) * lg ≤ 32 / Y := by
    calc 8/(k^3*Y^3) * lg ≤ 8/(k^3*Y^3) * (4*k) := mul_le_mul_of_nonneg_left hl6 (by positivity)
      _ = 32/(k^2*Y^3) := by field_simp; ring
      _ ≤ 32 / Y := div_le_div_of_nonneg_left (by norm_num) hY0 hYk2
  have hβ2 : 4/(Y*L) * lg ≤ 16 / Y := by
    calc 4/(Y*L) * lg ≤ 4/(Y*L) * (4*L) := mul_le_mul_of_nonneg_left hlgL (by positivity)
      _ = 16 / Y := by field_simp; ring
  have e48 : 32/Y + 16/Y = 48/Y := by ring
  have c2 : u * lg ≤ 48 / Y := by
    have := mul_le_mul_of_nonneg_right hu hlg0
    rw [add_mul] at this
    linarith
  have eS : S * lg / Y' = u * lg := by rw [hud]; ring
  refine ⟨by rw [← hud]; exact c1, by rw [eS]; exact c2, hκ, ?_⟩
  unfold epsSeg
  have e1 : 2 * S / Y' = 2 * u := by rw [hud]; ring
  have e2 : 2 * S * lg / Y' = 2 * (u * lg) := by rw [hud]; ring
  rw [e1, e2]
  have h48 : 48 / Y ≤ 48 := div_le_self (by norm_num) hY
  have hκ0 : 0 < κ := by linarith
  have c3 : (2 * κ + 2 * (u * lg)) / (Y * κ) ≤ 4 / Y := by
    calc (2 * κ + 2 * (u * lg)) / (Y * κ) ≤ (4 * κ) / (Y * κ) :=
          div_le_div_of_nonneg_right (by linarith) (by positivity)
      _ = 4 / Y := by field_simp
  have e28 : 2 * (12 / Y) + 4 / Y = 28 / Y := by ring
  linarith

theorem segment_epsilon_plus : SegEpsPlus := by
  intro p N N₁ r s t Y a b' Q La J Yp h hts hJ0 hJ hYp
  obtain ⟨hl1, hl2, hl3, hl4, hl5, hl6⟩ := segment_log_bound p N N₁ r Y a b' Q La h
  obtain ⟨hY, hp, h2, hlog, h4, hba, h6, hr, hQ, hb0, hp9, hb27, hpb, hL1, hN1, hkb⟩ := segment_parameter_bounds h
  have hκ := forty_eight_le_kappa (s := s) hr hl2
  obtain ⟨hD1, hD2⟩ := first_depth_bounds (t := t) hY (by linarith : 0 ≤ kapSeg p a r s)
  have hx0 : initialExponent p a r s t + lgSeg p a r ≤ kapSeg p a r s - 1 := by
    unfold initialExponent kapSeg
    obtain ⟨lg, hlg⟩ : ∃ x : ℝ, x = lgSeg p a r := ⟨_, rfl⟩
    rw [← hlg] at hl2 ⊢
    have hs0 : (0:ℝ) ≤ s := Nat.cast_nonneg _
    have htr : (t:ℝ) ≤ s := by exact_mod_cast hts
    have h1 : (t:ℝ)*((r:ℝ)+1) ≤ (s:ℝ)*((r:ℝ)+1) := mul_le_mul_of_nonneg_right htr (by linarith)
    have h2' : 2*(r:ℝ) ≤ (r:ℝ)^2 := by nlinarith
    have h3 : ((s:ℝ)+2)*(2*(r:ℝ)) ≤ ((s:ℝ)+2)*(r:ℝ)^2 := mul_le_mul_of_nonneg_left h2' (by linarith)
    have h4' : 0 ≤ (s:ℝ)*(r:ℝ) := by positivity
    have hc : 1 ≤ 3*((s:ℝ)+2)*(r:ℝ)^2 - ((r:ℝ) + (t:ℝ)*((r:ℝ)+1) + (2*(s:ℝ)+2)*((r:ℝ)-1) + 1) := by
      nlinarith
    have hm : (1:ℝ) * 1 ≤ (3*((s:ℝ)+2)*(r:ℝ)^2 - ((r:ℝ) + (t:ℝ)*((r:ℝ)+1) + (2*(s:ℝ)+2)*((r:ℝ)-1) + 1)) * lg :=
      mul_le_mul hc (by linarith) zero_le_one (by linarith)
    linarith
  have hceil : ((⌈initialExponent p a r s t⌉ : ℤ) : ℝ) + lgSeg p a r ≤ kapSeg p a r s := by
    have := Int.ceil_lt_add_one (initialExponent p a r s t)
    linarith
  obtain ⟨X, hX⟩ : ∃ x : ℝ, x = ((⌈initialExponent p a r s t⌉ : ℤ) : ℝ) := ⟨_, rfl⟩
  obtain ⟨k, hk⟩ : ∃ k : ℝ, k = (r:ℝ) + 1 := ⟨_, rfl⟩
  obtain ⟨lg, hlg⟩ : ∃ x : ℝ, x = lgSeg p a r := ⟨_, rfl⟩
  obtain ⟨L, hLd⟩ : ∃ x : ℝ, x = Real.log a := ⟨_, rfl⟩
  obtain ⟨κ, hκd⟩ : ∃ x : ℝ, x = kapSeg p a r s := ⟨_, rfl⟩
  rw [← hk] at hp h2 hl6 hYp
  rw [← hX] at hceil ⊢
  rw [← hlg] at hl2 hl4 hl6 hx0 hceil ⊢
  rw [← hLd] at h2 hL1 hl5 ⊢
  rw [← hκd] at hκ hD1 hD2 hx0 hceil ⊢
  obtain ⟨D, hDd⟩ : ∃ x : ℝ, x = firstDepth t Y κ := ⟨_, rfl⟩
  rw [← hDd] at hD1 hD2 ⊢
  have hk0 : 0 < k := by linarith
  have hY0 : 0 < Y := by linarith
  have hL0 : 0 < L := by linarith
  have ha0 : 0 < a := by linarith
  have hlgL : lg ≤ 4 * L := by linarith
  have hlg0 : 0 ≤ lg := by linarith
  have hw : 0 < a / (k * Y) := by positivity
  have hv : J / Yp ≤ 3/2 * (1 / (Y * L)) := by
    calc J / Yp ≤ J / (a / (k*Y)) := div_le_div_of_nonneg_left hJ0 hw hYp
      _ ≤ (3 * b' / 2) / (a / (k*Y)) := div_le_div_of_nonneg_right hJ hw.le
      _ = 3/2 * (k * Y * b' / a) := by field_simp
      _ ≤ 3/2 * (1 / (Y * L)) := mul_le_mul_of_nonneg_left (segment_ratio_le hk0 hY0 hL0 ha0 hb0 h2) (by norm_num)
  have hYL0 : 0 < 1 / (Y * L) := by positivity
  have c2 : J / Yp ≤ 2 / (Y * L) := by
    have : 2 / (Y * L) = 2 * (1 / (Y * L)) := by ring
    rw [this]; linarith
  have c3 : J * lg / Yp ≤ 8 / Y := by
    have e : J * lg / Yp = J / Yp * lg := by ring
    rw [e]
    calc J / Yp * lg ≤ 3/2 * (1 / (Y * L)) * lg := mul_le_mul_of_nonneg_right hv hlg0
      _ ≤ 3/2 * (1 / (Y * L)) * (4 * L) := mul_le_mul_of_nonneg_left hlgL (by positivity)
      _ = 6 / Y := by field_simp; ring
      _ ≤ 8 / Y := div_le_div_of_nonneg_right (by norm_num) hY0.le
  refine ⟨hD1, c2, c3, hx0, hceil, ?_⟩
  unfold epsPlusSeg
  have hD0 : 0 < D := by linarith
  have hE : Y * D < ((⌊Y * D⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  have hYD : 0 < Y * D := by positivity
  have h8 : 8 / Y ≤ 8 := div_le_self (by norm_num) hY
  have c4 : (X + D + lg + J * lg / Yp) / (((⌊Y * D⌋ : ℤ) : ℝ) + 1) ≤ 3 / Y := by
    calc (X + D + lg + J * lg / Yp) / (((⌊Y * D⌋ : ℤ) : ℝ) + 1)
        ≤ (3 * D) / (((⌊Y * D⌋ : ℤ) : ℝ) + 1) := div_le_div_of_nonneg_right (by linarith) (by linarith)
      _ ≤ (3 * D) / (Y * D) := div_le_div_of_nonneg_left (by linarith) hYD hE.le
      _ = 3 / Y := by field_simp
  have c5 : 2 / (Y * L) ≤ 2 / Y :=
    div_le_div_of_nonneg_left (by norm_num) hY0 (le_mul_of_one_le_right hY0.le hL1)
  have e5 : 2 / Y + 3 / Y = 5 / Y := by ring
  linarith

theorem segment_depth_bound : SegDepth := by
  intro p N N₁ r s t Y a b' Q La h hts hsN
  obtain ⟨hl1, hl2, hl3, hl4, hl5, hl6⟩ := segment_log_bound p N N₁ r Y a b' Q La h
  obtain ⟨hY, hp, h2, hlog, h4, hba, h6, hr, hQ, hb0, hp9, hb27, hpb, hL1, hN1, hkb⟩ := segment_parameter_bounds h
  have hκ := forty_eight_le_kappa (s := s) hr hl2
  obtain ⟨hD1, hD2⟩ := first_depth_bounds (t := t) hY (by linarith : 0 ≤ kapSeg p a r s)
  have hs0 : (0:ℝ) ≤ s := Nat.cast_nonneg _
  have ht0 : (0:ℝ) ≤ t := Nat.cast_nonneg _
  have htr : (t:ℝ) ≤ s := by exact_mod_cast hts
  have hsr : (s:ℝ) ≤ N₁ := by exact_mod_cast hsN
  have hlg0 : 0 ≤ lgSeg p a r := by linarith
  have hY0 : 0 < Y := by linarith
  have c1 : kapSeg p a r s ≤ 9 * N₁ * ((r : ℝ) + 1) ^ 2 * lgSeg p a r := by
    unfold kapSeg
    have hs3 : (s:ℝ) + 2 ≤ 3 * N₁ := by linarith
    have hrk : (r:ℝ) ≤ (r:ℝ) + 1 := by linarith
    calc 3 * ((s : ℝ) + 2) * (r : ℝ) ^ 2 * lgSeg p a r
        ≤ 3 * (3 * N₁) * ((r : ℝ) + 1) ^ 2 * lgSeg p a r := by gcongr
      _ = _ := by ring
  have c3 : 3 * ((s : ℝ) + 1) * lgSeg p a r + 2 * uSeg p a r t ≤ kapSeg p a r s := by
    unfold uSeg kapSeg
    have h1 : ((t:ℝ)+1)*((r:ℝ)+1) ≤ ((s:ℝ)+1)*((r:ℝ)+1) := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    have h2' : 2*(r:ℝ) + 5 ≤ 3 * (r:ℝ)^2 := by nlinarith
    have h3 : ((s:ℝ)+1)*(2*(r:ℝ)+5) ≤ ((s:ℝ)+1)*(3*(r:ℝ)^2) := mul_le_mul_of_nonneg_left h2' (by linarith)
    have h5 : 0 ≤ (r:ℝ)^2 := by positivity
    have hc : 0 ≤ 3*((s:ℝ)+2)*(r:ℝ)^2 - (3*((s:ℝ)+1) + 2*(((t:ℝ)+1)*((r:ℝ)+1))) := by nlinarith
    have hm := mul_nonneg hc hlg0
    linarith
  have c2 : Y * firstDepth t Y (kapSeg p a r s) ≤ 36 * Y ^ 2 * (N₁ : ℝ) ^ 2 * ((r : ℝ) + 1) ^ 2 * lgSeg p a r := by
    have ht2 : (t:ℝ) + 1 ≤ 2 * N₁ := by linarith
    calc Y * firstDepth t Y (kapSeg p a r s) ≤ Y * (2 * ((t : ℝ) + 1) * Y * kapSeg p a r s) :=
          mul_le_mul_of_nonneg_left hD1 hY0.le
      _ ≤ Y * (2 * (2 * N₁) * Y * (9 * N₁ * ((r : ℝ) + 1) ^ 2 * lgSeg p a r)) := by gcongr
      _ = _ := by ring
  refine ⟨c1, c2, c3, ?_⟩
  unfold DjSeg
  have hfl : ((⌊Y * firstDepth t Y (kapSeg p a r s)⌋ : ℤ) : ℝ) ≤ Y * firstDepth t Y (kapSeg p a r s) := Int.floor_le _
  have hY2 : 1 ≤ Y ^ 2 := one_le_pow₀ hY
  have hN2 : (N₁:ℝ) ≤ (N₁:ℝ)^2 := le_self_pow₀ hN1 (by norm_num)
  have c4 : 9 * N₁ * ((r : ℝ) + 1) ^ 2 * lgSeg p a r ≤ 9 * Y ^ 2 * (N₁ : ℝ) ^ 2 * ((r : ℝ) + 1) ^ 2 * lgSeg p a r := by
    calc 9 * N₁ * ((r : ℝ) + 1) ^ 2 * lgSeg p a r = 9 * 1 * N₁ * ((r : ℝ) + 1) ^ 2 * lgSeg p a r := by ring
      _ ≤ _ := by gcongr
  linarith

end Formalism.CountingSumsFrames
