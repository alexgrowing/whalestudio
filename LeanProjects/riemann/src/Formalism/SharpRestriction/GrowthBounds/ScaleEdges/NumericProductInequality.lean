import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.ManyEdges

noncomputable section

namespace Formalism.MainNotions.Pf14

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility

theorem numeric_product_inequality (A B u : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hu1 : u ≤ 1) (hu : 1 - B ≤ u) :
    1 - A - B ≤ (1 - A) * u := by
  rcases le_or_gt A 1 with h | h
  · have h1 : (1 - A) * (1 - B) ≤ (1 - A) * u := mul_le_mul_of_nonneg_left hu (by linarith)
    have h2 := mul_nonneg hA hB
    linarith
  · have h1 : (A - 1) * u ≤ (A - 1) * 1 := mul_le_mul_of_nonneg_left hu1 (by linarith)
    linarith

theorem num_size (C k r N Q cS c0 z Y a : ℝ) (hC : 2 ≤ C) (hk : 1 ≤ k) (hr : 2 ≤ r) (hN : 1 ≤ N) (hQ : 1 ≤ Q)
    (hcS : 8 ≤ cS) (hc0 : 0 ≤ c0) (hz : 0 ≤ z) (hY : 2 ≤ Y)
    (hsz : C * k ^ 3 * r ^ 2 * N * Q ^ 5 * (cS + (r * N * c0 + z)) * Y ≤ a) :
    1 ≤ a ∧ N * k * c0 * Y ≤ a := by
  have hk3 : k ≤ k ^ 3 := le_self_pow₀ hk (by norm_num)
  have hr21 : (1 : ℝ) ≤ r ^ 2 := one_le_pow₀ (by linarith)
  have hQ5 : (1 : ℝ) ≤ Q ^ 5 := one_le_pow₀ hQ
  have hk0 : 0 ≤ k := by linarith
  have hN0 : 0 ≤ N := by linarith
  have e1 : k ≤ C * k ^ 3 := le_trans hk3 (le_mul_of_one_le_left (by positivity) (by linarith))
  have e2 : k ≤ C * k ^ 3 * r ^ 2 := le_trans e1 (le_mul_of_one_le_right (by positivity) hr21)
  have e3 : k * N ≤ C * k ^ 3 * r ^ 2 * N := mul_le_mul_of_nonneg_right e2 hN0
  have hP : k * N ≤ C * k ^ 3 * r ^ 2 * N * Q ^ 5 := le_trans e3 (le_mul_of_one_le_right (by positivity) hQ5)
  have hkN : 1 ≤ k * N := one_le_mul_of_one_le_of_one_le hk hN
  have hrN : 1 ≤ r * N := one_le_mul_of_one_le_of_one_le (by linarith) hN
  have hom : c0 ≤ r * N * c0 + z := by
    have : c0 ≤ r * N * c0 := le_mul_of_one_le_left hc0 hrN
    linarith
  have hS : 0 ≤ cS + (r * N * c0 + z) := by linarith
  have ha0 : k * N * (cS + (r * N * c0 + z)) * Y ≤ a :=
    le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hP hS) (by linarith)) hsz
  constructor
  · have e4 : 1 ≤ k * N * (cS + (r * N * c0 + z)) := one_le_mul_of_one_le_of_one_le hkN (by linarith)
    have e5 : 1 ≤ k * N * (cS + (r * N * c0 + z)) * Y := one_le_mul_of_one_le_of_one_le e4 (by linarith)
    linarith
  · refine le_trans ?_ ha0
    have e6 : k * N * c0 ≤ k * N * (cS + (r * N * c0 + z)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have e7 := mul_le_mul_of_nonneg_right e6 (show (0 : ℝ) ≤ Y by linarith)
    calc N * k * c0 * Y = k * N * c0 * Y := by ring
      _ ≤ _ := e7

theorem level_bound_numeric (C Ct0 r N X c0 z : ℝ) (hC2 : 2 ≤ C) (hC3 : Ct0 ≤ C) (hr : 2 ≤ r) (hN : 0 ≤ N) (hX : 0 ≤ X)
    (hc0 : 0 ≤ c0) : Ct0 * N * X + N * c0 + (r * N * c0 + z) ≤ C * r * N * (X + c0) + z := by
  have hCr : Ct0 ≤ C * r := le_trans hC3 (le_mul_of_one_le_right (by linarith) (by linarith))
  have hCr2 : r + 1 ≤ C * r := by
    have : 2 * r ≤ C * r := mul_le_mul_of_nonneg_right hC2 (by linarith)
    linarith
  have e1 : Ct0 * N * X ≤ C * r * N * X :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCr hN) hX
  have e2 : (r + 1) * (N * c0) ≤ C * r * (N * c0) := mul_le_mul_of_nonneg_right hCr2 (mul_nonneg hN hc0)
  have e3 : C * r * N * (X + c0) = C * r * N * X + C * r * (N * c0) := by ring
  have e4 : (r + 1) * (N * c0) = r * N * c0 + N * c0 := by ring
  rw [e3]
  linarith

theorem num_count (C Cr r k Y a c0 : ℝ) (n : ℕ) (hCr : 0 < Cr) (hC5 : Cr + 1 ≤ C) (hr : 2 ≤ r) (hk : 1 ≤ k)
    (hn : 1 ≤ (n : ℝ)) (hY : 2 ≤ Y) (hc0 : 0 ≤ c0) (ha : 1 ≤ a) (ha2 : (n : ℝ) * k * c0 * Y ≤ a) :
    1 - C * n * r ^ 2 * k / Y ≤ (1 - Cr * n * r ^ 2 * k / Y) * (1 - k * c0 / a) ^ n := by
  have hYpos : 0 < Y := by linarith
  have hapos : 0 < a := by linarith
  have hk0 : 0 ≤ k := by linarith
  have hB0 : 0 ≤ (n : ℝ) * r ^ 2 * k / Y := by positivity
  have hB1 : 1 / Y ≤ (n : ℝ) * r ^ 2 * k / Y := by
    apply div_le_div_of_nonneg_right _ hYpos.le
    have hr21 : (1 : ℝ) ≤ r ^ 2 := one_le_pow₀ (by linarith)
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hn hr21) hk
  have hy0 : 0 ≤ k * c0 / a := by positivity
  have hNy : (n : ℝ) * (k * c0 / a) ≤ 1 / Y := by
    rw [le_div_iff₀ hYpos]
    have : (n : ℝ) * (k * c0 / a) * Y = ((n : ℝ) * k * c0 * Y) / a := by ring
    rw [this, div_le_one hapos]
    exact ha2
  have hy1 : k * c0 / a ≤ 1 := by
    have e1 : k * c0 / a ≤ (n : ℝ) * (k * c0 / a) := le_mul_of_one_le_left hy0 hn
    have e2 : 1 / Y ≤ 1 := by
      rw [div_le_one hYpos]; linarith
    linarith
  have hu1 : (1 - k * c0 / a) ^ n ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have hu : 1 - (n : ℝ) * r ^ 2 * k / Y ≤ (1 - k * c0 / a) ^ n := by
    have hb := one_add_mul_le_pow (a := -(k * c0 / a)) (by linarith) n
    have e2 : (1 : ℝ) + -(k * c0 / a) = 1 - k * c0 / a := by ring
    rw [e2] at hb
    linarith
  have hAeq : Cr * n * r ^ 2 * k / Y = Cr * ((n : ℝ) * r ^ 2 * k / Y) := by ring
  have hCeq : C * n * r ^ 2 * k / Y = C * ((n : ℝ) * r ^ 2 * k / Y) := by ring
  rw [hAeq, hCeq]
  have h3 := numeric_product_inequality (Cr * ((n : ℝ) * r ^ 2 * k / Y)) ((n : ℝ) * r ^ 2 * k / Y) ((1 - k * c0 / a) ^ n)
    (mul_nonneg hCr.le hB0) hB0 hu1 hu
  have h4 : (Cr + 1) * ((n : ℝ) * r ^ 2 * k / Y) ≤ C * ((n : ℝ) * r ^ 2 * k / Y) :=
    mul_le_mul_of_nonneg_right hC5 hB0
  linarith

theorem num : Num := by
  intro C Ct0 CD1 Cr h0 h1 h2 hC2 hC3 hC4 hC5 p n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hH
  obtain ⟨hp, hr, _, hN1, _, hY, _, hk, _, hD, hc, hsz⟩ := hH
  have hN1pos : 1 ≤ orbitWindowCount r de h x := by unfold orbitWindowCount; omega
  have hNnat : 1 ≤ TT.card := by
    rcases Nat.eq_zero_or_pos TT.card with h0' | h0'
    · rw [h0', Nat.mul_zero] at hN1
      have : 0 < orbitWindowCount r de h x ^ 2 := by positivity
      omega
    · exact h0'
  have hN : (1 : ℝ) ≤ (TT.card : ℝ) := by exact_mod_cast hNnat
  have hk1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
    have : 1 ≤ m + 1 := by omega
    exact_mod_cast this
  have hr2 : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hp1 : (1 : ℝ) < p := by
    have : 1 < p := by omega
    exact_mod_cast this
  have hp0 : (0 : ℝ) < p := by linarith
  have hQ : (1 : ℝ) ≤ (p : ℝ) ^ goodG' r de h x := one_le_pow₀ hp1.le
  have hY2 : (2 : ℝ) ≤ Y := le_trans hr2 hY
  have hc0 : (0 : ℝ) ≤ c0 := Nat.cast_nonneg _
  have hz : (0 : ℝ) ≤ 2 * (r : ℝ) * n' * cpp := by positivity
  have hcS : (8 : ℝ) ≤ cStar := by
    have : 8 ≤ cStar := by omega
    exact_mod_cast this
  obtain ⟨ha1, ha2⟩ := num_size C _ _ _ _ _ _ _ Y a hC2 hk1 hr2 hN hQ hcS hc0 hz hY2 hsz
  have hapos : 0 < a := by linarith
  have hlog : 0 ≤ Real.log a := Real.log_nonneg ha1
  have hlogb : 0 ≤ Real.logb p a := Real.logb_nonneg hp1 ha1
  refine ⟨?_, mul_nonneg (by linarith) hc0, ?_, ?_⟩
  · unfold t0 om tableLineDegreeFive.tBound
    have hLa : 0 ≤ tableLineDegreeFive.La C (orbitWindowCount r de h x) a := by
      unfold tableLineDegreeFive.La
      have : 0 ≤ C := by linarith
      positivity
    have hX0 : 0 ≤ tableLineDegreeFive.La C (orbitWindowCount r de h x) a * a / ((p : ℝ) * ((m + 1 : ℕ) : ℝ)) + a * (p : ℝ) ^ (-(L₁ : ℤ)) +
        ((m + 1 : ℕ) : ℝ) * (p : ℝ) ^ goodG' r de h x := by
      have e1 : 0 ≤ tableLineDegreeFive.La C (orbitWindowCount r de h x) a * a / ((p : ℝ) * ((m + 1 : ℕ) : ℝ)) := by positivity
      have e2 : 0 ≤ a * (p : ℝ) ^ (-(L₁ : ℤ)) := by positivity
      have e3 : 0 ≤ ((m + 1 : ℕ) : ℝ) * (p : ℝ) ^ goodG' r de h x := by positivity
      linarith
    have key := level_bound_numeric C Ct0 r TT.card _ c0 (2 * (r : ℝ) * n' * cpp) hC2 hC3 hr2 (by linarith) hX0 hc0
    refine le_trans key (le_of_eq ?_)
    ring
  · refine le_trans ?_ hD
    have e1 : CD1 * (TT.card : ℝ) ≤ C * (TT.card : ℝ) := mul_le_mul_of_nonneg_right hC4 (by linarith)
    have e2 : CD1 * (TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 ≤ C * (TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right e1 (by positivity)
    exact mul_le_mul_of_nonneg_right e2 hlogb
  · exact num_count C Cr r _ Y a c0 TT.card h2 hC5 hr2 hk1 hN hY2 hc0 ha1 ha2

end Formalism.MainNotions.Pf14
