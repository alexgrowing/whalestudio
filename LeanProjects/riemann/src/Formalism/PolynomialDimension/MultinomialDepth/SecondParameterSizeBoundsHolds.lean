import Formalism.PolynomialDimension.StatementNum

noncomputable section

namespace Formalism.CountingSumsFrames

open Real

lemma pII0_one_le_mul {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b := by
  nlinarith

lemma pII0_basic (r N N₁ k : ℝ) (hr : 2 ≤ r) (hrN1 : r ≤ N₁) (hN1 : N₁ ^ 2 ≤ r * N)
    (hk : N₁ + 3 * r ≤ k) : r ≤ N ∧ 8 ≤ k ∧ N₁ + 1 ≤ 2 * r * N := by
  have h1 : r * r ≤ r * N := by nlinarith
  have hrN : r ≤ N := le_of_mul_le_mul_left h1 (by linarith)
  refine ⟨hrN, by linarith, ?_⟩
  nlinarith

lemma sizeBound_frame_le (r N N₁ Nₛ k : ℝ) (hr : 2 ≤ r) (hrN1 : r ≤ N₁) (hN1 : N₁ ^ 2 ≤ r * N)
    (hk8 : 8 ≤ k) (hN0 : 0 ≤ N) (hNs1 : Nₛ ≤ N₁) (hNs2 : Nₛ ≤ 2 * N) :
    Nₛ * (N₁ + r * k) ≤ 2 * r ^ 2 * N * k := by
  have hpos : 0 ≤ N₁ + r * k := by nlinarith
  have hrk : 0 ≤ r * N * k := by positivity
  rcases le_or_gt 0 Nₛ with hs | hs
  · have e1 : Nₛ * N₁ ≤ N₁ ^ 2 := by nlinarith
    have e2 : r * N ≤ r ^ 2 * N * k := by nlinarith
    have e3 : Nₛ * (r * k) ≤ 2 * N * (r * k) := by
      apply mul_le_mul_of_nonneg_right hNs2; positivity
    have e4 : 2 * N * (r * k) ≤ r ^ 2 * N * k := by nlinarith
    nlinarith
  · have : Nₛ * (N₁ + r * k) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hs.le hpos
    have : 0 ≤ 2 * r ^ 2 * N * k := by positivity
    linarith

lemma sizeBound_multiplicity_le (r k Q c' al : ℝ) (hQ : 1 ≤ Q) (hr : 2 ≤ r) (hk8 : 8 ≤ k) (hc : 1 ≤ c')
    (hal : al ≤ 1 + r * k * Q) :
    (2 * Q + 3) * c' + k * Q + c' * al + 3 * c' ≤ 3 * r * k * c' * Q := by
  have hrk : 16 ≤ r * k := by nlinarith
  have e1 : c' * al ≤ c' * (1 + r * k * Q) := mul_le_mul_of_nonneg_left hal (by linarith)
  have hcQ : 1 ≤ c' * Q := by nlinarith
  have e2 : k * Q ≤ k * (c' * Q) :=
    mul_le_mul_of_nonneg_left (by nlinarith) (by linarith)
  have e3 : 2 * k * (c' * Q) ≤ r * k * (c' * Q) :=
    mul_le_mul_of_nonneg_right (by nlinarith) (by linarith)
  have e4 : 16 * (c' * Q) ≤ r * k * (c' * Q) := by nlinarith
  have e5 : c' ≤ c' * Q := by nlinarith
  nlinarith

lemma sizeBound_count_le (r N N₁ Nₛ : ℝ) (hrN1 : 2 ≤ N₁) (hN1 : N₁ ^ 2 ≤ r * N) (hNs1 : Nₛ ≤ N₁) :
    Nₛ * (N₁ + 1) ≤ 2 * r * N := by
  rcases le_or_gt 0 Nₛ with hs | hs
  · have : Nₛ * (N₁ + 1) ≤ N₁ * (N₁ + 1) := mul_le_mul_of_nonneg_right hNs1 (by linarith)
    nlinarith
  · have : Nₛ * (N₁ + 1) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hs.le (by linarith)
    nlinarith

lemma sizeBound_card_le (r N Nₛ k Q c' : ℝ) (hr : 2 ≤ r) (hk : 1 ≤ k) (hQ : 1 ≤ Q) (hc : 1 ≤ c')
    (hN0 : 0 ≤ N) (hNs2 : Nₛ ≤ 2 * N) : Nₛ ≤ r ^ 2 * N * k * c' * Q ^ 2 := by
  have hkcQ : 1 ≤ k * c' * Q ^ 2 := by
    have : 1 ≤ Q ^ 2 := one_le_pow₀ hQ
    have : 1 ≤ k * c' := by nlinarith
    nlinarith
  have h4 : 4 ≤ r ^ 2 := by nlinarith
  have e1 : 2 * N ≤ r ^ 2 * N := by nlinarith
  have e2 : r ^ 2 * N ≤ r ^ 2 * N * (k * c' * Q ^ 2) := by
    have : 0 ≤ r ^ 2 * N := by positivity
    nlinarith
  calc Nₛ ≤ 2 * N := hNs2
    _ ≤ r ^ 2 * N := e1
    _ ≤ r ^ 2 * N * (k * c' * Q ^ 2) := e2
    _ = r ^ 2 * N * k * c' * Q ^ 2 := by ring

lemma pII0_size (CE p r N N₁ Nₛ k Q c' Y al : ℝ) (hCE : 0 ≤ CE) (hp : 0 ≤ p) (hpQ : p ≤ Q)
    (hQ : 1 ≤ Q) (hr : 2 ≤ r) (hrN1 : r ≤ N₁) (hN1 : N₁ ^ 2 ≤ r * N) (hk : N₁ + 3 * r ≤ k)
    (hNs0 : 0 ≤ Nₛ) (hNs1 : Nₛ ≤ N₁) (hNs2 : Nₛ ≤ 2 * N) (hc : 1 ≤ c') (hY : 0 ≤ Y)
    (hal0 : 0 ≤ al) (hal : al ≤ 1 + r * k * Q) :
    32 * p * Y * k ^ 2 * Nₛ * Q ^ 2 *
        (CE * c' * (N₁ + r * k) * Q ^ 2 + (N₁ + 1) * ((2 * Q + 3) * c' + k * Q + c' * al + 3 * c') + 1)
      ≤ 32 * (2 * CE + 7) * (k ^ 3 * r ^ 2 * N * Q ^ 5 * c' * Y) := by
  obtain ⟨hrN, hk8, hN1r⟩ := pII0_basic r N N₁ k hr hrN1 hN1 hk
  have hN0 : 0 ≤ N := by linarith
  set S := (2 * Q + 3) * c' + k * Q + c' * al + 3 * c' with hS
  have hS0 : 0 ≤ S := by
    have : 0 ≤ c' * al := by nlinarith
    nlinarith
  have hS3 : S ≤ 3 * r * k * c' * Q := sizeBound_multiplicity_le r k Q c' al hQ hr hk8 hc hal
  have h1 := sizeBound_frame_le r N N₁ Nₛ k hr hrN1 hN1 hk8 hN0 hNs1 hNs2
  have h3 := sizeBound_count_le r N N₁ Nₛ (by linarith) hN1 hNs1
  have h4 := sizeBound_card_le r N Nₛ k Q c' hr (by linarith) hQ hc hN0 hNs2
  set M := k * r ^ 2 * N * Q ^ 2 * c' with hM
  have hQ2 : Q ≤ Q ^ 2 := by nlinarith
  have a1 : Nₛ * (CE * c' * (N₁ + r * k) * Q ^ 2) ≤ 2 * CE * M := by
    have : Nₛ * (CE * c' * (N₁ + r * k) * Q ^ 2) = (CE * c' * Q ^ 2) * (Nₛ * (N₁ + r * k)) := by ring
    rw [this]
    have hcq : 0 ≤ CE * c' * Q ^ 2 := by positivity
    calc (CE * c' * Q ^ 2) * (Nₛ * (N₁ + r * k)) ≤ (CE * c' * Q ^ 2) * (2 * r ^ 2 * N * k) :=
          mul_le_mul_of_nonneg_left h1 hcq
      _ = 2 * CE * M := by rw [hM]; ring
  have a2 : Nₛ * ((N₁ + 1) * S) ≤ 6 * M := by
    have e : Nₛ * ((N₁ + 1) * S) = (Nₛ * (N₁ + 1)) * S := by ring
    rw [e]
    have hr0 : 0 ≤ 2 * r * N := by positivity
    calc (Nₛ * (N₁ + 1)) * S ≤ (2 * r * N) * S := mul_le_mul_of_nonneg_right h3 hS0
      _ ≤ (2 * r * N) * (3 * r * k * c' * Q) := mul_le_mul_of_nonneg_left hS3 hr0
      _ = 6 * (k * r ^ 2 * N * Q * c') := by ring
      _ ≤ 6 * M := by
        rw [hM]
        have : 0 ≤ k * r ^ 2 * N * c' := by positivity
        nlinarith
  have a3 : Nₛ ≤ M := by rw [hM]; linarith [h4, show r ^ 2 * N * k * c' * Q ^ 2 = k * r ^ 2 * N * Q ^ 2 * c' by ring]
  have hX : Nₛ * (CE * c' * (N₁ + r * k) * Q ^ 2 + (N₁ + 1) * S + 1) ≤ (2 * CE + 7) * M := by
    have : Nₛ * (CE * c' * (N₁ + r * k) * Q ^ 2 + (N₁ + 1) * S + 1)
        = Nₛ * (CE * c' * (N₁ + r * k) * Q ^ 2) + Nₛ * ((N₁ + 1) * S) + Nₛ := by ring
    rw [this]; linarith
  have hB : 0 ≤ 32 * Y * k ^ 2 * Q ^ 2 := by positivity
  have hpX : p * (Nₛ * (CE * c' * (N₁ + r * k) * Q ^ 2 + (N₁ + 1) * S + 1)) ≤ Q * ((2 * CE + 7) * M) := by
    have hX0 : 0 ≤ Nₛ * (CE * c' * (N₁ + r * k) * Q ^ 2 + (N₁ + 1) * S + 1) := by
      have : 0 ≤ CE * c' * (N₁ + r * k) * Q ^ 2 := by
        have : 0 ≤ N₁ + r * k := by nlinarith
        positivity
      have : 0 ≤ (N₁ + 1) * S := mul_nonneg (by linarith) hS0
      positivity
    calc p * _ ≤ Q * (Nₛ * (CE * c' * (N₁ + r * k) * Q ^ 2 + (N₁ + 1) * S + 1)) :=
          mul_le_mul_of_nonneg_right hpQ hX0
      _ ≤ Q * ((2 * CE + 7) * M) := mul_le_mul_of_nonneg_left hX (by linarith)
  calc 32 * p * Y * k ^ 2 * Nₛ * Q ^ 2 * (CE * c' * (N₁ + r * k) * Q ^ 2 + (N₁ + 1) * S + 1)
      = (32 * Y * k ^ 2 * Q ^ 2) * (p * (Nₛ * (CE * c' * (N₁ + r * k) * Q ^ 2 + (N₁ + 1) * S + 1))) := by ring
    _ ≤ (32 * Y * k ^ 2 * Q ^ 2) * (Q * ((2 * CE + 7) * M)) := mul_le_mul_of_nonneg_left hpX hB
    _ = 32 * (2 * CE + 7) * (k ^ 3 * r ^ 2 * N * Q ^ 5 * c' * Y) := by rw [hM]; ring

lemma sizeBound_first_term (r N k Q c' Y : ℝ) (hr : 0 ≤ r) (hN : 1 ≤ N) (hk : 1 ≤ k) (hQ : 1 ≤ Q)
    (hc : 0 ≤ c') (hY : 0 ≤ Y) :
    r ^ 2 * c' * (Y * k ^ 2 * Q) ≤ k ^ 3 * r ^ 2 * N * Q ^ 5 * c' * Y := by
  have h0 : 0 ≤ r ^ 2 * c' * Y * k ^ 2 * Q := by positivity
  have h1 : 1 ≤ k * N * Q ^ 4 := by
    have : 1 ≤ Q ^ 4 := one_le_pow₀ hQ
    have : 1 ≤ k * N := by nlinarith
    nlinarith
  calc r ^ 2 * c' * (Y * k ^ 2 * Q) = (r ^ 2 * c' * Y * k ^ 2 * Q) * 1 := by ring
    _ ≤ (r ^ 2 * c' * Y * k ^ 2 * Q) * (k * N * Q ^ 4) := mul_le_mul_of_nonneg_left h1 h0
    _ = k ^ 3 * r ^ 2 * N * Q ^ 5 * c' * Y := by ring

lemma sizeBound_second_term (r N N₁ k Q c' Y c₀ : ℝ) (hr : 1 ≤ r) (hN : 1 ≤ N) (hk0 : 0 ≤ k) (hQ : 1 ≤ Q)
    (hY : 0 ≤ Y) (hNk : N₁ + r ≤ k) (hc00 : 0 ≤ c₀) (hc0 : c₀ ≤ c') :
    (N₁ + r) * c₀ * (Y * k ^ 2 * Q) ≤ k ^ 3 * r ^ 2 * N * Q ^ 5 * c' * Y := by
  have hW : 0 ≤ Y * k ^ 2 * Q := by positivity
  have e1 : (N₁ + r) * c₀ ≤ k * c' := by
    calc (N₁ + r) * c₀ ≤ k * c₀ := mul_le_mul_of_nonneg_right hNk hc00
      _ ≤ k * c' := mul_le_mul_of_nonneg_left hc0 hk0
  have hc : 0 ≤ c' := le_trans hc00 hc0
  have h1 : 1 ≤ r ^ 2 * N * Q ^ 4 := by
    have : 1 ≤ Q ^ 4 := one_le_pow₀ hQ
    have : 1 ≤ r ^ 2 := one_le_pow₀ hr
    have : 1 ≤ r ^ 2 * N := by nlinarith
    nlinarith
  have h0 : 0 ≤ k ^ 3 * c' * Y * Q := by positivity
  calc (N₁ + r) * c₀ * (Y * k ^ 2 * Q) ≤ k * c' * (Y * k ^ 2 * Q) := mul_le_mul_of_nonneg_right e1 hW
    _ = (k ^ 3 * c' * Y * Q) * 1 := by ring
    _ ≤ (k ^ 3 * c' * Y * Q) * (r ^ 2 * N * Q ^ 4) := mul_le_mul_of_nonneg_left h1 h0
    _ = k ^ 3 * r ^ 2 * N * Q ^ 5 * c' * Y := by ring

lemma sizeBound_third_term (r N N₁ k Q c' Y al : ℝ) (hQ : 1 ≤ Q) (hr : 2 ≤ r) (hk8 : 8 ≤ k) (hc : 1 ≤ c')
    (hY : 0 ≤ Y) (hal0 : 0 ≤ al) (hal : al ≤ 1 + r * k * Q) (hN0 : 0 ≤ N) (hN10 : 0 ≤ N₁)
    (hN1r : N₁ + 1 ≤ 2 * r * N) :
    (N₁ + 1) * ((2 * Q + 3) * c' + k * Q + c' * al + 3 * c') * (Y * k ^ 2 * Q)
      ≤ 6 * (k ^ 3 * r ^ 2 * N * Q ^ 5 * c' * Y) := by
  have hS3 := sizeBound_multiplicity_le r k Q c' al hQ hr hk8 hc hal
  have hS0 : 0 ≤ (2 * Q + 3) * c' + k * Q + c' * al + 3 * c' := by
    have : 0 ≤ c' * al := by nlinarith
    nlinarith
  have hW : 0 ≤ Y * k ^ 2 * Q := by positivity
  have e1 : (N₁ + 1) * ((2 * Q + 3) * c' + k * Q + c' * al + 3 * c') ≤ (2 * r * N) * (3 * r * k * c' * Q) :=
    mul_le_mul hN1r hS3 hS0 (by positivity)
  have h1 : Q ^ 2 ≤ Q ^ 5 := pow_le_pow_right₀ hQ (by norm_num)
  have h0 : 0 ≤ 6 * r ^ 2 * N * k ^ 3 * c' * Y := by positivity
  calc (N₁ + 1) * ((2 * Q + 3) * c' + k * Q + c' * al + 3 * c') * (Y * k ^ 2 * Q)
      ≤ (2 * r * N) * (3 * r * k * c' * Q) * (Y * k ^ 2 * Q) := mul_le_mul_of_nonneg_right e1 hW
    _ = (6 * r ^ 2 * N * k ^ 3 * c' * Y) * Q ^ 2 := by ring
    _ ≤ (6 * r ^ 2 * N * k ^ 3 * c' * Y) * Q ^ 5 := mul_le_mul_of_nonneg_left h1 h0
    _ = 6 * (k ^ 3 * r ^ 2 * N * Q ^ 5 * c' * Y) := by ring

lemma sizeBound_fourth_term (r N k Q c' Y : ℝ) (hr : 1 ≤ r) (hN : 1 ≤ N) (hk : 1 ≤ k) (hQ : 1 ≤ Q)
    (hc : 1 ≤ c') (hY : 0 ≤ Y) : Y * k ^ 2 * Q ≤ k ^ 3 * r ^ 2 * N * Q ^ 5 * c' * Y := by
  have h := sizeBound_first_term r N k Q 1 Y (by linarith) hN hk hQ (by norm_num) hY
  have h0 : 0 ≤ k ^ 3 * r ^ 2 * N * Q ^ 5 * Y := by positivity
  have h1 : Y * k ^ 2 * Q ≤ r ^ 2 * 1 * (Y * k ^ 2 * Q) := by
    have : 1 ≤ r ^ 2 := one_le_pow₀ hr
    have : 0 ≤ Y * k ^ 2 * Q := by positivity
    nlinarith
  have h2 : k ^ 3 * r ^ 2 * N * Q ^ 5 * 1 * Y ≤ k ^ 3 * r ^ 2 * N * Q ^ 5 * c' * Y := by nlinarith
  linarith

lemma pII0_slack (r N N₁ k Q c' Y al c₀ : ℝ) (hQ : 1 ≤ Q) (hr : 2 ≤ r) (hrN1 : r ≤ N₁)
    (hN1 : N₁ ^ 2 ≤ r * N) (hk : N₁ + 3 * r ≤ k) (hc : 1 ≤ c') (hY : 0 ≤ Y)
    (hal0 : 0 ≤ al) (hal : al ≤ 1 + r * k * Q) (hc00 : 0 ≤ c₀) (hc0 : c₀ ≤ c') :
    (100 * r ^ 2 * c' + 24 * (N₁ + r) * c₀ +
        (N₁ + 1) * ((2 * Q + 3) * c' + k * Q + c' * al + 3 * c') + 1) * (Y * k ^ 2 * Q)
      ≤ 155 * (k ^ 3 * r ^ 2 * N * Q ^ 5 * c' * Y) := by
  obtain ⟨hrN, hk8, hN1r⟩ := pII0_basic r N N₁ k hr hrN1 hN1 hk
  have hN : 1 ≤ N := by linarith
  have q1 := sizeBound_first_term r N k Q c' Y (by linarith) hN (by linarith) hQ (by linarith) hY
  have q2 := sizeBound_second_term r N N₁ k Q c' Y c₀ (by linarith) hN (by linarith) hQ hY (by linarith) hc00 hc0
  have q3 := sizeBound_third_term r N N₁ k Q c' Y al hQ hr hk8 hc hY hal0 hal (by linarith) (by linarith) hN1r
  have q4 := sizeBound_fourth_term r N k Q c' Y (by linarith) hN (by linarith) hQ hc hY
  have hM : 0 ≤ k ^ 3 * r ^ 2 * N * Q ^ 5 * c' * Y := by
    have : 0 ≤ k := by linarith
    have : 0 ≤ N := by linarith
    have : 0 ≤ Q := by linarith
    have : 0 ≤ c' := by linarith
    positivity
  have e : (100 * r ^ 2 * c' + 24 * (N₁ + r) * c₀ +
        (N₁ + 1) * ((2 * Q + 3) * c' + k * Q + c' * al + 3 * c') + 1) * (Y * k ^ 2 * Q)
      = 100 * (r ^ 2 * c' * (Y * k ^ 2 * Q)) + 24 * ((N₁ + r) * c₀ * (Y * k ^ 2 * Q))
        + (N₁ + 1) * ((2 * Q + 3) * c' + k * Q + c' * al + 3 * c') * (Y * k ^ 2 * Q)
        + Y * k ^ 2 * Q := by ring
  rw [e]
  linarith

lemma pII0_floor (L Y k Q a B : ℝ) (hQ0 : 0 < Q) (ha : 0 ≤ a) (hYk100 : 100 ≤ Y * k ^ 2)
    (h : (L + 1) * (Y * k ^ 2 * Q) ≤ a) (hB : a / Q ≤ B) :
    L ≤ ((⌊B / (Y * k ^ 2)⌋ : ℤ) : ℝ) ∧ ((⌊B / (Y * k ^ 2)⌋ : ℤ) : ℝ) ≤ B / 100 := by
  have hW : 0 < Y * k ^ 2 := by linarith
  have h1 : (L + 1) * (Y * k ^ 2) ≤ a / Q := by
    rw [le_div_iff₀ hQ0]; linarith [show (L + 1) * (Y * k ^ 2) * Q = (L + 1) * (Y * k ^ 2 * Q) by ring]
  have h2 : L + 1 ≤ B / (Y * k ^ 2) := by
    rw [le_div_iff₀ hW]; linarith
  have hB0 : 0 ≤ B := le_trans (div_nonneg ha hQ0.le) hB
  constructor
  · have := Int.sub_one_lt_floor (B / (Y * k ^ 2))
    linarith
  · have h3 : B / (Y * k ^ 2) ≤ B / 100 := by
      gcongr
    exact le_trans (Int.floor_le _) h3

lemma sizeBound_one_le_product (k r N Q c' Y : ℝ) (hk : 1 ≤ k) (hr : 1 ≤ r) (hN : 1 ≤ N) (hQ : 1 ≤ Q)
    (hc : 1 ≤ c') (hY : 1 ≤ Y) : 1 ≤ k ^ 3 * r ^ 2 * N * Q ^ 5 * c' * Y := by
  have h1 : 1 ≤ k ^ 3 := one_le_pow₀ hk
  have h2 : 1 ≤ r ^ 2 := one_le_pow₀ hr
  have h3 : 1 ≤ Q ^ 5 := one_le_pow₀ hQ
  exact pII0_one_le_mul (pII0_one_le_mul (pII0_one_le_mul (pII0_one_le_mul
    (pII0_one_le_mul h1 h2) hN) h3) hc) hY

lemma pII0_om (r N n' c₀ c'' : ℕ) (hr : 1 ≤ r) (hN : 1 ≤ N) : (c₀ : ℝ) ≤ omII r N n' c₀ c'' := by
  unfold omII
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hrN : (1 : ℝ) ≤ r * N := pII0_one_le_mul hr' hN'
  have hc : (0 : ℝ) ≤ c₀ := Nat.cast_nonneg _
  have h2 : (0 : ℝ) ≤ 2 * r * n' * c'' := by positivity
  nlinarith

set_option maxHeartbeats 1000000 in
theorem secondParameterSizeBounds_holds : ParamsII0 := by
  intro CE C₂ hCE hC₂
  refine ⟨64 * CE + 400 + C₂, by linarith, ?_⟩
  intro p r N N₁ Nₛ J k n' L₁ G' Y a al c₀ c'' D cStar hH hal0 hal
  obtain ⟨hp13, hr2, hrN1, hN1, hrY, hClog, hk, h256, hCD, hDc, hCa, hL1, hLG, hNs1, hNs2,
    hJ, hJr⟩ := hH
  have hr2' : (2 : ℝ) ≤ r := by exact_mod_cast hr2
  have hrN1' : (r : ℝ) ≤ N₁ := by exact_mod_cast hrN1
  have hN1' : (N₁ : ℝ) ^ 2 ≤ r * N := by exact_mod_cast hN1
  have hk' : (N₁ : ℝ) + 3 * r ≤ k := by exact_mod_cast hk
  have hNs1' : (Nₛ : ℝ) ≤ N₁ := by exact_mod_cast hNs1
  have hNs2' : (Nₛ : ℝ) ≤ 2 * N := by exact_mod_cast hNs2
  obtain ⟨hrN, hk8, hN1r⟩ := pII0_basic r N N₁ k hr2' hrN1' hN1' hk'
  have hNone : (1 : ℝ) ≤ N := by linarith
  have hNone' : 1 ≤ N := by exact_mod_cast hNone
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (show 1 ≤ p by omega)
  have hQ1 : 1 ≤ QII p G' := one_le_pow₀ hp1
  have hpQ : (p : ℝ) ≤ QII p G' := by
    unfold QII
    calc (p : ℝ) = (p : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (p : ℝ) ^ G' := pow_le_pow_right₀ hp1 (by omega)
  have hom0 : (0 : ℝ) ≤ omII r N n' c₀ c'' := by unfold omII; positivity
  have hc1 : 1 ≤ cPrII r N n' c₀ c'' cStar := by
    unfold cPrII
    have : (8 : ℝ) ≤ cStar := by exact_mod_cast (show 8 ≤ cStar by omega)
    linarith
  have hc0le : (c₀ : ℝ) ≤ cPrII r N n' c₀ c'' cStar := by
    unfold cPrII
    have := pII0_om r N n' c₀ c'' (by omega) hNone'
    have : (0 : ℝ) ≤ cStar := Nat.cast_nonneg _
    linarith
  have hY1 : 1 ≤ Y := by linarith
  have hY0 : 0 ≤ Y := by linarith
  set Q := QII p G' with hQdef
  set c' := cPrII r N n' c₀ c'' cStar with hcdef
  set M := (k : ℝ) ^ 3 * r ^ 2 * N * Q ^ 5 * c' * Y with hMdef
  have hM0 : 0 ≤ M := by
    have : 0 ≤ Q := by linarith
    have : 0 ≤ c' := by linarith
    positivity
  have hCa' : (64 * CE + 400 + C₂) * M ≤ a := by
    have : (64 * CE + 400 + C₂) * M
        = (64 * CE + 400 + C₂) * (k : ℝ) ^ 3 * (r : ℝ) ^ 2 * N * Q ^ 5 * c' * Y := by
      rw [hMdef]; ring
    linarith
  have ha0 : 0 ≤ a := le_trans (mul_nonneg (by linarith) hM0) hCa'
  refine ⟨?_, ?_, ?_, ?_, hY1, ?_⟩
  · unfold errorTerm mStarII
    have hs := pII0_size CE p r N N₁ Nₛ k Q c' Y al (by linarith) (Nat.cast_nonneg _) hpQ hQ1
      hr2' hrN1' hN1' hk' (Nat.cast_nonneg _) hNs1' hNs2' hc1 hY0 hal0 hal
    have : 32 * (2 * CE + 7) * M ≤ (64 * CE + 400 + C₂) * M :=
      mul_le_mul_of_nonneg_right (by linarith) hM0
    linarith
  · intro B hB
    unfold slII mStarII
    have hs := pII0_slack r N N₁ k Q c' Y al c₀ hQ1 hr2' hrN1' hN1' hk' hc1 hY0 hal0 hal
      (Nat.cast_nonneg _) hc0le
    have h155 : 155 * M ≤ (64 * CE + 400 + C₂) * M :=
      mul_le_mul_of_nonneg_right (by linarith) hM0
    have hYk : 100 ≤ Y * (k : ℝ) ^ 2 := by
      have : (64 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
      nlinarith
    exact pII0_floor _ Y k Q a B (by linarith) ha0 hYk (by linarith) hB
  · have : (0 : ℝ) ≤ (k : ℝ) ^ 2 * Y ^ 2 := by positivity
    nlinarith
  · rcases le_or_gt 0 (Real.log a) with hl | hl
    · have hsq : (Nₛ : ℝ) ^ 2 ≤ (N₁ : ℝ) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hNs1' 2
      have e1 : C₂ * (Nₛ : ℝ) ^ 2 ≤ (64 * CE + 400 + C₂) * (N₁ : ℝ) ^ 2 :=
        mul_le_mul (by linarith) hsq (by positivity) (by linarith)
      have e2 := mul_le_mul_of_nonneg_right e1 hl
      linarith
    · have : C₂ * (Nₛ : ℝ) ^ 2 * Real.log a ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) hl.le
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg _
      linarith
  · omega

end Formalism.CountingSumsFrames
