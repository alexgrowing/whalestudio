import Mathlib
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MeanSquareHypWIff
import Formalism.LandauZeroFreeBounds.LogDerivRegionChiOf

open Finset Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

open Formalism.HermitianLattices.ZeroFreeRegionGL2

theorem piAP_le_card_PPset_add (X : ℝ) (m₀ a₀ : ℕ) (hX : 1 ≤ X) :
    (piAP X m₀ a₀ : ℝ) ≤ ((PPset m₀ a₀ X).card : ℝ) + X ^ (1 / 2 : ℝ) := by
  have hs : (0:ℝ) ≤ X ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by linarith) _
  have key : piAP X m₀ a₀ ≤ (PPset m₀ a₀ X).card + ⌊X ^ (1 / 2 : ℝ)⌋₊ := by
    unfold piAP
    calc _ ≤ (PPset m₀ a₀ X ∪ Icc 1 ⌊X ^ (1 / 2 : ℝ)⌋₊).card := by
          apply Finset.card_le_card
          intro q hq
          simp only [PPset, Finset.mem_union, Finset.mem_filter, Finset.mem_Icc] at hq ⊢
          by_cases h : X ^ (1 / 2 : ℝ) < (q : ℝ)
          · exact Or.inl ⟨hq.1, hq.2.1, hq.2.2, h⟩
          · exact Or.inr ⟨hq.1.1, Nat.le_floor (not_lt.mp h)⟩
      _ ≤ (PPset m₀ a₀ X).card + (Icc 1 ⌊X ^ (1 / 2 : ℝ)⌋₊).card := Finset.card_union_le _ _
      _ = (PPset m₀ a₀ X).card + ⌊X ^ (1 / 2 : ℝ)⌋₊ := by simp
  have h3 : ((⌊X ^ (1 / 2 : ℝ)⌋₊ : ℕ) : ℝ) ≤ X ^ (1 / 2 : ℝ) := Nat.floor_le hs
  have key' : (piAP X m₀ a₀ : ℝ) ≤ ((PPset m₀ a₀ X).card : ℝ) + (⌊X ^ (1 / 2 : ℝ)⌋₊ : ℝ) := by
    exact_mod_cast key
  linarith

theorem intervalIntegrable_inv_log {a b : ℝ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    IntervalIntegrable (fun t => 1 / Real.log t) MeasureTheory.volume a b := by
  have hmem : ∀ t ∈ Set.uIcc a b, 2 ≤ t := by
    intro t ht
    rcases Set.mem_uIcc.mp ht with h | h
    · linarith [h.1]
    · linarith [h.1]
  apply ContinuousOn.intervalIntegrable
  refine ContinuousOn.div continuousOn_const (Real.continuousOn_log.mono ?_) ?_
  · intro t ht
    have h2 := hmem t ht
    exact ne_of_gt (by linarith)
  · intro t ht
    have h2 := hmem t ht
    exact (Real.log_pos (by linarith)).ne'

theorem liX_sub_ge {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    (b - a) / Real.log b ≤ liX b - liX a := by
  have hb : 2 ≤ b := le_trans ha hab
  have hsub : liX b - liX a = ∫ t in a..b, 1 / Real.log t := by
    unfold liX
    exact intervalIntegral.integral_interval_sub_left (intervalIntegrable_inv_log le_rfl hb)
      (intervalIntegrable_inv_log le_rfl ha)
  rw [hsub]
  have hconst : ∫ _t in a..b, (1 / Real.log b) = (b - a) / Real.log b := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [← hconst]
  apply intervalIntegral.integral_mono_on hab intervalIntegrable_const (intervalIntegrable_inv_log ha hb)
  intro t ht
  have h2t : 2 ≤ t := le_trans ha ht.1
  have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
  exact one_div_le_one_div_of_le hlogt (Real.log_le_log (by linarith) ht.2)

theorem liX_two : liX 2 = 0 := by
  unfold liX
  simp

theorem liX_nonneg {a : ℝ} (ha : 2 ≤ a) : 0 ≤ liX a := by
  have h := liX_sub_ge (le_refl (2:ℝ)) ha
  rw [liX_two, sub_zero] at h
  exact le_trans (div_nonneg (by linarith) (Real.log_nonneg (by linarith))) h

theorem exp_neg_le_one_sub_half {w : ℝ} (h0 : 0 ≤ w) (h1 : w ≤ 1) : Real.exp (-w) ≤ 1 - w / 2 := by
  have he1 : Real.exp (-1) ≤ 1 / 2 := by
    have h2 : (2:ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
    have hm : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos (-1)]
  have hx : (1 - w) • (0:ℝ) + w • (-1:ℝ) = -w := by simp [smul_eq_mul]
  have hconv := convexOn_exp.2 (Set.mem_univ (0:ℝ)) (Set.mem_univ (-1:ℝ))
    (by linarith : (0:ℝ) ≤ 1 - w) h0 (by ring : (1 - w) + w = 1)
  rw [hx, smul_eq_mul, smul_eq_mul, Real.exp_zero] at hconv
  nlinarith [mul_le_mul_of_nonneg_left he1 h0]

theorem mainAP_lower {M : ℕ} [NeZero M] (h8 : 8 ∣ M) (e : Option (DirichletCharacter ℂ M × ℝ))
    (he : ∀ p : DirichletCharacter ℂ M × ℝ, e = some p → IsExcPair p.1 p.2)
    (c : ℝ) (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hc : ∀ (χ : DirichletCharacter ℂ M) (β : ℝ), χ ^ 2 = 1 → χ ≠ 1 →
      DirichletCharacter.LFunction χ (β : ℂ) = 0 → β ≤ 1 - c * (M : ℝ) ^ (-1 : ℝ))
    (b : ℕ) (X : ℝ) (hX : 0 < X) (hY : 4 ≤ Real.log X) :
    c * X / (2 * Real.log X * (M : ℝ) ^ 2) ≤ mainAP e b X := by
  have hM8 : (8:ℝ) ≤ M := by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) h8
  have hMpos : (0:ℝ) < M := by linarith
  have hlogX : 0 < Real.log X := by linarith
  have hX5 : 5 ≤ X := by
    have h := Real.add_one_le_exp (Real.log X)
    rw [Real.exp_log hX] at h
    linarith
  have hX2 : (2:ℝ) ≤ X := by linarith
  have hlogM : 1 ≤ Real.log M := by
    have h1 : Real.log 8 ≤ Real.log M := Real.log_le_log (by norm_num) hM8
    have h2 : (1:ℝ) ≤ Real.log 8 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      linarith [Real.exp_one_lt_d9]
    linarith
  have hcM0 : 0 ≤ c / M := div_nonneg hc0.le hMpos.le
  have hcM1 : c / M ≤ 1 := by
    rw [div_le_iff₀ hMpos]
    linarith
  have hfin : ∀ N : ℝ, c * X / (2 * Real.log X * M) ≤ N →
      c * X / (2 * Real.log X * (M:ℝ) ^ 2) ≤ N / (M.totient : ℝ) := by
    intro N hN
    have hT0 : 0 ≤ c * X / (2 * Real.log X * M) :=
      div_nonneg (mul_nonneg hc0.le hX.le) (mul_pos (mul_pos two_pos hlogX) hMpos).le
    have hN0 : 0 ≤ N := le_trans hT0 hN
    have hφpos : (0:ℝ) < M.totient := by
      exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne M))
    have hφle : (M.totient : ℝ) ≤ M := by exact_mod_cast Nat.totient_le M
    calc c * X / (2 * Real.log X * (M:ℝ) ^ 2) = (c * X / (2 * Real.log X * M)) / M := by ring
      _ ≤ N / M := div_le_div_of_nonneg_right hN hMpos.le
      _ ≤ N / M.totient := div_le_div_of_nonneg_left hN0 hφpos hφle
  have hT : c * X / (2 * Real.log X * M) = (c * X / (2 * M)) / Real.log X := by ring
  cases e with
  | none =>
    show c * X / (2 * Real.log X * (M:ℝ) ^ 2) ≤ liX X / (M.totient : ℝ)
    apply hfin
    have h := liX_sub_ge (le_refl (2:ℝ)) hX2
    rw [liX_two, sub_zero] at h
    have hXM : c * X / (2 * M) ≤ X - 2 := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    rw [hT]
    exact le_trans (div_le_div_of_nonneg_right hXM hlogX.le) h
  | some p =>
    obtain ⟨χ₁, β₁⟩ := p
    obtain ⟨hsq, hne1, hL0, hβlow, hβ1⟩ := he (χ₁, β₁) rfl
    have hβc := hc χ₁ β₁ hsq hne1 hL0
    rw [Real.rpow_neg_one, ← div_eq_mul_inv] at hβc
    have hβ78 : 7 / 8 ≤ β₁ := by
      have h1 : 1 / (8 * Real.log M) ≤ 1 / 8 := one_div_le_one_div_of_le (by norm_num) (by linarith)
      linarith
    have hXβ_eq : X ^ β₁ = Real.exp (Real.log X * β₁) := Real.rpow_def_of_pos hX β₁
    have hXβ2 : 2 ≤ X ^ β₁ := by
      rw [hXβ_eq]
      have := Real.add_one_le_exp (Real.log X * β₁)
      nlinarith
    have hXβX : X ^ β₁ ≤ X := by
      have := Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ) ≤ X) hβ1.le
      rwa [Real.rpow_one] at this
    have hXβup : X ^ β₁ ≤ X * Real.exp (-(c / M)) := by
      have hle : Real.log X * β₁ ≤ Real.log X + -(c / M) := by
        nlinarith [mul_le_mul_of_nonneg_left hβc hlogX.le, le_mul_of_one_le_left hcM0 hlogM]
      calc X ^ β₁ = Real.exp (Real.log X * β₁) := hXβ_eq
        _ ≤ Real.exp (Real.log X + -(c / M)) := Real.exp_le_exp.mpr hle
        _ = X * Real.exp (-(c / M)) := by rw [Real.exp_add, Real.exp_log hX]
    have hexp := exp_neg_le_one_sub_half hcM0 hcM1
    have hgap : c * X / (2 * M) ≤ X - X ^ β₁ := by
      have h1 : X * Real.exp (-(c / M)) ≤ X * (1 - c / M / 2) := mul_le_mul_of_nonneg_left hexp hX.le
      have e2 : c * X / (2 * M) = X * (c / M / 2) := by ring
      rw [e2]
      nlinarith
    have hθ : (χ₁ (b : ZMod M)).re ≤ 1 :=
      le_trans (Complex.re_le_norm _) (DirichletCharacter.norm_le_one χ₁ _)
    have hL0' : 0 ≤ liX (X ^ β₁) := liX_nonneg hXβ2
    have hsub := liX_sub_ge hXβ2 hXβX
    show c * X / (2 * Real.log X * (M:ℝ) ^ 2) ≤
      (liX X - (χ₁ (b : ZMod M)).re * liX (X ^ β₁)) / (M.totient : ℝ)
    apply hfin
    rw [hT]
    have h3 : (c * X / (2 * M)) / Real.log X ≤ (X - X ^ β₁) / Real.log X :=
      div_le_div_of_nonneg_right hgap hlogX.le
    nlinarith [mul_le_mul_of_nonneg_right hθ hL0']

theorem size_ineq {c Y Λ : ℝ} (hc0 : 0 < c) (hY0 : 0 < Y) (h80 : 80 * Λ ≤ Y)
    (hlog : Real.log (320 / c) ≤ Y / 20) :
    4 * Real.exp (Y * (9 / 10)) ≤ c * Real.exp Y / (2 * Y * Real.exp Λ ^ 2) := by
  have hApos : 0 < Real.exp (Y / 40) := Real.exp_pos _
  have hDpos : 0 < Real.exp (Y * (9 / 10)) := Real.exp_pos _
  have hLpos : 0 < Real.exp Λ ^ 2 := pow_pos (Real.exp_pos _) 2
  have hY1 : Y ≤ 40 * Real.exp (Y / 40) := by
    have := Real.add_one_le_exp (Y / 40)
    linarith
  have hcB : 320 ≤ c * Real.exp (Y / 20) := by
    have h := Real.exp_le_exp.mpr hlog
    rw [Real.exp_log (div_pos (by norm_num) hc0), div_le_iff₀ hc0] at h
    linarith
  have hL : Real.exp Λ ^ 2 ≤ Real.exp (Y / 40) := by
    rw [← Real.exp_nat_mul]
    exact Real.exp_le_exp.mpr (by push_cast; linarith)
  have hexpY : Real.exp Y = Real.exp (Y * (9 / 10)) * Real.exp (Y / 20) * Real.exp (Y / 40) * Real.exp (Y / 40) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have h1 : Y * Real.exp Λ ^ 2 ≤ 40 * Real.exp (Y / 40) * Real.exp (Y / 40) :=
    mul_le_mul hY1 hL hLpos.le (by linarith)
  have h2 : 8 * (Y * Real.exp Λ ^ 2) ≤ c * Real.exp (Y / 20) * (Real.exp (Y / 40) * Real.exp (Y / 40)) := by
    have h3 : 320 * (Real.exp (Y / 40) * Real.exp (Y / 40)) ≤ c * Real.exp (Y / 20) * (Real.exp (Y / 40) * Real.exp (Y / 40)) :=
      mul_le_mul_of_nonneg_right hcB (by positivity)
    linarith
  rw [le_div_iff₀ (mul_pos (mul_pos two_pos hY0) hLpos), hexpY]
  have h4 := mul_le_mul_of_nonneg_left h2 hDpos.le
  nlinarith

theorem err_le_half {A c₃ Y Λ l : ℝ} (hc₃ : 0 < c₃) (hΛ : 0 < Λ) (hYΛ : l ^ 2 / 4 * Λ ≤ Y)
    (hYl : l ^ 2 / 4 ≤ Y)
    (hK1 : Real.log (4 * (|A| + 1)) ≤ c₃ * (l ^ 2 / 4))
    (hK2 : Real.log (4 * (|A| + 1)) ^ 2 ≤ c₃ * (l ^ 2 / 4)) :
    |A| * (Real.exp (-(c₃ * Y / Λ)) + Real.exp (-Real.sqrt (c₃ * Y))) ≤ 1 / 2 := by
  set K := Real.log (4 * (|A| + 1)) with hK
  have hA1 : 0 < 4 * (|A| + 1) := by positivity
  have hK0 : 0 ≤ K := Real.log_nonneg (by linarith [abs_nonneg A])
  have hexpK : Real.exp (-K) = 1 / (4 * (|A| + 1)) := by
    rw [Real.exp_neg, Real.exp_log hA1, one_div]
  have hl : l ^ 2 / 4 ≤ Y / Λ := by
    rw [le_div_iff₀ hΛ]
    linarith
  have hc3l : c₃ * (l ^ 2 / 4) ≤ c₃ * Y / Λ := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hl hc₃.le
  have e1 : Real.exp (-(c₃ * Y / Λ)) ≤ Real.exp (-K) := Real.exp_le_exp.mpr (by linarith)
  have hsq : K ≤ Real.sqrt (c₃ * Y) := by
    have hKY : K ^ 2 ≤ c₃ * Y := by
      have : c₃ * (l ^ 2 / 4) ≤ c₃ * Y := mul_le_mul_of_nonneg_left hYl hc₃.le
      linarith
    have h := Real.sqrt_le_sqrt hKY
    rwa [Real.sqrt_sq hK0] at h
  have e2 : Real.exp (-Real.sqrt (c₃ * Y)) ≤ Real.exp (-K) := Real.exp_le_exp.mpr (by linarith)
  rw [hexpK] at e1 e2
  have hsum : Real.exp (-(c₃ * Y / Λ)) + Real.exp (-Real.sqrt (c₃ * Y)) ≤ 2 / (4 * (|A| + 1)) := by
    have : 2 / (4 * (|A| + 1)) = 1 / (4 * (|A| + 1)) + 1 / (4 * (|A| + 1)) := by ring
    linarith
  calc |A| * (Real.exp (-(c₃ * Y / Λ)) + Real.exp (-Real.sqrt (c₃ * Y)))
      ≤ |A| * (2 / (4 * (|A| + 1))) := mul_le_mul_of_nonneg_left hsum (abs_nonneg A)
    _ ≤ 1 / 2 := by
      rw [mul_div_assoc', div_le_iff₀ hA1]
      nlinarith [abs_nonneg A]

theorem range_ok {C₀ ε x Λ Y : ℝ} (hε : 0 < ε) (hx : 1 ≤ x) (hΛ : 1 ≤ Λ) (hl1 : 1 ≤ Real.log x)
    (hl : 4 * |C₀| * (5 + ε / 5) ≤ Real.log x)
    (h1 : (1 / 4) * Real.log x ^ 2 * Λ ≤ Y) (h3 : Y ≤ x ^ (ε / 5) * Real.log x ^ 2) :
    C₀ * Λ * Real.log (Λ + 2) ≤ Y := by
  set L := Real.log x with hLdef
  have hL0 : 0 < L := by linarith
  have hxpos : 0 < x := by linarith
  have hxr : 0 < x ^ (ε / 5) := Real.rpow_pos_of_pos hxpos _
  have hxe1 : 1 ≤ x ^ (ε / 5) := Real.one_le_rpow hx (by linarith)
  have hΛle : Λ ≤ 4 * x ^ (ε / 5) := by
    have h13 : (1 / 4) * L ^ 2 * Λ ≤ x ^ (ε / 5) * L ^ 2 := le_trans h1 h3
    have hL2 : 0 < L ^ 2 := pow_pos hL0 2
    nlinarith
  have hlogΛ : Real.log (Λ + 2) ≤ Real.log 6 + ε / 5 * L := by
    have h6 : Λ + 2 ≤ 6 * x ^ (ε / 5) := by linarith
    have h := Real.log_le_log (by linarith) h6
    rw [Real.log_mul (by norm_num) hxr.ne', Real.log_rpow hxpos] at h
    exact h
  have hlog6 : Real.log 6 ≤ 5 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 6)
    linarith
  have hlogpos : 0 ≤ Real.log (Λ + 2) := Real.log_nonneg (by linarith)
  have hkey : |C₀| * Real.log (Λ + 2) ≤ L ^ 2 / 4 := by
    have hA0 := abs_nonneg C₀
    have hb : Real.log (Λ + 2) ≤ L * (5 + ε / 5) := by nlinarith
    have h1' : |C₀| * Real.log (Λ + 2) ≤ |C₀| * (L * (5 + ε / 5)) := mul_le_mul_of_nonneg_left hb hA0
    have h2' : (4 * |C₀| * (5 + ε / 5)) * L ≤ L * L := mul_le_mul_of_nonneg_right hl hL0.le
    nlinarith
  have hΛlog : 0 ≤ Λ * Real.log (Λ + 2) := mul_nonneg (by linarith) hlogpos
  calc C₀ * Λ * Real.log (Λ + 2) = C₀ * (Λ * Real.log (Λ + 2)) := by ring
    _ ≤ |C₀| * (Λ * Real.log (Λ + 2)) := mul_le_mul_of_nonneg_right (le_abs_self C₀) hΛlog
    _ = Λ * (|C₀| * Real.log (Λ + 2)) := by ring
    _ ≤ Λ * (L ^ 2 / 4) := mul_le_mul_of_nonneg_left hkey (by linarith)
    _ = (1 / 4) * L ^ 2 * Λ := by ring
    _ ≤ Y := h1

theorem count_pos {c₃ A₀ C₀ c ε : ℝ} (hc₃ : 0 < c₃) (hcpos : 0 < c) (hc1 : c ≤ 1) (hε : 0 < ε)
    {m₀ : ℕ} [NeZero m₀] (h8 : 8 ∣ m₀) (a₀ : ℕ) (hcop : a₀.Coprime m₀)
    (e : Option (DirichletCharacter ℂ m₀ × ℝ))
    (he1 : ∀ p : DirichletCharacter ℂ m₀ × ℝ, e = some p → IsExcPair p.1 p.2)
    (he3 : ∀ (X : ℝ) (b : ℕ), 2 ≤ X → C₀ * Real.log m₀ * Real.log (Real.log m₀ + 2) ≤ Real.log X →
      b.Coprime m₀ → |(piAP X m₀ b : ℝ) - mainAP e b X| ≤
        A₀ * (Real.exp (-(c₃ * Real.log X / Real.log m₀)) + Real.exp (-Real.sqrt (c₃ * Real.log X))) *
          mainAP e b X)
    (hcb : ∀ (χ : DirichletCharacter ℂ m₀) (β : ℝ), χ ^ 2 = 1 → χ ≠ 1 →
      DirichletCharacter.LFunction χ (β : ℂ) = 0 → β ≤ 1 - c * (m₀ : ℝ) ^ (-1 : ℝ))
    (x X : ℝ) (hx1 : 1 ≤ x) (hl320 : 320 ≤ Real.log x)
    (hlC : 4 * |C₀| * (5 + ε / 5) ≤ Real.log x)
    (hlK1 : 4 * Real.log (4 * (|A₀| + 1)) / c₃ ≤ Real.log x)
    (hlK2 : 4 * Real.log (4 * (|A₀| + 1)) ^ 2 / c₃ ≤ Real.log x)
    (hlc : |Real.log (320 / c)| ≤ Real.log x)
    (h1 : (1 / 4) * Real.log x ^ 2 * Real.log m₀ ≤ Real.log X)
    (h3 : Real.log X ≤ x ^ (ε / 5) * Real.log x ^ 2) (hpos : 0 < X) :
    X ^ (9 / 10 : ℝ) ≤ ((PPset m₀ a₀ X).card : ℝ) := by
  have hm8 : (8:ℝ) ≤ m₀ := by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne m₀)) h8
  have hmpos : (0:ℝ) < m₀ := by linarith
  have hΛ1 : 1 ≤ Real.log m₀ := by
    have h1' : Real.log 8 ≤ Real.log m₀ := Real.log_le_log (by norm_num) hm8
    have h2' : (1:ℝ) ≤ Real.log 8 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      linarith [Real.exp_one_lt_d9]
    linarith
  have hl1 : 1 ≤ Real.log x := by linarith
  have hl2 : 320 * Real.log x ≤ Real.log x ^ 2 := by nlinarith
  have hYl : Real.log x ^ 2 / 4 ≤ Real.log X := by nlinarith
  have hY80 : 80 * Real.log m₀ ≤ Real.log X := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ Real.log m₀) (by nlinarith : (0:ℝ) ≤ Real.log x ^ 2 / 4 - 80)]
  have hY4 : 4 ≤ Real.log X := by linarith
  have hY0 : 0 < Real.log X := by linarith
  have hX2 : 2 ≤ X := by
    have h := Real.add_one_le_exp (Real.log X)
    rw [Real.exp_log hpos] at h
    linarith
  have hX1 : 1 ≤ X := by linarith
  have hrange : C₀ * Real.log m₀ * Real.log (Real.log m₀ + 2) ≤ Real.log X :=
    range_ok hε hx1 hΛ1 hl1 hlC h1 h3
  have hmain := he3 X a₀ hX2 hrange hcop
  have hll : Real.log x ≤ Real.log x ^ 2 := by nlinarith
  have hK1 : Real.log (4 * (|A₀| + 1)) ≤ c₃ * (Real.log x ^ 2 / 4) := by
    rw [div_le_iff₀ hc₃] at hlK1
    nlinarith [mul_le_mul_of_nonneg_left hll hc₃.le]
  have hK2 : Real.log (4 * (|A₀| + 1)) ^ 2 ≤ c₃ * (Real.log x ^ 2 / 4) := by
    rw [div_le_iff₀ hc₃] at hlK2
    nlinarith [mul_le_mul_of_nonneg_left hll hc₃.le]
  have herr := err_le_half (A := A₀) hc₃ (by linarith : 0 < Real.log m₀)
    (by linarith : Real.log x ^ 2 / 4 * Real.log m₀ ≤ Real.log X) hYl hK1 hK2
  have hlow := mainAP_lower h8 e he1 c hcpos hc1 hcb a₀ X hpos hY4
  have hlogc : Real.log (320 / c) ≤ Real.log X / 20 := by
    have := le_abs_self (Real.log (320 / c))
    linarith
  have hsize := size_ineq hcpos hY0 hY80 hlogc
  rw [Real.exp_log hpos, Real.exp_log hmpos] at hsize
  have hXpow : X ^ (9 / 10 : ℝ) = Real.exp (Real.log X * (9 / 10)) := Real.rpow_def_of_pos hpos _
  have hhalf : X ^ (1 / 2 : ℝ) ≤ X ^ (9 / 10 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num)
  have hpp := piAP_le_card_PPset_add X m₀ a₀ hX1
  set Mn := mainAP e a₀ X with hMn
  set E := Real.exp (-(c₃ * Real.log X / Real.log m₀)) + Real.exp (-Real.sqrt (c₃ * Real.log X)) with hE
  have hE0 : 0 ≤ E := by positivity
  have h4 : 0 ≤ 4 * Real.exp (Real.log X * (9 / 10)) := by positivity
  have hMn0 : 0 ≤ Mn := le_trans (le_trans h4 hsize) hlow
  have hAE : A₀ * E * Mn ≤ |A₀| * E * Mn :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self A₀) hE0) hMn0
  have herr2 : |A₀| * E * Mn ≤ 1 / 2 * Mn := mul_le_mul_of_nonneg_right herr hMn0
  have habs := neg_abs_le ((piAP X m₀ a₀ : ℝ) - Mn)
  linarith

theorem count_a (hP : PNTAPRelW) (hE : Formalism.ZeroFreeDirichlet.ExcBound) (ε : ℝ) (hε : 0 < ε) : ∃ x₀ : ℝ, ∀ (x X : ℝ) (m₀ a₀ : ℕ),
    x₀ ≤ x → 0 < m₀ → 8 ∣ m₀ → a₀.Coprime m₀ →
    (1 / 4) * Real.log x ^ 2 * Real.log m₀ ≤ Real.log X → x ^ (ε / 6) ≤ Real.log X →
    Real.log X ≤ x ^ (ε / 5) * Real.log x ^ 2 →
    X ^ (9 / 10 : ℝ) ≤ ((PPset m₀ a₀ X).card : ℝ) := by
  obtain ⟨c₃, A₀, C₀, hc₃, hPM⟩ := hP
  obtain ⟨c0, hc0, hcb0⟩ := hE 1 one_pos
  have hcpos : 0 < min c0 1 := lt_min hc0 one_pos
  have hc1 : min c0 1 ≤ 1 := min_le_right _ _
  refine ⟨Real.exp (320 + 4 * |C₀| * (5 + ε / 5) + |4 * Real.log (4 * (|A₀| + 1)) / c₃|
    + |4 * Real.log (4 * (|A₀| + 1)) ^ 2 / c₃| + |Real.log (320 / min c0 1)|), ?_⟩
  intro x X m₀ a₀ hx hm0 h8 hcop h1 h6 h3
  haveI : NeZero m₀ := ⟨hm0.ne'⟩
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hlx : 320 + 4 * |C₀| * (5 + ε / 5) + |4 * Real.log (4 * (|A₀| + 1)) / c₃|
      + |4 * Real.log (4 * (|A₀| + 1)) ^ 2 / c₃| + |Real.log (320 / min c0 1)| ≤ Real.log x := by
    rw [← Real.exp_le_exp, Real.exp_log hxpos]
    exact hx
  have hC0 : 0 ≤ 4 * |C₀| * (5 + ε / 5) := mul_nonneg (by positivity) (by linarith)
  have a1 := abs_nonneg (4 * Real.log (4 * (|A₀| + 1)) / c₃)
  have a2 := abs_nonneg (4 * Real.log (4 * (|A₀| + 1)) ^ 2 / c₃)
  have a3 := abs_nonneg (Real.log (320 / min c0 1))
  have hl320 : 320 ≤ Real.log x := by linarith
  have hx1 : 1 ≤ x := by
    have h := Real.add_one_le_exp (Real.log x)
    rw [Real.exp_log hxpos] at h
    linarith
  have hlC : 4 * |C₀| * (5 + ε / 5) ≤ Real.log x := by linarith
  have hlK1 : 4 * Real.log (4 * (|A₀| + 1)) / c₃ ≤ Real.log x := by
    linarith [le_abs_self (4 * Real.log (4 * (|A₀| + 1)) / c₃)]
  have hlK2 : 4 * Real.log (4 * (|A₀| + 1)) ^ 2 / c₃ ≤ Real.log x := by
    linarith [le_abs_self (4 * Real.log (4 * (|A₀| + 1)) ^ 2 / c₃)]
  have hlc : |Real.log (320 / min c0 1)| ≤ Real.log x := by linarith
  obtain ⟨e, he1, -, he3⟩ := hPM m₀ h8
  have hcb : ∀ (χ : DirichletCharacter ℂ m₀) (β : ℝ), χ ^ 2 = 1 → χ ≠ 1 →
      DirichletCharacter.LFunction χ (β : ℂ) = 0 → β ≤ 1 - min c0 1 * (m₀ : ℝ) ^ (-1 : ℝ) := by
    intro χ β h1' h2' h3'
    have h := hcb0 m₀ χ β h1' h2' h3'
    have hpow : 0 ≤ (m₀ : ℝ) ^ (-1 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    nlinarith [mul_le_mul_of_nonneg_right (min_le_left c0 1) hpow]
  by_cases hpos : 0 < X
  · exact count_pos hc₃ hcpos hc1 hε h8 a₀ hcop e he1 he3 hcb x X hx1 hl320 hlC hlK1 hlK2 hlc h1 h3 hpos
  · have hXle : X ≤ 0 := not_lt.mp hpos
    rcases hXle.lt_or_eq with hneg | hzero
    · have hcard : (0:ℝ) ≤ ((PPset m₀ a₀ X).card : ℝ) := Nat.cast_nonneg _
      rw [Real.rpow_def_of_neg hneg]
      have hcos : Real.cos (9 / 10 * Real.pi) ≤ 0 :=
        Real.cos_nonpos_of_pi_div_two_le_of_le (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
      nlinarith [Real.exp_pos (Real.log X * (9 / 10))]
    · subst hzero
      rw [Real.zero_rpow (by norm_num)]
      exact Nat.cast_nonneg _

end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
