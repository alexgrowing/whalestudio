import Formalism.HermitianCurvature.LevelRecursionCondNeeded

namespace Formalism.FourierDecayAlt.P.ProductFactorBounds

open Formalism.FourierDecayAlt.F7

theorem letter_ratio {K : Type} [Field K] (l : WLetter K) (Y : K) (h : OffPoles l Y) :
    (if l.plus then (Y - l.pt + 1) / (Y - l.pt) else (l.pt - Y) / (l.pt - Y - 1)) /
      (if l.first then
        (if l.plus then (Y + 1 - l.pt) / (Y + 1 - l.pt - 1)
          else (l.pt - (Y + 1)) / (l.pt - (Y + 1) - 1)) else 1) = wFactor l Y := by
  obtain ⟨p, t, f⟩ := l
  cases p <;> cases f
  · simp [wFactor]
  · have h' : t - Y ≠ 1 ∧ t - Y ≠ 2 := by simpa [OffPoles] using h
    have h1 : t - Y - 1 ≠ 0 := sub_ne_zero.2 h'.1
    have h2 : t - (Y + 1) ≠ 0 := by
      intro e; apply h1; rw [← e]; ring
    have h3 : t - (Y + 1) - 1 ≠ 0 := by
      intro e; apply h'.2; linear_combination e
    simp only [wFactor, if_true, Bool.false_eq_true, if_false]
    field_simp
    ring
  · simp [wFactor]
  · have h' : Y - t ≠ 0 ∧ Y - t ≠ -1 := by simpa [OffPoles] using h
    have h1 : Y - t + 1 ≠ 0 := by
      intro e; apply h'.2; linear_combination e
    have h4 : Y - t ≠ 0 := h'.1
    simp only [wFactor, if_true]
    have e1 : Y + 1 - t = Y - t + 1 := by ring
    have e2 : Y + 1 - t - 1 = Y - t := by ring
    rw [e2, e1]
    exact div_self (div_ne_zero h1 h4)

theorem prod_bounds (a b : ℝ) (ha1 : a ≤ 1) (hb : 0 ≤ b) (L : List ℝ)
    (h : ∀ f ∈ L, 1 - a ≤ f ∧ f ≤ 1 + b) :
    (1 - a) ^ L.length ≤ L.prod ∧ L.prod ≤ (1 + b) ^ L.length := by
  induction L with
  | nil => simp
  | cons f L ih =>
    have hf := h f (by simp)
    have hL := ih (fun g hg => h g (by simp [hg]))
    have h0 : 0 ≤ 1 - a := by linarith
    have h1 : 0 ≤ (1 - a) ^ L.length := pow_nonneg h0 _
    have h2 : 0 ≤ L.prod := le_trans h1 hL.1
    have h3 : 0 ≤ f := le_trans h0 hf.1
    simp only [List.length_cons, List.prod_cons, pow_succ']
    exact ⟨mul_le_mul hf.1 hL.1 h1 h3, mul_le_mul hf.2 hL.2 h2 (by linarith)⟩

theorem one_add_pow_le (u : ℝ) (hu : 0 ≤ u) (k : ℕ) (hk : (k : ℝ) * u ≤ 1) :
    (1 + u) ^ k ≤ 1 + k * u + (k * u) ^ 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk' : (k : ℝ) * u ≤ 1 := by
      push_cast at hk; nlinarith
    have h := ih hk'
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    rw [pow_succ]
    push_cast
    have h1 : (1 + u) ^ k * (1 + u) ≤ (1 + k * u + (k * u) ^ 2) * (1 + u) :=
      mul_le_mul_of_nonneg_right h (by linarith)
    have h2 : (k : ℝ) * u * (k * u ^ 2) ≤ 1 * (k * u ^ 2) :=
      mul_le_mul_of_nonneg_right hk' (by positivity)
    nlinarith [sq_nonneg u]

theorem factor_bounds (N : ℝ) (hN : 2 ≤ N) (l : WLetter ℝ) (Y : ℝ) (h : N ^ 2 ≤ |Y - l.pt|) :
    1 - 1 / N ^ 2 ≤ wFactor l Y ∧ wFactor l Y ≤ 1 + 1 / (N ^ 2 - 1) := by
  obtain ⟨p, t, f⟩ := l
  have hN2 : 4 ≤ N ^ 2 := by nlinarith
  have hN2p : 0 < N ^ 2 := by linarith
  have hpos : 0 < N ^ 2 - 1 := by linarith
  have e1 : 0 ≤ 1 / N ^ 2 := (one_div_pos.2 hN2p).le
  have e2 : 0 ≤ 1 / (N ^ 2 - 1) := (one_div_pos.2 hpos).le
  have e3 : 1 / N ^ 2 ≤ 1 / (N ^ 2 - 1) := one_div_le_one_div_of_le hpos (by linarith)
  replace h : N ^ 2 ≤ |Y - t| := h
  cases p <;> cases f <;> simp only [wFactor, if_true, Bool.false_eq_true, if_false]
  · rcases le_abs.1 h with h | h
    · have hx : 0 < Y - t + 1 := by linarith
      have hne : t - Y - 1 ≠ 0 := by
        intro e; linarith
      have e : (t - Y) / (t - Y - 1) = 1 - 1 / (Y - t + 1) := by
        field_simp
        ring
      have b1 : 1 / (Y - t + 1) ≤ 1 / N ^ 2 := one_div_le_one_div_of_le hN2p (by linarith)
      have b2 : 0 ≤ 1 / (Y - t + 1) := (one_div_pos.2 hx).le
      rw [e]
      constructor <;> linarith
    · have hx : 0 < t - Y - 1 := by linarith
      have e : (t - Y) / (t - Y - 1) = 1 + 1 / (t - Y - 1) := by
        field_simp
        ring
      have b1 : 1 / (t - Y - 1) ≤ 1 / (N ^ 2 - 1) := one_div_le_one_div_of_le hpos (by linarith)
      have b2 : 0 ≤ 1 / (t - Y - 1) := (one_div_pos.2 hx).le
      rw [e]
      constructor <;> linarith
  · have hsq : N ^ 2 ≤ (t - Y - 1) ^ 2 := by
      rcases le_abs.1 h with h | h
      · nlinarith
      · nlinarith
    have b1 : 1 / (t - Y - 1) ^ 2 ≤ 1 / N ^ 2 := one_div_le_one_div_of_le hN2p hsq
    have b2 : 0 ≤ 1 / (t - Y - 1) ^ 2 := by positivity
    constructor <;> linarith
  · rcases le_abs.1 h with h | h
    · have hx : 0 < Y - t := by linarith
      have e : (Y - t + 1) / (Y - t) = 1 + 1 / (Y - t) := by
        field_simp
      have b1 : 1 / (Y - t) ≤ 1 / N ^ 2 := one_div_le_one_div_of_le hN2p h
      have b2 : 0 ≤ 1 / (Y - t) := (one_div_pos.2 hx).le
      rw [e]
      constructor <;> linarith
    · have hx : 0 < t - Y := by linarith
      have hne : Y - t ≠ 0 := by
        intro e; linarith
      have e : (Y - t + 1) / (Y - t) = 1 - 1 / (t - Y) := by
        field_simp
        ring
      have b1 : 1 / (t - Y) ≤ 1 / N ^ 2 := one_div_le_one_div_of_le hN2p (by linarith)
      have b2 : 0 ≤ 1 / (t - Y) := (one_div_pos.2 hx).le
      rw [e]
      constructor <;> linarith
  · constructor <;> linarith

theorem factor_bounds_first (N : ℝ) (hN : 2 ≤ N) (l : WLetter ℝ) (Y : ℝ)
    (h : N ^ 2 ≤ |Y - l.pt|) (hf : l.first = true) :
    1 - 1 / (N ^ 2 - 1) ^ 2 ≤ wFactor l Y ∧ wFactor l Y ≤ 1 + 0 := by
  obtain ⟨p, t, f⟩ := l
  have hN2 : 4 ≤ N ^ 2 := by nlinarith
  have hpos : 0 < N ^ 2 - 1 := by linarith
  have hpos2 : 0 < (N ^ 2 - 1) ^ 2 := by positivity
  have e1 : 0 ≤ 1 / (N ^ 2 - 1) ^ 2 := (one_div_pos.2 hpos2).le
  replace h : N ^ 2 ≤ |Y - t| := h
  replace hf : f = true := hf
  subst hf
  cases p <;> simp only [wFactor, if_true, Bool.false_eq_true, if_false]
  · have hsq : (N ^ 2 - 1) ^ 2 ≤ (t - Y - 1) ^ 2 := by
      rcases le_abs.1 h with h | h
      · have : (t - Y - 1) ^ 2 = (Y - t + 1) ^ 2 := by ring
        rw [this]
        exact pow_le_pow_left₀ hpos.le (by linarith) 2
      · exact pow_le_pow_left₀ hpos.le (by linarith) 2
    have b1 : 1 / (t - Y - 1) ^ 2 ≤ 1 / (N ^ 2 - 1) ^ 2 := one_div_le_one_div_of_le hpos2 hsq
    have b2 : 0 ≤ 1 / (t - Y - 1) ^ 2 := by positivity
    constructor <;> linarith
  · constructor <;> linarith

end Formalism.FourierDecayAlt.P.ProductFactorBounds

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.F7 Formalism.FourierDecayAlt.P.ProductFactorBounds

theorem word_weight_formula : Formalism.FourierDecayAlt.F7.WordWeight := by
  intro K _ q x w Y h
  induction w with
  | nil => simp [qW, xW]
  | cons l w ih =>
    have hl := letter_ratio l Y (h l (by simp))
    have hw := ih (fun g hg => h g (by simp [hg]))
    simp only [qW, xW, List.map_cons, List.prod_cons]
    rw [mul_div_mul_comm, hw, hl]
    ring

theorem all_first_level_weight : Formalism.FourierDecayAlt.F7.AllFirstWeight := by
  intro K _ q x w Y h hp
  rw [word_weight_formula K q x w Y h]
  congr 1
  clear h
  induction w with
  | nil => simp
  | cons l w ih =>
    have hw := ih (fun g hg => hp g (by simp [hg]))
    have hl : l.first = true := hp l (by simp)
    cases hpl : l.plus
    · have e : wFactor l Y = 1 - 1 / (l.pt - Y - 1) ^ 2 := by simp [wFactor, hpl, hl]
      rw [List.map_cons, List.prod_cons, hw, e, List.filter_cons_of_pos (by simp [hpl]),
        List.map_cons, List.prod_cons]
    · have e : wFactor l Y = 1 := by simp [wFactor, hpl, hl]
      rw [List.map_cons, List.prod_cons, hw, e, one_mul, List.filter_cons_of_neg (by simp [hpl])]

theorem word_weight_bounds : Formalism.FourierDecayAlt.F7.WeightBounds := by
  intro N w Y hN hlen h
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hN2 : (4 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
  have hN2p : (0 : ℝ) < (N : ℝ) ^ 2 := by linarith
  have hpos : (0 : ℝ) < (N : ℝ) ^ 2 - 1 := by linarith
  have hlenr : (w.length : ℝ) ≤ N := by exact_mod_cast hlen
  have a1 : 1 / (N : ℝ) ^ 2 ≤ 1 := by
    rw [div_le_one hN2p]; linarith
  have a0 : 0 ≤ 1 / (N : ℝ) ^ 2 := (one_div_pos.2 hN2p).le
  have u0 : 0 ≤ 1 / ((N : ℝ) ^ 2 - 1) := (one_div_pos.2 hpos).le
  obtain ⟨lo, hi⟩ := prod_bounds (1 / (N : ℝ) ^ 2) (1 / ((N : ℝ) ^ 2 - 1)) a1 u0
    (w.map fun l => wFactor l Y) (by
      intro f hf
      obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hf
      exact factor_bounds N hNr l Y (h l hl))
  rw [List.length_map] at lo hi
  constructor
  · refine le_trans ?_ lo
    have hb := one_add_mul_le_pow (a := -(1 / (N : ℝ) ^ 2)) (by linarith) w.length
    have e : (1 : ℝ) + -(1 / (N : ℝ) ^ 2) = 1 - 1 / (N : ℝ) ^ 2 := by ring
    rw [e] at hb
    refine le_trans ?_ hb
    have h1 : (w.length : ℝ) * (1 / (N : ℝ) ^ 2) ≤ N * (1 / (N : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right hlenr a0
    have h2 : (N : ℝ) * (1 / (N : ℝ) ^ 2) = 1 / N := by
      field_simp
    linarith
  · refine le_trans hi ?_
    have h1 : (1 + 1 / ((N : ℝ) ^ 2 - 1)) ^ w.length ≤ (1 + 1 / ((N : ℝ) ^ 2 - 1)) ^ N :=
      pow_le_pow_right₀ (by linarith) hlen
    refine le_trans h1 ?_
    have t1 : (N : ℝ) * (1 / ((N : ℝ) ^ 2 - 1)) ≤ 2 / 3 := by
      rw [mul_one_div, div_le_iff₀ hpos]; nlinarith
    have t2 : (N : ℝ) * (1 / ((N : ℝ) ^ 2 - 1)) ≤ (4 / 3) / N := by
      rw [mul_one_div, div_le_div_iff₀ hpos hN0]; nlinarith
    have t0 : 0 ≤ (N : ℝ) * (1 / ((N : ℝ) ^ 2 - 1)) := mul_nonneg hN0.le u0
    have h2 := one_add_pow_le (1 / ((N : ℝ) ^ 2 - 1)) u0 N (by linarith)
    refine le_trans h2 ?_
    have h3 : ((N : ℝ) * (1 / ((N : ℝ) ^ 2 - 1))) ^ 2 ≤ (2 / 3) * ((4 / 3) / N) := by
      rw [sq]
      exact mul_le_mul t1 t2 t0 (by norm_num)
    have h4 : (3 : ℝ) / N = (4 / 3) / N + (2 / 3) * ((4 / 3) / N) + (7 / 9) / N := by
      field_simp
      norm_num
    have h5 : (0 : ℝ) ≤ (7 / 9) / N := by positivity
    linarith

theorem all_first_level_bounds : Formalism.FourierDecayAlt.F7.AllFirstBounds := by
  intro N w Y hN hlen h hfirst
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hN2 : (4 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
  have hpos : (0 : ℝ) < (N : ℝ) ^ 2 - 1 := by linarith
  have hpos2 : (0 : ℝ) < ((N : ℝ) ^ 2 - 1) ^ 2 := by positivity
  have hlenr : (w.length : ℝ) ≤ N := by exact_mod_cast hlen
  have a0 : 0 ≤ 1 / ((N : ℝ) ^ 2 - 1) ^ 2 := (one_div_pos.2 hpos2).le
  have a1 : 1 / ((N : ℝ) ^ 2 - 1) ^ 2 ≤ 1 := by
    rw [div_le_one hpos2]; nlinarith
  obtain ⟨lo, hi⟩ := prod_bounds (1 / ((N : ℝ) ^ 2 - 1) ^ 2) 0 a1 le_rfl
    (w.map fun l => wFactor l Y) (by
      intro f hf
      obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hf
      exact factor_bounds_first N hNr l Y (h l hl) (hfirst l hl))
  rw [List.length_map] at lo hi
  constructor
  · refine le_trans ?_ lo
    have hb := one_add_mul_le_pow (a := -(1 / ((N : ℝ) ^ 2 - 1) ^ 2)) (by linarith) w.length
    have e : (1 : ℝ) + -(1 / ((N : ℝ) ^ 2 - 1) ^ 2) = 1 - 1 / ((N : ℝ) ^ 2 - 1) ^ 2 := by ring
    rw [e] at hb
    refine le_trans ?_ hb
    have h1 : (w.length : ℝ) * (1 / ((N : ℝ) ^ 2 - 1) ^ 2) ≤ N * (1 / ((N : ℝ) ^ 2 - 1) ^ 2) :=
      mul_le_mul_of_nonneg_right hlenr a0
    have h2 : (N : ℝ) * (1 / ((N : ℝ) ^ 2 - 1) ^ 2) ≤ 2 / (N : ℝ) ^ 3 := by
      rw [mul_one_div, div_le_div_iff₀ hpos2 (by positivity)]
      nlinarith [mul_nonneg (sub_nonneg.2 hN2) (sub_nonneg.2 hN2)]
    linarith
  · simpa using hi

end Formalism.FourierDecayAlt.P
