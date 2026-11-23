import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.RingHomPointBijective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormXLeOneOfNsmulEqZero

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.TorsionReduction

open IsUltrametricDist WeierstrassCurve GlobalTheory.TorsionIntegral

section General

variable {K : Type} [NormedField K] [IsUltrametricDist K]

def intRing (K : Type) [NormedField K] [IsUltrametricDist K] : Subring K where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq, norm_mul] at *
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' := fun {a b} ha hb => (norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' := fun {a} ha => by simpa using ha

lemma norm_mul_le_of_mem {a b : K} (hb : b ∈ intRing K) : ‖a * b‖ ≤ ‖a‖ := by
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) hb

lemma quad_le {y b r : K} {C : ℝ} (h : y ^ 2 + b * y = r) (hb : ‖b‖ ^ 2 ≤ C) (hr : ‖r‖ ≤ C) :
    ‖y‖ ^ 2 ≤ C := by
  rcases le_or_gt ‖y‖ ‖b‖ with hy | hy
  · exact (pow_le_pow_left₀ (norm_nonneg _) hy 2).trans hb
  · have : ‖r‖ = ‖y‖ ^ 2 := by
      rw [← h, show y ^ 2 + b * y = y * (y + b) by ring, norm_mul, norm_add_eq_of_lt hy, sq]
    exact this ▸ hr

lemma quad_eq {y b r : K} (h : y ^ 2 + b * y = r) (hb : ‖b‖ ^ 2 < ‖r‖) : ‖y‖ ^ 2 = ‖r‖ := by
  rcases le_or_gt ‖y‖ ‖b‖ with hy | hy
  · exfalso
    have h1 : ‖y + b‖ ≤ ‖b‖ := (norm_add_le_max _ _).trans (max_le hy le_rfl)
    have : ‖r‖ ≤ ‖b‖ * ‖b‖ := by
      rw [← h, show y ^ 2 + b * y = y * (y + b) by ring, norm_mul]
      gcongr
    nlinarith
  · rw [← h, show y ^ 2 + b * y = y * (y + b) by ring, norm_mul, norm_add_eq_of_lt hy, sq]

lemma quad_mem {y b r : K} (h : y ^ 2 + b * y = r) (hb : b ∈ intRing K) (hr : r ∈ intRing K) :
    y ∈ intRing K := by
  have hb' : ‖b‖ ≤ 1 := hb
  have := quad_le (C := 1) h (pow_le_one₀ (norm_nonneg _) hb') hr
  show ‖y‖ ≤ 1
  nlinarith [norm_nonneg y]

lemma norm_lin_le {a c x : K} (ha : ‖a‖ ≤ 1) (hc : ‖c‖ ≤ 1) (hx : 1 < ‖x‖) :
    ‖a * x + c‖ ≤ ‖x‖ := by
  refine (norm_add_le_max _ _).trans (max_le ?_ (by linarith))
  rw [mul_comm]
  exact norm_mul_le_of_mem ha

lemma norm_cubic {a₂ a₄ a₆ x : K} (h₂ : ‖a₂‖ ≤ 1) (h₄ : ‖a₄‖ ≤ 1) (h₆ : ‖a₆‖ ≤ 1)
    (hx : 1 < ‖x‖) : ‖x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆‖ = ‖x‖ ^ 3 := by
  have h1 : ‖(a₂ * x + a₄) * x + a₆‖ < ‖x ^ 3‖ := by
    have := norm_lin_le h₂ h₄ hx
    have h3 : ‖x‖ * ‖x‖ < ‖x‖ ^ 3 := by
      have := pow_lt_pow_right₀ hx (show 2 < 3 by norm_num)
      rwa [sq] at this
    rw [norm_pow]
    refine (norm_add_le_max _ _).trans_lt (max_lt ?_ (by nlinarith))
    rw [norm_mul]
    exact lt_of_le_of_lt (by gcongr) h3
  rw [← norm_pow, ← norm_add_eq_of_lt h1]
  congr 1
  ring

lemma norm_y_sq' {a₁ a₂ a₃ a₄ a₆ x y : K} (h₁ : ‖a₁‖ ≤ 1) (h₂ : ‖a₂‖ ≤ 1) (h₃ : ‖a₃‖ ≤ 1)
    (h₄ : ‖a₄‖ ≤ 1) (h₆ : ‖a₆‖ ≤ 1) (hx : 1 < ‖x‖)
    (h : y ^ 2 + a₁ * x * y + a₃ * y = x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆) :
    ‖y‖ ^ 2 = ‖x‖ ^ 3 := by
  rw [← norm_cubic h₂ h₄ h₆ hx]
  refine quad_eq (b := a₁ * x + a₃) (by linear_combination h) ?_
  rw [norm_cubic h₂ h₄ h₆ hx]
  exact (pow_le_pow_left₀ (norm_nonneg _) (norm_lin_le h₁ h₃ hx) 2).trans_lt
    (pow_lt_pow_right₀ hx (by norm_num))

lemma neg_param {a₁ a₂ a₃ a₄ a₆ x y : K} {M : ℝ} (h₁ : ‖a₁‖ ≤ 1) (h₂ : ‖a₂‖ ≤ 1) (h₃ : ‖a₃‖ ≤ 1)
    (h₄ : ‖a₄‖ ≤ 1) (h₆ : ‖a₆‖ ≤ 1) (hM : 1 < M) (hx : M ≤ ‖x‖)
    (h : y ^ 2 + a₁ * x * y + a₃ * y = x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆) :
    ‖x / y + x / (-y - a₁ * x - a₃)‖ ≤ M⁻¹ := by
  have hx1 : 1 < ‖x‖ := by linarith
  have hn : ‖y * (-y - a₁ * x - a₃)‖ = ‖x‖ ^ 3 := by
    rw [← norm_cubic h₂ h₄ h₆ hx1, ← h, ← norm_neg]
    congr 1
    ring
  have x0 : 0 < ‖x‖ := by linarith
  have h0 : y * (-y - a₁ * x - a₃) ≠ 0 := by
    rw [← norm_pos_iff, hn]; positivity
  rw [div_add_div _ _ (left_ne_zero_of_mul h0) (right_ne_zero_of_mul h0), norm_div, hn,
    show x * (-y - a₁ * x - a₃) + y * x = -(x * (a₁ * x + a₃)) by ring, norm_neg, norm_mul]
  have := norm_lin_le h₁ h₃ hx1
  calc _ ≤ ‖x‖ * ‖x‖ / ‖x‖ ^ 3 := by gcongr
    _ = ‖x‖⁻¹ := by field_simp
    _ ≤ M⁻¹ := by gcongr

lemma third_big {a₁ a₂ a₃ a₄ a₆ x₁ x₂ x₃ l n : K} (h₁ : ‖a₁‖ ≤ 1) (h₂ : ‖a₂‖ ≤ 1)
    (h₃ : ‖a₃‖ ≤ 1) (h₄ : ‖a₄‖ ≤ 1) (h₆ : ‖a₆‖ ≤ 1)
    (e1 : x₁ + x₂ + x₃ = l ^ 2 + a₁ * l - a₂)
    (e2 : x₁ * x₂ + x₁ * x₃ + x₂ * x₃ = a₄ - 2 * l * n - a₁ * n - a₃ * l)
    (e3 : x₁ * x₂ * x₃ = n ^ 2 + a₃ * n - a₆) (h12 : ‖x₂‖ ≤ ‖x₁‖) (h2 : 1 < ‖x₂‖) :
    ‖x₂‖ ≤ ‖x₃‖ := by
  by_contra hc
  push Not at hc
  set a := ‖x₁‖ with ha
  set b := ‖x₂‖ with hb
  set c := ‖x₃‖ with hc'
  have c0 : 0 ≤ c := norm_nonneg _
  have hl : ‖l‖ ^ 2 ≤ a := by
    refine quad_le (b := a₁) (r := x₁ + x₂ + x₃ + a₂) (by linear_combination -e1)
      ((pow_le_one₀ (norm_nonneg _) h₁).trans (by linarith)) ?_
    refine (norm_add_le_max _ _).trans (max_le ?_ (by linarith))
    exact (norm_sum_three_le _ _ _).trans (max_le (max_le le_rfl h12) (by linarith))
  have hn : ‖n‖ ^ 2 ≤ max (a * b * c) 1 := by
    refine quad_le (b := a₃) (r := x₁ * x₂ * x₃ + a₆) (by linear_combination -e3)
      ((pow_le_one₀ (norm_nonneg _) h₃).trans (le_max_right _ _)) ?_
    refine (norm_add_le_max _ _).trans (max_le_max ?_ h₆)
    rw [norm_mul, norm_mul]
  obtain ⟨L, L1, Ll, hL⟩ : ∃ L : ℝ, 1 ≤ L ∧ ‖l‖ ≤ L ∧ L ^ 2 ≤ a := by
    rcases le_total ‖l‖ 1 with h | h
    · exact ⟨1, le_rfl, h, by linarith⟩
    · exact ⟨_, h, le_rfl, hl⟩
  obtain ⟨N, N1, Nn, hN⟩ : ∃ N : ℝ, 1 ≤ N ∧ ‖n‖ ≤ N ∧ N ^ 2 ≤ max (a * b * c) 1 := by
    rcases le_total ‖n‖ 1 with h | h
    · exact ⟨1, le_rfl, h, by simp⟩
    · exact ⟨_, h, le_rfl, hn⟩
  have hab : a * b ≤ L * N := by
    have h1 : ‖x₁ * x₂ + x₁ * x₃ + x₂ * x₃‖ = a * b := by
      rw [add_assoc, norm_add_eq_of_lt, norm_mul]
      refine (norm_add_le_max _ _).trans_lt (max_lt ?_ ?_) <;> rw [norm_mul, norm_mul] <;>
        nlinarith
    have t1 : ‖l * n * 2‖ ≤ ‖l * n‖ := norm_mul_le_of_mem norm_two_le
    have t2 : ‖n * a₁‖ ≤ ‖n‖ := norm_mul_le_of_mem h₁
    have t3 : ‖l * a₃‖ ≤ ‖l‖ := norm_mul_le_of_mem h₃
    have t4 : ‖l * n‖ ≤ L * N := by rw [norm_mul]; gcongr
    rw [← h1, e2, show a₄ - 2 * l * n - a₁ * n - a₃ * l = a₄ - (l * n * 2 + n * a₁ + l * a₃) by ring]
    refine (norm_sub_le_max' _ _).trans (max_le (by nlinarith) ?_)
    refine (norm_sum_three_le _ _ _).trans (max_le (max_le ?_ ?_) ?_) <;> nlinarith
  have hab1 : 1 < a * b := by nlinarith
  have h4 : (a * b) ^ 2 ≤ a * max (a * b * c) 1 := by
    calc (a * b) ^ 2 ≤ (L * N) ^ 2 := by gcongr
      _ = L ^ 2 * N ^ 2 := by ring
      _ ≤ _ := by gcongr
  have a0 : 0 < a := by linarith
  have h5 : max (a * b * c) 1 < a * b * b := by
    refine max_lt ?_ ?_
    · exact mul_lt_mul_of_pos_left hc (by linarith)
    · nlinarith
  have := mul_lt_mul_of_pos_left h5 a0
  nlinarith

lemma mul_pow_two_le_triple_prod_of_ge {a b c M : ℝ} (hM : 1 < M) (ha : M ≤ a) (hb : M ≤ b) (hc : M ≤ c) :
    a * M ^ 2 ≤ a * b * c := by
  have a0 : 0 ≤ a := by linarith
  have : M * M ≤ b * c := mul_le_mul hb hc (by linarith) (by linarith)
  nlinarith

lemma chord {a₁ a₂ a₃ a₄ a₆ x₁ x₂ x₃ y₁ y₂ y₃ l n : K} {M : ℝ} (h₁ : ‖a₁‖ ≤ 1) (h₂ : ‖a₂‖ ≤ 1)
    (h₃ : ‖a₃‖ ≤ 1) (h₄ : ‖a₄‖ ≤ 1) (h₆ : ‖a₆‖ ≤ 1) (hM : 1 < M)
    (e1 : x₁ + x₂ + x₃ = l ^ 2 + a₁ * l - a₂)
    (e2 : x₁ * x₂ + x₁ * x₃ + x₂ * x₃ = a₄ - 2 * l * n - a₁ * n - a₃ * l)
    (e3 : x₁ * x₂ * x₃ = n ^ 2 + a₃ * n - a₆) (hy₁ : y₁ = l * x₁ + n) (hy₂ : y₂ = l * x₂ + n)
    (hy₃ : y₃ = l * x₃ + n) (h1 : M ≤ ‖x₁‖) (h2 : M ≤ ‖x₂‖) :
    M ≤ ‖x₃‖ ∧ ‖x₁ / y₁ + x₂ / y₂ + x₃ / y₃‖ ≤ M⁻¹ := by
  have h3 : M ≤ ‖x₃‖ := by
    rcases le_total ‖x₂‖ ‖x₁‖ with h | h
    · exact h2.trans (third_big h₁ h₂ h₃ h₄ h₆ e1 e2 e3 h (by linarith))
    · exact h1.trans (third_big (x₁ := x₂) (x₂ := x₁) (l := l) (n := n) h₁ h₂ h₃ h₄ h₆
        (by linear_combination e1) (by linear_combination e2) (by linear_combination e3) h
        (by linarith))
  refine ⟨h3, ?_⟩
  have q1 : y₁ ^ 2 + a₁ * x₁ * y₁ + a₃ * y₁ = x₁ ^ 3 + a₂ * x₁ ^ 2 + a₄ * x₁ + a₆ := by
    rw [hy₁]; linear_combination (-x₁ ^ 2) * e1 + x₁ * e2 - e3
  have q2 : y₂ ^ 2 + a₁ * x₂ * y₂ + a₃ * y₂ = x₂ ^ 3 + a₂ * x₂ ^ 2 + a₄ * x₂ + a₆ := by
    rw [hy₂]; linear_combination (-x₂ ^ 2) * e1 + x₂ * e2 - e3
  have q3 : y₃ ^ 2 + a₁ * x₃ * y₃ + a₃ * y₃ = x₃ ^ 3 + a₂ * x₃ ^ 2 + a₄ * x₃ + a₆ := by
    rw [hy₃]; linear_combination (-x₃ ^ 2) * e1 + x₃ * e2 - e3
  have n1 := norm_y_sq' h₁ h₂ h₃ h₄ h₆ (by linarith) q1
  have n2 := norm_y_sq' h₁ h₂ h₃ h₄ h₆ (by linarith) q2
  have n3 := norm_y_sq' h₁ h₂ h₃ h₄ h₆ (by linarith) q3
  set a := ‖x₁‖ with ha
  set b := ‖x₂‖ with hb
  set c := ‖x₃‖ with hc
  have M0 : 0 < M := by linarith
  have p1 := mul_pow_two_le_triple_prod_of_ge hM h1 h2 h3
  have p2 : b * M ^ 2 ≤ a * b * c := by have := mul_pow_two_le_triple_prod_of_ge hM h2 h1 h3; linarith
  have p3 : c * M ^ 2 ≤ a * b * c := by have := mul_pow_two_le_triple_prod_of_ge hM h3 h1 h2; linarith
  have hM2 : 1 < M ^ 2 := by nlinarith
  have habc : M ^ 2 ≤ a * b * c := by nlinarith
  have hr : ‖x₁ * x₂ * x₃ + a₆‖ = a * b * c := by
    rw [norm_add_eq_of_lt, norm_mul, norm_mul]
    rw [norm_mul, norm_mul]
    linarith
  have hn : ‖n‖ ^ 2 = a * b * c := by
    rw [← hr]
    refine quad_eq (b := a₃) (by linear_combination -e3) ?_
    rw [hr]
    exact (pow_le_one₀ (norm_nonneg _) h₃).trans_lt (by linarith)
  have hl : ‖l‖ * M ≤ ‖n‖ := by
    refine (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).1 ?_
    rw [hn, mul_pow, ← le_div_iff₀ (by positivity)]
    have u1 : a ≤ a * b * c / M ^ 2 := by rwa [le_div_iff₀ (by positivity)]
    have u2 : b ≤ a * b * c / M ^ 2 := by rwa [le_div_iff₀ (by positivity)]
    have u3 : c ≤ a * b * c / M ^ 2 := by rwa [le_div_iff₀ (by positivity)]
    refine quad_le (b := a₁) (r := x₁ + x₂ + x₃ + a₂) (by linear_combination -e1)
      ((pow_le_one₀ (norm_nonneg _) h₁).trans (by linarith)) ?_
    refine (norm_add_le_max _ _).trans (max_le ?_ (by linarith))
    exact (norm_sum_three_le _ _ _).trans (max_le (max_le u1 u2) u3)
  have hMn : M ≤ ‖n‖ := by
    refine (pow_le_pow_iff_left₀ (by linarith) (norm_nonneg _) two_ne_zero).1 ?_
    rw [hn]; exact habc
  have hyy : ‖y₁ * y₂ * y₃‖ = ‖n‖ ^ 3 := by
    refine (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
    rw [norm_mul, norm_mul, mul_pow, mul_pow, n1, n2, n3, ← pow_mul, mul_comm 3 2, pow_mul, hn]
    ring
  have n0 : 0 < ‖n‖ := by linarith
  have n0' : n ≠ 0 := norm_pos_iff.1 n0
  have hy0 : y₁ * y₂ * y₃ ≠ 0 := by
    rw [← norm_pos_iff, hyy]; positivity
  have y1 : y₁ ≠ 0 := fun h => hy0 (by simp [h])
  have y2 : y₂ ≠ 0 := fun h => hy0 (by simp [h])
  have y3 : y₃ ≠ 0 := fun h => hy0 (by simp [h])
  have hS : x₁ * y₂ * y₃ + y₁ * x₂ * y₃ + y₁ * y₂ * x₃ =
      a₃ * l ^ 2 * n - 3 * a₆ * l ^ 2 + 2 * a₄ * l * n - a₁ * l * n ^ 2 - a₂ * n ^ 2 := by
    rw [hy₁, hy₂, hy₃]
    linear_combination n ^ 2 * e1 + 2 * l * n * e2 + 3 * l ^ 2 * e3
  have k1 : ‖l / n‖ ≤ M⁻¹ := by
    rw [norm_div, inv_eq_one_div, div_le_div_iff₀ n0 M0]; linarith
  have k2 : ‖n⁻¹‖ ≤ M⁻¹ := by rw [norm_inv]; gcongr
  have Mi : M⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hM.le
  have m1 : l / n ∈ intRing K := k1.trans Mi
  have m₁ : a₁ ∈ intRing K := h₁
  have m₂ : a₂ ∈ intRing K := h₂
  have m₃ : a₃ ∈ intRing K := h₃
  have m₄ : a₄ ∈ intRing K := h₄
  have m₆ : a₆ ∈ intRing K := h₆
  have hq : x₁ / y₁ + x₂ / y₂ + x₃ / y₃ = n ^ 3 / (y₁ * y₂ * y₃) *
      (l / n * (a₃ * (l / n) - a₁) + n⁻¹ * (2 * a₄ * (l / n) - 3 * a₆ * (l / n) ^ 2 - a₂)) := by
    have : n ^ 3 * (l / n * (a₃ * (l / n) - a₁) +
        n⁻¹ * (2 * a₄ * (l / n) - 3 * a₆ * (l / n) ^ 2 - a₂)) =
        x₁ * y₂ * y₃ + y₁ * x₂ * y₃ + y₁ * y₂ * x₃ := by
      rw [hS]; field_simp; ring
    rw [div_mul_eq_mul_div, this]; field_simp
  rw [hq, norm_mul, norm_div, hyy, norm_pow, div_self (by positivity), one_mul]
  refine (norm_add_le_max _ _).trans (max_le ((norm_mul_le_of_mem ?_).trans k1)
    ((norm_mul_le_of_mem ?_).trans k2))
  · exact sub_mem (mul_mem m₃ m1) m₁
  · exact sub_mem (sub_mem (mul_mem (mul_mem norm_two_le m₄) m1)
      (mul_mem (mul_mem norm_three_le m₆) (pow_mem m1 _))) m₂

lemma add_step' [DecidableEq K] {W : Affine K} {M : ℝ} (h₁ : ‖W.a₁‖ ≤ 1) (h₂ : ‖W.a₂‖ ≤ 1)
    (h₃ : ‖W.a₃‖ ≤ 1) (h₄ : ‖W.a₄‖ ≤ 1) (h₆ : ‖W.a₆‖ ≤ 1) (hM : 1 < M)
    (P Q : W.Point) (hP : Near M P)
    (hQ : Near M Q) : Near M (P + Q) ∧ ‖param (P + Q) - param P - param Q‖ ≤ M⁻¹ := by
  have M0 : 0 ≤ M⁻¹ := inv_nonneg.2 (by linarith)
  rcases P with _ | ⟨x₁, y₁, k₁⟩
  · rw [← Affine.Point.zero_def, zero_add]
    refine ⟨hQ, ?_⟩
    simpa [Affine.Point.zero_def, param] using M0
  rcases Q with _ | ⟨x₂, y₂, k₂⟩
  · rw [← Affine.Point.zero_def, add_zero]
    refine ⟨hP, ?_⟩
    simpa [Affine.Point.zero_def, param] using M0
  by_cases hxy : x₁ = x₂ ∧ y₁ = W.negY x₂ y₂
  · rw [Affine.Point.add_of_Y_eq hxy.1 hxy.2]
    refine ⟨trivial, ?_⟩
    obtain ⟨rfl, rfl⟩ := hxy
    have := neg_param h₁ h₂ h₃ h₄ h₆ hM hQ ((Affine.equation_iff _ _).1 k₂.1)
    rw [← norm_neg]
    refine le_of_eq_of_le (congrArg norm ?_) this
    simp only [Affine.Point.zero_def, param, Affine.negY]
    ring
  have hp := Affine.addPolynomial_slope k₁.1 k₂.1 hxy
  rw [Affine.addPolynomial_eq, neg_inj, Cubic.prod_X_sub_C_eq, Cubic.toPoly_injective] at hp
  have hy₂ : y₂ = W.slope x₁ x₂ y₁ y₂ * x₂ + (y₁ - W.slope x₁ x₂ y₁ y₂ * x₁) := by
    by_cases hx : x₁ = x₂
    · have := Affine.Y_eq_of_Y_ne k₁.1 k₂.1 hx (fun h => hxy ⟨hx, h⟩)
      rw [← hx, ← this]; ring
    · rw [Affine.slope_of_X_ne hx]
      have := sub_ne_zero.2 hx
      field_simp
      ring
  have he := (Affine.equation_iff _ _).1 (Affine.equation_negAdd k₁.1 k₂.1 hxy)
  rw [Affine.Point.add_some hxy]
  simp only [Near, param, Affine.addY] at hP hQ ⊢
  generalize W.slope x₁ x₂ y₁ y₂ = l at hp hy₂ he ⊢
  have hb := congrArg Cubic.b hp
  have hc := congrArg Cubic.c hp
  have hd := congrArg Cubic.d hp
  simp only [Affine.negY, Affine.negAddY] at hb hc hd he ⊢
  generalize W.addX x₁ x₂ l = x₃ at hb hc hd he ⊢
  have t1 := chord (x₃ := x₃) (y₁ := y₁) (y₂ := y₂) (y₃ := l * (x₃ - x₁) + y₁) (l := l)
    (n := y₁ - l * x₁) h₁ h₂ h₃ h₄ h₆ hM (by linear_combination hb) (by linear_combination -hc)
    (by linear_combination hd) (by ring) hy₂ (by ring) hP hQ
  refine ⟨t1.1, ?_⟩
  have t2 := neg_param h₁ h₂ h₃ h₄ h₆ hM t1.1 he
  have := (norm_sub_le_max' _ _).trans (max_le t2 t1.2)
  refine le_of_eq_of_le (congrArg norm ?_) this
  ring

theorem norm_x_le_one [DecidableEq K] {W : Affine K} (h₁ : ‖W.a₁‖ ≤ 1) (h₂ : ‖W.a₂‖ ≤ 1)
    (h₃ : ‖W.a₃‖ ≤ 1) (h₄ : ‖W.a₄‖ ≤ 1) (h₆ : ‖W.a₆‖ ≤ 1) (N : ℕ) (x y : K)
    (h : W.Nonsingular x y) (hN : ‖(N : K)‖ = 1)
    (h0 : N • (Affine.Point.some x y h) = 0) : ‖x‖ ≤ 1 := by
  by_contra hx
  push Not at hx
  have M0 : 0 ≤ ‖x‖⁻¹ := by positivity
  have hP : Near ‖x‖ (Affine.Point.some x y h) := le_refl _
  have key : ∀ k : ℕ, Near ‖x‖ (k • Affine.Point.some x y h) ∧
      ‖param (k • Affine.Point.some x y h) - (k : K) * (x / y)‖ ≤ ‖x‖⁻¹ := by
    intro k
    induction k with
    | zero =>
      rw [zero_nsmul]
      exact ⟨trivial, by simp [Affine.Point.zero_def, param]⟩
    | succ k ih =>
      obtain ⟨s1, s2⟩ := add_step' h₁ h₂ h₃ h₄ h₆ hx _ _ ih.1 hP
      rw [succ_nsmul]
      refine ⟨s1, ?_⟩
      have := (norm_add_le_max _ _).trans (max_le s2 ih.2)
      refine le_of_eq_of_le (congrArg norm ?_) this
      simp only [param]
      push_cast
      ring
  have h1 := (key N).2
  rw [h0] at h1
  simp only [Affine.Point.zero_def, param, zero_sub, norm_neg, norm_mul, hN, one_mul,
    norm_div] at h1
  have hy := norm_y_sq' h₁ h₂ h₃ h₄ h₆ hx ((Affine.equation_iff _ _).1 h.1)
  have x0 : 0 < ‖x‖ := by linarith
  have y0 : 0 < ‖y‖ := by
    refine lt_of_le_of_ne (norm_nonneg _) fun h => ?_
    rw [← h] at hy
    have : 0 < ‖x‖ ^ 3 := by positivity
    simp at hy
    linarith
  rw [inv_eq_one_div, div_le_div_iff₀ y0 x0, one_mul] at h1
  have h2 : (‖x‖ * ‖x‖) ^ 2 ≤ ‖y‖ ^ 2 := by gcongr
  rw [hy] at h2
  have : ‖x‖ ^ 3 * 1 < ‖x‖ ^ 3 * ‖x‖ := by gcongr
  nlinarith

theorem norm_x_sub_eq_one {W : Affine K} (h₁ : ‖W.a₁‖ ≤ 1) (h₂ : ‖W.a₂‖ ≤ 1)
    (h₃ : ‖W.a₃‖ ≤ 1) (h₄ : ‖W.a₄‖ ≤ 1) (h₆ : ‖W.a₆‖ ≤ 1) (hΔ : ‖W.Δ‖ = 1) {x₁ x₂ y₁ y₂ : K}
    (k₁ : W.Equation x₁ y₁) (k₂ : W.Equation x₂ y₂) (hx : x₁ ≠ x₂) (i₁ : ‖x₁‖ ≤ 1) (i₂ : ‖x₂‖ ≤ 1)
    (i₃ : ‖W.addX x₁ x₂ ((y₁ - y₂) / (x₁ - x₂))‖ ≤ 1)
    (i₄ : ‖W.addX x₁ x₂ ((y₁ - W.negY x₂ y₂) / (x₁ - x₂))‖ ≤ 1) : ‖x₁ - x₂‖ = 1 := by
  have m₁ : W.a₁ ∈ intRing K := h₁
  have m₂ : W.a₂ ∈ intRing K := h₂
  have j₁ : x₁ ∈ intRing K := i₁
  have j₂ : x₂ ∈ intRing K := i₂
  have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.2 hx
  have hl : ∀ l : K, ‖W.addX x₁ x₂ l‖ ≤ 1 → l ∈ intRing K := fun l h =>
    quad_mem (b := W.a₁) (r := W.addX x₁ x₂ l + W.a₂ + x₁ + x₂) (by simp only [Affine.addX]; ring)
      m₁ (add_mem (add_mem (add_mem h m₂) j₁) j₂)
  have l₃ := hl _ i₃
  have l₄ := hl _ i₄
  have e₃ : (y₁ - y₂) / (x₁ - x₂) * (x₁ - x₂) = y₁ - y₂ := div_mul_cancel₀ _ hd
  have e₄ : (y₁ - W.negY x₂ y₂) / (x₁ - x₂) * (x₁ - x₂) = y₁ - W.negY x₂ y₂ := div_mul_cancel₀ _ hd
  generalize (y₁ - y₂) / (x₁ - x₂) = l at l₃ e₃
  generalize (y₁ - W.negY x₂ y₂) / (x₁ - x₂) = l' at l₄ e₄
  rw [Affine.negY] at e₄
  rw [Affine.equation_iff] at k₁ k₂
  have md : x₁ - x₂ ∈ intRing K := sub_mem j₁ j₂
  obtain ⟨α, mα, eα⟩ : ∃ α ∈ intRing K, W.a₃ + x₁ * W.a₁ + 2 * y₁ = (x₁ - x₂) * α :=
    ⟨l + l' + W.a₁, add_mem (add_mem l₃ l₄) m₁, by linear_combination -e₃ - e₄⟩
  obtain ⟨β, mβ, eβ⟩ : ∃ β ∈ intRing K,
      W.a₄ + 2 * x₁ * W.a₂ - y₁ * W.a₁ + 3 * x₁ ^ 2 = (x₁ - x₂) * β := by
    refine ⟨l * l' + x₁ + x₁ + x₂ + W.a₂,
      add_mem (add_mem (add_mem (add_mem (mul_mem l₃ l₄) j₁) j₁) j₂) m₂, mul_left_cancel₀ hd ?_⟩
    linear_combination k₂ - k₁ - l' * (x₁ - x₂) * e₃ - (y₁ - y₂) * e₄
  let V : WeierstrassCurve K := ⟨W.a₁, W.a₂ + 3 * x₁, (x₁ - x₂) * α, (x₁ - x₂) * β, 0⟩
  have hV : (⟨1, x₁, 0, y₁⟩ : VariableChange K) • W = V := by
    ext
    · simp [V, variableChange_a₁]
    · simp [V, variableChange_a₂]
    · simp [V, variableChange_a₃, ← eα]
    · simp [V, variableChange_a₄, ← eβ]
    · simp only [V, variableChange_a₆, inv_one, Units.val_one]
      linear_combination -k₁
  have hΔ' : V.Δ = W.Δ := by rw [← hV, variableChange_Δ]; simp
  refine le_antisymm md ?_
  have ma : W.a₂ + 3 * x₁ ∈ intRing K := add_mem m₂ (mul_mem norm_three_le j₁)
  have e : V.Δ = (x₁ - x₂) * ((x₁ - x₂) * (-(W.a₁ ^ 2 + 4 * (W.a₂ + 3 * x₁)) ^ 2 *
      (-(W.a₁ * α * β) + (W.a₂ + 3 * x₁) * α ^ 2 - β ^ 2) -
      8 * (x₁ - x₂) * (2 * β + W.a₁ * α) ^ 3 - 27 * (x₁ - x₂) ^ 2 * α ^ 4 +
      9 * (W.a₁ ^ 2 + 4 * (W.a₂ + 3 * x₁)) * (2 * β + W.a₁ * α) * (x₁ - x₂) * α ^ 2)) := by
    simp only [V, Δ, b₂, b₄, b₆, b₈]
    ring
  rw [← hΔ, ← hΔ', e]
  refine norm_mul_le_of_mem ?_
  generalize W.a₂ + 3 * x₁ = a at ma
  generalize x₁ - x₂ = d at md
  have mb : W.a₁ ^ 2 + 4 * a ∈ intRing K := add_mem (pow_mem m₁ _) (mul_mem (ofNat_mem _ _) ma)
  have mc : 2 * β + W.a₁ * α ∈ intRing K := add_mem (mul_mem (ofNat_mem _ _) mβ) (mul_mem m₁ mα)
  exact mul_mem md (add_mem (sub_mem (sub_mem (mul_mem (neg_mem (pow_mem mb _))
    (sub_mem (add_mem (neg_mem (mul_mem (mul_mem m₁ mα) mβ)) (mul_mem ma (pow_mem mα _)))
      (pow_mem mβ _))) (mul_mem (mul_mem (ofNat_mem _ _) md) (pow_mem mc _)))
    (mul_mem (mul_mem (ofNat_mem _ _) (pow_mem md _)) (pow_mem mα _)))
    (mul_mem (mul_mem (mul_mem (mul_mem (ofNat_mem _ _) mb) mc) md) (pow_mem mα _)))

end General

open Classical in

theorem torsion_integral_and_distinct (q : ℕ) [Fact q.Prime] (M : Mdl q) (N : ℕ) (hM : M.Ok)
    (hN : Nat.Coprime N q) :
    (∀ p : ℂ, (N : ℂ) * p ∈ M.L.lattice → p ∉ M.L.lattice → ‖M.ι (M.x p)‖ ≤ 1) ∧
    ∀ p p' : ℂ, (N : ℂ) * p ∈ M.L.lattice → (N : ℂ) * p' ∈ M.L.lattice → p ∉ M.L.lattice →
      p' ∉ M.L.lattice → p + p' ∉ M.L.lattice → p - p' ∉ M.L.lattice →
      ‖M.ι (M.x p) - M.ι (M.x p')‖ = 1 := by
  obtain ⟨φ, -, hker, hφ⟩ := Mdl.exists_pointHom q M hM
  obtain ⟨-, h₁, h₂, h₃, h₄, h₆, hΔ, -, -⟩ := hM
  have hNn : ‖(N : ℂ_[q])‖ = 1 := by
    rw [← map_natCast (algebraMap ℚ_[q] ℂ_[q]), norm_algebraMap']
    exact Padic.norm_natCast_eq_one_iff.2 hN.symm
  have int : ∀ (p : ℂ) (x y : ℂ_[q]) (h), (N : ℂ) * p ∈ M.L.lattice →
      φ p = Affine.Point.some x y h → ‖x‖ ≤ 1 := fun p x y h hp e => by
    refine norm_x_le_one (W := M.W.toAffine) h₁ h₂ h₃ h₄ h₆ N x y h hNn ?_
    rw [← e, ← map_nsmul, hker, nsmul_eq_mul]
    exact hp
  refine ⟨fun p hp hp' => ?_, fun p p' hp hp' np np' ns nd => ?_⟩
  · obtain ⟨h, e⟩ := hφ p hp'
    exact int p _ _ h hp e
  obtain ⟨h, e⟩ := hφ p np
  obtain ⟨h', e'⟩ := hφ p' np'
  have hx : M.ι (M.x p) ≠ M.ι (M.x p') := fun hx => by
    rcases Affine.Y_eq_of_X_eq h.1 h'.1 hx with hy | hy
    · refine nd ((hker _).1 ?_)
      rw [map_sub, e, e', sub_eq_zero]
      simp only [Affine.Point.some.injEq]
      exact ⟨hx, hy⟩
    · refine ns ((hker _).1 ?_)
      rw [map_add, e, e', Affine.Point.add_of_Y_eq hx hy]
  refine norm_x_sub_eq_one (W := M.W.toAffine) h₁ h₂ h₃ h₄ h₆ hΔ h.1 h'.1 hx (int p _ _ h hp e)
    (int p' _ _ h' hp' e') ?_ ?_
  · rw [← Affine.slope_of_X_ne (W := M.W.toAffine) hx]
    exact int (p + p') _ _ _ (by rw [mul_add]; exact add_mem hp hp')
      (by rw [map_add, e, e', Affine.Point.add_of_X_ne hx])
  · rw [← Affine.slope_of_X_ne (W := M.W.toAffine) hx]
    exact int (p - p') _ _ _ (by rw [mul_sub]; exact sub_mem hp hp')
      (by rw [map_sub, e, e', sub_eq_add_neg, Affine.Point.neg_some, Affine.Point.add_of_X_ne hx])

end GlobalTheory.MomOne.TorsionReduction
