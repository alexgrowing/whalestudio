import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormAddOfLt

namespace GlobalTheory.TorsionIntegral

open IsUltrametricDist WeierstrassCurve

variable {K : Type} [NormedField K] [IsUltrametricDist K]

lemma norm_sub_le_max' (a b : K) : ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by
  have := norm_add_le_max a (-b)
  rwa [norm_neg, ← sub_eq_add_neg] at this

lemma norm_add_eq_of_lt {a b : K} (h : ‖b‖ < ‖a‖) : ‖a + b‖ = ‖a‖ := by
  rw [norm_add_eq_max_of_norm_ne_norm h.ne', max_eq_left h.le]

lemma norm_y_sq {A B x y : K} (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) (hx : 1 < ‖x‖)
    (h : y ^ 2 = x ^ 3 + A * x + B) : ‖y‖ ^ 2 = ‖x‖ ^ 3 := by
  have h1 : ‖x‖ < ‖x‖ ^ 3 := by
    have := pow_lt_pow_right₀ hx (show 1 < 3 by norm_num)
    simpa using this
  rw [← norm_pow, h, add_assoc, norm_add_eq_of_lt, norm_pow]
  rw [norm_pow]
  refine (norm_add_le_max _ _).trans_lt (max_lt ?_ (by linarith))
  rw [norm_mul]
  nlinarith [norm_nonneg A]

lemma norm_sum_three_le (a b c : K) : ‖a + b + c‖ ≤ max (max ‖a‖ ‖b‖) ‖c‖ :=
  (norm_add_le_max _ _).trans (max_le_max (norm_add_le_max _ _) le_rfl)

lemma norm_two_le : ‖(2 : K)‖ ≤ 1 := by
  simpa using IsUltrametricDist.norm_natCast_le_one K 2

lemma norm_three_le : ‖(3 : K)‖ ≤ 1 := by
  simpa using IsUltrametricDist.norm_natCast_le_one K 3

lemma torsion_root_norm_bound {A B x₁ x₂ x₃ l n : K} (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1)
    (e1 : x₁ + x₂ + x₃ = l ^ 2) (e2 : x₁ * x₂ + x₁ * x₃ + x₂ * x₃ = A - 2 * l * n)
    (e3 : x₁ * x₂ * x₃ = n ^ 2 - B) (h12 : ‖x₂‖ ≤ ‖x₁‖) (h2 : 1 < ‖x₂‖) : ‖x₂‖ ≤ ‖x₃‖ := by
  by_contra hc
  push Not at hc
  set a := ‖x₁‖ with ha
  set b := ‖x₂‖ with hb
  set c := ‖x₃‖ with hc'
  have c0 : 0 ≤ c := norm_nonneg _
  have hl : ‖l‖ ^ 2 ≤ a := by
    rw [← norm_pow, ← e1]
    exact (norm_sum_three_le _ _ _).trans (max_le (max_le le_rfl h12) (by linarith))
  have hn : ‖n‖ ^ 2 ≤ max (a * b * c) 1 := by
    rw [← norm_pow, show n ^ 2 = x₁ * x₂ * x₃ + B by rw [e3]; ring]
    refine (norm_add_le_max _ _).trans (max_le_max ?_ hB)
    rw [norm_mul, norm_mul]
  have hab : a * b ≤ max 1 (‖l‖ * ‖n‖) := by
    have h1 : ‖x₁ * x₂ + x₁ * x₃ + x₂ * x₃‖ = a * b := by
      rw [add_assoc, norm_add_eq_of_lt, norm_mul]
      refine (norm_add_le_max _ _).trans_lt (max_lt ?_ ?_) <;> rw [norm_mul, norm_mul] <;>
        nlinarith
    rw [← h1, e2]
    refine (norm_sub_le_max' _ _).trans (max_le_max hA ?_)
    rw [norm_mul, norm_mul]
    have := norm_two_le (K := K)
    have h3 : 0 ≤ ‖l‖ * ‖n‖ := by positivity
    nlinarith
  have hab1 : 1 < a * b := by nlinarith
  have hab2 : a * b ≤ ‖l‖ * ‖n‖ := by
    rcases le_max_iff.1 hab with h | h
    · linarith
    · exact h
  have h4 : (a * b) ^ 2 ≤ a * max (a * b * c) 1 := by
    calc (a * b) ^ 2 ≤ (‖l‖ * ‖n‖) ^ 2 := by gcongr
      _ = ‖l‖ ^ 2 * ‖n‖ ^ 2 := by ring
      _ ≤ _ := by gcongr
  have a0 : 0 < a := by linarith
  have h5 : max (a * b * c) 1 < a * b * b := by
    refine max_lt ?_ ?_
    · exact mul_lt_mul_of_pos_left hc (by linarith)
    · nlinarith
  have := mul_lt_mul_of_pos_left h5 a0
  nlinarith

lemma core {A B x₁ x₂ x₃ y₁ y₂ y₃ l n : K} {M : ℝ} (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) (hM : 1 < M)
    (e1 : x₁ + x₂ + x₃ = l ^ 2) (e2 : x₁ * x₂ + x₁ * x₃ + x₂ * x₃ = A - 2 * l * n)
    (e3 : x₁ * x₂ * x₃ = n ^ 2 - B) (hy₁ : y₁ = l * x₁ + n) (hy₂ : y₂ = l * x₂ + n)
    (hy₃ : y₃ = l * x₃ + n) (h1 : M ≤ ‖x₁‖) (h2 : M ≤ ‖x₂‖) :
    M ≤ ‖x₃‖ ∧ ‖x₁ / y₁ + x₂ / y₂ + x₃ / y₃‖ ≤ M⁻¹ := by
  have h3 : M ≤ ‖x₃‖ := by
    rcases le_total ‖x₂‖ ‖x₁‖ with h | h
    · exact h2.trans (torsion_root_norm_bound hA hB e1 e2 e3 h (by linarith))
    · exact h1.trans (torsion_root_norm_bound (x₁ := x₂) (x₂ := x₁) (l := l) (n := n) hA hB
        (by linear_combination e1) (by linear_combination e2) (by linear_combination e3) h
        (by linarith))
  refine ⟨h3, ?_⟩
  have q1 : y₁ ^ 2 = x₁ ^ 3 + A * x₁ + B := by
    rw [hy₁]; linear_combination (-x₁ ^ 2) * e1 + x₁ * e2 - e3
  have q2 : y₂ ^ 2 = x₂ ^ 3 + A * x₂ + B := by
    rw [hy₂]; linear_combination (-x₂ ^ 2) * e1 + x₂ * e2 - e3
  have q3 : y₃ ^ 2 = x₃ ^ 3 + A * x₃ + B := by
    rw [hy₃]; linear_combination (-x₃ ^ 2) * e1 + x₃ * e2 - e3
  have n1 := norm_y_sq hA hB (by linarith) q1
  have n2 := norm_y_sq hA hB (by linarith) q2
  have n3 := norm_y_sq hA hB (by linarith) q3
  set a := ‖x₁‖ with ha
  set b := ‖x₂‖ with hb
  set c := ‖x₃‖ with hc
  have hab : M ≤ a * b := by nlinarith
  have hac : M ≤ a * c := by nlinarith
  have hbc : M ≤ b * c := by nlinarith
  have habc : M ^ 2 ≤ a * b * c := by nlinarith
  have hM2 : 1 < M ^ 2 := by nlinarith
  have hn : ‖n‖ ^ 2 = a * b * c := by
    rw [← norm_pow, show n ^ 2 = x₁ * x₂ * x₃ + B by rw [e3]; ring, norm_add_eq_of_lt,
      norm_mul, norm_mul]
    rw [norm_mul, norm_mul]
    linarith
  have hl : ‖l‖ ≤ ‖n‖ := by
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
    rw [hn, ← norm_pow, ← e1]
    refine (norm_sum_three_le _ _ _).trans (max_le (max_le ?_ ?_) ?_) <;> nlinarith
  have hMn : M ≤ ‖n‖ := by
    refine (pow_le_pow_iff_left₀ (by linarith) (norm_nonneg _) two_ne_zero).1 ?_
    rw [hn]; exact habc
  have hyy : ‖y₁ * y₂ * y₃‖ = ‖n‖ ^ 3 := by
    refine (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
    rw [norm_mul, norm_mul, mul_pow, mul_pow, n1, n2, n3, ← pow_mul, mul_comm 3 2, pow_mul, hn]
    ring
  have n0 : 0 < ‖n‖ := by linarith
  have hy0 : y₁ * y₂ * y₃ ≠ 0 := by
    rw [← norm_pos_iff, hyy]; positivity
  have y1 : y₁ ≠ 0 := fun h => hy0 (by simp [h])
  have y2 : y₂ ≠ 0 := fun h => hy0 (by simp [h])
  have y3 : y₃ ≠ 0 := fun h => hy0 (by simp [h])
  have hS : x₁ * y₂ * y₃ + y₁ * x₂ * y₃ + y₁ * y₂ * x₃ = 2 * A * l * n - 3 * B * l * l := by
    rw [hy₁, hy₂, hy₃]
    linear_combination n ^ 2 * e1 + 2 * l * n * e2 + 3 * l ^ 2 * e3
  have hq : x₁ / y₁ + x₂ / y₂ + x₃ / y₃ = (2 * A * l * n - 3 * B * l * l) / (y₁ * y₂ * y₃) := by
    rw [← hS]; field_simp
  have hN : ‖2 * A * l * n - 3 * B * l * l‖ ≤ ‖n‖ ^ 2 := by
    refine (norm_sub_le_max' _ _).trans (max_le ?_ ?_)
    · rw [norm_mul, norm_mul, norm_mul]
      calc _ ≤ 1 * 1 * ‖n‖ * ‖n‖ := by gcongr; exact norm_two_le
        _ = _ := by ring
    · rw [norm_mul, norm_mul, norm_mul]
      calc _ ≤ 1 * 1 * ‖n‖ * ‖n‖ := by gcongr; exact norm_three_le
        _ = _ := by ring
  rw [hq, norm_div, hyy]
  calc _ ≤ ‖n‖ ^ 2 / ‖n‖ ^ 3 := by gcongr
    _ = ‖n‖⁻¹ := by field_simp
    _ ≤ M⁻¹ := by gcongr

noncomputable def param {W : Affine K} : W.Point → K
  | .zero => 0
  | .some x y _ => x / y

def Near {W : Affine K} (M : ℝ) : W.Point → Prop
  | .zero => True
  | .some x _ _ => M ≤ ‖x‖

lemma add_step [DecidableEq K] {A B : K} {M : ℝ} (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) (hM : 1 < M)
    (P Q : (⟨0, 0, 0, A, B⟩ : WeierstrassCurve K).toAffine.Point) (hP : Near M P)
    (hQ : Near M Q) : Near M (P + Q) ∧ ‖param (P + Q) - param P - param Q‖ ≤ M⁻¹ := by
  first
  | exact @_root_.GlobalTheory.UltrametricLineBounds.large_add
  | exact _root_.GlobalTheory.UltrametricLineBounds.large_add
  | (apply _root_.GlobalTheory.UltrametricLineBounds.large_add <;> assumption)
  | (intros; apply _root_.GlobalTheory.UltrametricLineBounds.large_add <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UltrametricLineBounds.large_add <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UltrametricLineBounds.large_add ..)

theorem norm_x_le_one_of_nsmul_eq_zero (K : Type) [NormedField K] [IsUltrametricDist K]
    [DecidableEq K] (A B : K) (N : ℕ) (x y : K)
    (h : (⟨0, 0, 0, A, B⟩ : WeierstrassCurve K).toAffine.Nonsingular x y)
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) (hN : ‖(N : K)‖ = 1)
    (h0 : N • (WeierstrassCurve.Affine.Point.some x y h) = 0) : ‖x‖ ≤ 1 := by
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
      obtain ⟨s1, s2⟩ := add_step hA hB hx _ _ ih.1 hP
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
  have he : y ^ 2 = x ^ 3 + A * x + B := by
    have := (Affine.equation_iff _ _).1 h.1
    simp only at this
    linear_combination this
  have hy := norm_y_sq hA hB hx he
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

end GlobalTheory.TorsionIntegral
