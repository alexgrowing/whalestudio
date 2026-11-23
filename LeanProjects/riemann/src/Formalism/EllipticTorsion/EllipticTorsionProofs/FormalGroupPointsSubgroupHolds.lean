import Mathlib
import Formalism.EllipticTorsion.FormalGroupPointsTorsionFree

noncomputable section

universe u

namespace Formalism.ELL.FormalGroupPointsSubgroup

open WeierstrassCurve Polynomial

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

lemma add_le {a b : K} {c : ℝ} (ha : ‖a‖ ≤ c) (hb : ‖b‖ ≤ c) : ‖a + b‖ ≤ c := by
  exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)

lemma sub_le {a b : K} {c : ℝ} (ha : ‖a‖ ≤ c) (hb : ‖b‖ ≤ c) : ‖a - b‖ ≤ c := by
  rw [sub_eq_add_neg]
  exact add_le ha (by rwa [norm_neg])

lemma le_sub_of_lt {a b : K} (h : ‖b‖ < ‖a‖) : ‖a‖ ≤ ‖a - b‖ := by
  have h1 : ‖a‖ ≤ max ‖a - b‖ ‖b‖ := by
    simpa using IsUltrametricDist.norm_add_le_max (a - b) b
  rcases le_max_iff.mp h1 with h2 | h2
  · exact h2
  · exact absurd h2 (not_le.mpr h)

lemma mul_le {a b : K} {c d : ℝ} (ha : ‖a‖ ≤ c) (hb : ‖b‖ ≤ d) : ‖a * b‖ ≤ c * d := by
  rw [norm_mul]
  exact mul_le_mul ha hb (norm_nonneg _) ((norm_nonneg _).trans ha)

lemma y_int (W : WeierstrassCurve K)
    (hW : IntegralModel W) {x y : K} (h : W.toAffine.Equation x y) (hx : ‖x‖ ≤ 1) : ‖y‖ ≤ 1 := by
  obtain ⟨h1, h2, h3, h4, h6⟩ := hW
  have h' : y ^ 2 + W.a₁ * x * y + W.a₃ * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ :=
    (WeierstrassCurve.Affine.equation_iff _ _).mp h
  by_contra hy
  push_neg at hy
  have hR : ‖x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆‖ ≤ 1 := by
    have hx2 : ‖x ^ 2‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx
    have hx3 : ‖x ^ 3‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx
    refine add_le (add_le (add_le hx3 ?_) ?_) h6
    · simpa using mul_le h2 hx2
    · simpa using mul_le h4 hx
  have hT : ‖W.a₁ * x * y + W.a₃ * y‖ ≤ ‖y‖ := by
    refine add_le ?_ ?_
    · simpa using mul_le (mul_le h1 hx) (le_refl ‖y‖)
    · simpa using mul_le h3 (le_refl ‖y‖)
  have hlt : ‖-(W.a₁ * x * y + W.a₃ * y)‖ < ‖y ^ 2‖ := by
    rw [norm_neg, norm_pow]; nlinarith
  have key := le_sub_of_lt hlt
  rw [sub_neg_eq_add, ← add_assoc, h', norm_pow] at key
  nlinarith

lemma y_sq_le (W : WeierstrassCurve K) (hW : IntegralModel W) {x y : K}
    (h : W.toAffine.Equation x y) (hx : 1 < ‖x‖) : ‖y‖ ^ 2 ≤ ‖x‖ ^ 3 := by
  obtain ⟨h1, h2, h3, h4, h6⟩ := hW
  have h' : y ^ 2 + W.a₁ * x * y + W.a₃ * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ :=
    (WeierstrassCurve.Affine.equation_iff _ _).mp h
  by_contra hy
  push_neg at hy
  have hx0 : (0 : ℝ) < ‖x‖ := by linarith
  have hx2 : ‖x‖ ^ 2 < ‖x‖ ^ 3 := by
    nlinarith [mul_pos (mul_pos hx0 hx0) (by linarith : (0 : ℝ) < ‖x‖ - 1)]
  have hx1 : ‖x‖ ≤ ‖x‖ ^ 3 := by
    nlinarith [mul_pos hx0 (by linarith : (0 : ℝ) < ‖x‖ - 1)]
  have hxy : ‖x‖ < ‖y‖ := by
    by_contra hc
    push_neg at hc
    have := mul_le_mul hc hc (norm_nonneg y) hx0.le
    nlinarith
  have hR : ‖x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆‖ ≤ ‖x‖ ^ 3 := by
    refine add_le (add_le (add_le (le_of_eq (norm_pow _ _)) ?_) ?_) ?_
    · exact (mul_le h2 (le_of_eq (norm_pow x 2))).trans (by linarith)
    · exact (mul_le h4 (le_refl ‖x‖)).trans (by linarith)
    · exact h6.trans (one_le_pow₀ hx.le)
  have hT : ‖W.a₁ * x * y + W.a₃ * y‖ ≤ ‖x‖ * ‖y‖ := by
    refine add_le ?_ ?_
    · simpa using mul_le (mul_le h1 (le_refl ‖x‖)) (le_refl ‖y‖)
    · exact (mul_le h3 (le_refl ‖y‖)).trans (by nlinarith [norm_nonneg y])
  have hlt : ‖-(W.a₁ * x * y + W.a₃ * y)‖ < ‖y ^ 2‖ := by
    rw [norm_neg, norm_pow]; nlinarith [norm_nonneg y]
  have key := le_sub_of_lt hlt
  rw [sub_neg_eq_add, ← add_assoc, h', norm_pow] at key
  linarith

lemma addX_norm [DecidableEq K] (W : WeierstrassCurve K) (hW : IntegralModel W)
    {x₁ x₂ y₁ y₂ : K} (h₁ : W.toAffine.Equation x₁ y₁) (h₂ : W.toAffine.Equation x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂)) (hx₁ : 1 < ‖x₁‖) (hx₂ : 1 < ‖x₂‖) :
    1 < ‖W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂)‖ := by
  set ℓ := W.toAffine.slope x₁ x₂ y₁ y₂ with hℓ
  set x₃ := W.toAffine.addX x₁ x₂ ℓ with hx₃
  set y₃ := W.toAffine.negAddY x₁ x₂ y₁ ℓ with hy₃
  by_contra hC
  push Not at hC
  have h₃ : W.toAffine.Equation x₃ y₃ := Affine.equation_negAdd h₁ h₂ hxy
  have hy3 : ‖y₃‖ ≤ 1 := y_int W hW h₃ hC
  have hpoly := Affine.addPolynomial_slope h₁ h₂ hxy
  rw [← hℓ] at hpoly
  have hev := congrArg (Polynomial.eval (x₃ + 1)) hpoly
  simp only [Affine.addPolynomial, Affine.linePolynomial, Affine.polynomial] at hev
  simp at hev
  have hx3def : x₃ = ℓ ^ 2 + W.toAffine.a₁ * ℓ - W.toAffine.a₂ - x₁ - x₂ := by simp [hx₃]
  rw [← hx3def] at hev
  obtain ⟨a1, a2, a3, a4, a6⟩ := hW

  have hy3def : y₃ = ℓ * (x₃ - x₁) + y₁ := by simp [hy₃, hx₃]
  have hx0 : 0 ≤ ‖x₁‖ := norm_nonneg _
  have hℓ0 : 0 ≤ ‖ℓ‖ := norm_nonneg _
  have hsq := y_sq_le W ⟨a1, a2, a3, a4, a6⟩ h₁ hx₁
  have hd : ‖x₁‖ ≤ ‖x₁ - x₃‖ := le_sub_of_lt (by linarith)
  have hlin : ‖ℓ‖ * ‖x₁‖ ≤ max ‖y₁‖ 1 := by
    have e : ℓ * (x₁ - x₃) = y₁ - y₃ := by rw [hy3def]; ring
    have : ‖ℓ * (x₁ - x₃)‖ ≤ max ‖y₁‖ 1 := by
      rw [e]; exact sub_le (le_max_left _ _) (hy3.trans (le_max_right _ _))
    rw [norm_mul] at this
    nlinarith
  have hℓsq : ‖ℓ‖ ^ 2 ≤ ‖x₁‖ := by
    have hm : (max ‖y₁‖ 1) ^ 2 ≤ ‖x₁‖ ^ 3 := by
      rcases le_total ‖y₁‖ 1 with h | h
      · rw [max_eq_right h, one_pow]; exact one_le_pow₀ hx₁.le
      · rw [max_eq_left h]; exact hsq
    have : (‖ℓ‖ * ‖x₁‖) ^ 2 ≤ ‖x₁‖ ^ 3 :=
      (pow_le_pow_left₀ (by positivity) hlin 2).trans hm
    have hx1p : 0 < ‖x₁‖ ^ 2 := by positivity
    nlinarith

  set M := max 1 ‖ℓ‖ with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  have hMℓ : ‖ℓ‖ ≤ M := le_max_right _ _
  have hMsq : M ^ 2 ≤ ‖x₁‖ := by
    rcases le_total 1 ‖ℓ‖ with h | h
    · rw [hM, max_eq_right h]; exact hℓsq
    · rw [hM, max_eq_left h]; nlinarith
  have ht : ‖x₃ + 1‖ ≤ 1 := add_le hC (by simp)
  have hu : ‖ℓ * (x₃ + 1 - x₁) + y₁‖ ≤ M := by
    have e : ℓ * (x₃ + 1 - x₁) + y₁ = y₃ + ℓ := by rw [hy3def]; ring
    rw [e]; exact add_le (hy3.trans hM1) hMℓ
  have hM2 : M ≤ M ^ 2 := by nlinarith
  have hLHS : ‖(ℓ * (x₃ + 1 - x₁) + y₁) ^ 2 + W.a₁ * (x₃ + 1) * (ℓ * (x₃ + 1 - x₁) + y₁)
      + W.a₃ * (ℓ * (x₃ + 1 - x₁) + y₁)
      - ((x₃ + 1) ^ 3 + W.a₂ * (x₃ + 1) ^ 2 + W.a₄ * (x₃ + 1) + W.a₆)‖ ≤ ‖x₁‖ := by
    have ht2 : ‖(x₃ + 1) ^ 2‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ht
    have ht3 : ‖(x₃ + 1) ^ 3‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ht
    have hc : ‖(x₃ + 1) ^ 3 + W.a₂ * (x₃ + 1) ^ 2 + W.a₄ * (x₃ + 1) + W.a₆‖ ≤ 1 := by
      refine add_le (add_le (add_le ht3 ?_) ?_) a6
      · simpa using mul_le a2 ht2
      · simpa using mul_le a4 ht
    refine sub_le (add_le (add_le ?_ ?_) ?_) (hc.trans (by nlinarith))
    · rw [norm_pow]; exact (pow_le_pow_left₀ (norm_nonneg _) hu 2).trans hMsq
    · have := mul_le (mul_le a1 ht) hu
      linarith
    · have := mul_le a3 hu
      linarith

  have hRHS : ‖x₁‖ * ‖x₂‖ ≤ ‖(x₃ + 1 - x₁) * (x₃ + 1 - x₂) * (x₃ + 1 - x₃)‖ := by
    have e1 : ‖x₁‖ ≤ ‖x₃ + 1 - x₁‖ := by
      rw [norm_sub_rev]; exact le_sub_of_lt (by linarith)
    have e2 : ‖x₂‖ ≤ ‖x₃ + 1 - x₂‖ := by
      rw [norm_sub_rev]; exact le_sub_of_lt (by linarith)
    have e3 : x₃ + 1 - x₃ = 1 := by ring
    rw [e3, mul_one, norm_mul]
    exact mul_le_mul e1 e2 (norm_nonneg _) (norm_nonneg _)
  have heq : (ℓ * (x₃ + 1 - x₁) + y₁) ^ 2 + W.a₁ * (x₃ + 1) * (ℓ * (x₃ + 1 - x₁) + y₁)
      + W.a₃ * (ℓ * (x₃ + 1 - x₁) + y₁)
      - ((x₃ + 1) ^ 3 + W.a₂ * (x₃ + 1) ^ 2 + W.a₄ * (x₃ + 1) + W.a₆) =
      -((x₃ + 1 - x₁) * (x₃ + 1 - x₂) * (x₃ + 1 - x₃)) := by
    linear_combination hev
  rw [heq, norm_neg] at hLHS
  have := hRHS.trans hLHS
  nlinarith

end Formalism.ELL.FormalGroupPointsSubgroup

namespace Formalism.ELL

open WeierstrassCurve

open Classical in
theorem formal_group_points_subgroup_holds : Formalism.ELL.FormalGroupPointsSubgroup' := by
  intro K _ _ W hW _ P Q hP hQ
  refine ⟨?_, ?_⟩
  · rcases P with _ | @⟨x₁, y₁, h₁⟩
    · rw [show (Affine.Point.zero : W.toAffine.Point) = 0 from rfl, zero_add]; exact hQ
    rcases Q with _ | @⟨x₂, y₂, h₂⟩
    · rw [show (Affine.Point.zero : W.toAffine.Point) = 0 from rfl, add_zero]; exact hP
    by_cases hxy : x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂
    · rw [Affine.Point.add_of_Y_eq hxy.1 hxy.2]
      trivial
    · rw [Affine.Point.add_some hxy]
      exact FormalGroupPointsSubgroup.addX_norm W hW h₁.1 h₂.1 hxy hP hQ
  · rcases P with _ | @⟨x, y, h⟩
    · trivial
    · simpa [InFormalGroupPoints] using hP

end Formalism.ELL
