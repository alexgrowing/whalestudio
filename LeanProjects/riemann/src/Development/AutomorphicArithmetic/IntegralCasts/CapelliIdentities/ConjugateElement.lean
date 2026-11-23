import Mathlib

theorem UpperTheory.Reformulated.B.CMConjNegOfSqEqNegPos.conj_alt_bis :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E]
    [inst_2 : NumberField.IsCMField E] {d : ℕ},
    (0 : ℕ) < d → ∀ {x : E}, x ^ (2 : ℕ) = -(↑d : E) → (NumberField.IsCMField.complexConj E : E → E) x = -x := by
  intro E _ _ _ d hd x hx
  let φ : E →+* ℂ := Classical.choice (inferInstance : Nonempty _)
  apply φ.injective
  rw [NumberField.IsCMField.complexEmbedding_complexConj, map_neg]
  have h : (φ x) ^ 2 = -(d : ℂ) := by
    rw [← map_pow, hx, map_neg, map_natCast]
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.natCast_re, Complex.natCast_im, neg_zero] at hre him
  have h0 : (φ x).re * (φ x).im = 0 := by linarith
  have hr : (φ x).re = 0 := by
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact h1
    · rw [h1] at hre
      nlinarith [mul_self_nonneg (φ x).re]
  apply Complex.ext
  · rw [Complex.conj_re, Complex.neg_re, hr, neg_zero]
  · rw [Complex.conj_im, Complex.neg_im]
