import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementU

noncomputable section

namespace Formalism.L2.Th1.E

namespace unitAtAlt

section Norm

variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem i_add {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a + b‖ ≤ 1 := (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)

theorem i_neg {a : K} (ha : ‖a‖ ≤ 1) : ‖-a‖ ≤ 1 := by
  rw [norm_neg]
  exact ha

theorem i_sub {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a - b‖ ≤ 1 := by
  rw [sub_eq_add_neg]
  exact i_add ha (i_neg hb)

theorem i_mul {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a * b‖ ≤ 1 := by
  rw [norm_mul]
  calc ‖a‖ * ‖b‖ ≤ 1 * 1 := mul_le_mul ha hb (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

theorem i_pow {a : K} (ha : ‖a‖ ≤ 1) (n : ℕ) : ‖a ^ n‖ ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    exact i_mul ih ha

theorem i_ofNat (n : ℕ) [n.AtLeastTwo] : ‖(OfNat.ofNat n : K)‖ ≤ 1 := by
  have key : ∀ m : ℕ, ‖(m : K)‖ ≤ 1 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Nat.cast_succ]
      exact i_add ih (by simp)
  first
  | exact key n
  | (have h0 := key n; rwa [Nat.cast_ofNat] at h0)
  | simpa using key n

theorem s_add {a b : K} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) : ‖a + b‖ < 1 := (IsUltrametricDist.norm_add_le_max a b).trans_lt (max_lt ha hb)

theorem s_neg {a : K} (ha : ‖a‖ < 1) : ‖-a‖ < 1 := by
  rw [norm_neg]
  exact ha

theorem s_sub {a b : K} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) : ‖a - b‖ < 1 := by
  rw [sub_eq_add_neg]
  exact s_add ha (s_neg hb)

theorem s_mul {a b : K} (ha : ‖a‖ < 1) (hb : ‖b‖ ≤ 1) : ‖a * b‖ < 1 := by
  rw [norm_mul]
  calc ‖a‖ * ‖b‖ ≤ ‖a‖ * 1 := mul_le_mul_of_nonneg_left hb (norm_nonneg a)
    _ = ‖a‖ := mul_one _
    _ < 1 := ha

theorem s_mul' {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ < 1) : ‖a * b‖ < 1 := by
  rw [norm_mul]
  calc ‖a‖ * ‖b‖ ≤ 1 * ‖b‖ := mul_le_mul_of_nonneg_right ha (norm_nonneg b)
    _ = ‖b‖ := one_mul _
    _ < 1 := hb

macro "integ" : tactic =>
  `(tactic| repeat' (first
    | assumption
    | exact i_ofNat _
    | apply i_add
    | apply i_sub
    | apply i_mul
    | apply i_neg
    | apply i_pow))

theorem i_of_quadratic {t b c : K} (hb : ‖b‖ ≤ 1) (hc : ‖c‖ ≤ 1) (h : t ^ 2 + b * t = c) : ‖t‖ ≤ 1 := by
  by_contra hlt
  push_neg at hlt
  have h1 : t ^ 2 = c - b * t := by rw [← h]; ring
  have h2 : ‖t ^ 2‖ ≤ max ‖c‖ ‖b * t‖ := by
    rw [h1, sub_eq_add_neg]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_eq (by rw [norm_neg])
  rw [norm_pow] at h2
  have h3 : ‖b * t‖ ≤ ‖t‖ := by
    rw [norm_mul]
    calc ‖b‖ * ‖t‖ ≤ 1 * ‖t‖ := mul_le_mul_of_nonneg_right hb (norm_nonneg t)
      _ = ‖t‖ := one_mul _
  have h4 : max ‖c‖ ‖b * t‖ ≤ ‖t‖ := max_le (hc.trans hlt.le) h3
  have h5 : ‖t‖ * 1 < ‖t‖ * ‖t‖ := mul_lt_mul_of_pos_left hlt (by linarith)
  nlinarith [h2, h4, h5]

end Norm

section Alg

variable {K : Type} [Field K] (W : WeierstrassCurve K)

set_option maxHeartbeats 800000 in

theorem disc_comb (x y : K) (h : W.toAffine.Equation x y) :
    W.Δ =
      (2 * y + W.a₁ * x + W.a₃) *
        (-(W.a₁ ^ 2 + 4 * (W.a₂ + 3 * x)) ^ 2 *
            (-W.a₁ * (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) +
              (W.a₂ + 3 * x) * (2 * y + W.a₁ * x + W.a₃)) -
          8 * W.a₁ * (2 * (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) +
              W.a₁ * (2 * y + W.a₁ * x + W.a₃)) ^ 2 -
          27 * (2 * y + W.a₁ * x + W.a₃) ^ 3 +
          9 * (W.a₁ ^ 2 + 4 * (W.a₂ + 3 * x)) *
            (2 * (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) + W.a₁ * (2 * y + W.a₁ * x + W.a₃)) *
            (2 * y + W.a₁ * x + W.a₃)) +
      (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) *
        ((W.a₁ ^ 2 + 4 * (W.a₂ + 3 * x)) ^ 2 * (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) -
          16 * (2 * (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) +
              W.a₁ * (2 * y + W.a₁ * x + W.a₃)) ^ 2) := by
  rw [WeierstrassCurve.Affine.equation_iff] at h
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  first
  | linear_combination (432 * (W.a₆ + (y ^ 2 + W.a₁ * x * y + W.a₃ * y - x ^ 3 - W.a₂ * x ^ 2 - W.a₄ * x)) + (W.a₁ ^ 2 + 4 * W.a₂) ^ 3 + 216 * W.a₃ ^ 2 - 36 * (W.a₁ ^ 2 + 4 * W.a₂) * (2 * W.a₄ + W.a₁ * W.a₃)) * h
  | linear_combination (-(432 * (W.a₆ + (y ^ 2 + W.a₁ * x * y + W.a₃ * y - x ^ 3 - W.a₂ * x ^ 2 - W.a₄ * x)) + (W.a₁ ^ 2 + 4 * W.a₂) ^ 3 + 216 * W.a₃ ^ 2 - 36 * (W.a₁ ^ 2 + 4 * W.a₂) * (2 * W.a₄ + W.a₁ * W.a₃))) * h

end Alg

end unitAtAlt

open unitAtAlt WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem nonsingular_norm : NonsingNorm := by
  intro K _ _ W hW x y hx hy hE
  obtain ⟨h1, h2, h3, h4, h6, hΔ⟩ := hW
  have hFy : ‖2 * y + W.a₁ * x + W.a₃‖ ≤ 1 := by integ
  have hFx : ‖3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y‖ ≤ 1 := by integ
  by_contra hne
  push_neg at hne
  obtain ⟨hy1, hx1⟩ := hne
  have hy1' : ‖2 * y + W.a₁ * x + W.a₃‖ < 1 := lt_of_le_of_ne hFy hy1
  have hx1' : ‖3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y‖ < 1 := lt_of_le_of_ne hFx hx1
  have hlt : ‖W.Δ‖ < 1 := by
    rw [disc_comb W x y hE]
    apply s_add
    · exact s_mul hy1' (by integ)
    · exact s_mul hx1' (by integ)
  rw [hΔ] at hlt
  exact lt_irrefl _ hlt

theorem UnitKap_of (hN : NonsingNorm) : UnitKap := by
  intro K _ _ _ W hW P hP hPP hx hy
  cases P with
  | zero => exact absurd rfl hP
  | some x y h =>
    have hyeq : y = W.toAffine.negY x y := by
      by_contra hyne
      rw [add_self_of_Y_ne hyne] at hPP
      first
      | cases hPP
      | exact absurd hPP (by simp)
    have hpsi : 2 * y + W.a₁ * x + W.a₃ = 0 := by
      simp only [negY] at hyeq
      linear_combination hyeq
    refine ⟨hpsi, ?_⟩
    rcases hN K W hW x y hx hy h.1 with h1 | h1
    · rw [hpsi, norm_zero] at h1
      exact absurd h1 zero_ne_one
    · exact h1

theorem UnitPsi2_of (hN : NonsingNorm) : UnitPsi2 := by
  intro K _ _ _ W hW P hP hPP hx hy h2x
  cases P with
  | zero => exact absurd rfl hP
  | some x y h =>
    have hW' := hW
    obtain ⟨h1, h2, h3, h4, h6, hΔ⟩ := hW'
    have hxi : ‖x‖ ≤ 1 := hx
    have hyi : ‖y‖ ≤ 1 := hy
    have hyne : y ≠ W.toAffine.negY x y := by
      intro hyeq
      apply hPP
      first
      | exact add_self_of_Y_eq hyeq
      | exact add_of_Y_eq rfl hyeq
    have hpsi_ne : 2 * y + W.a₁ * x + W.a₃ ≠ 0 := by
      intro h0
      apply hyne
      simp only [negY]
      linear_combination h0
    rw [add_self_of_Y_ne hyne] at h2x
    have e2 : ‖W.toAffine.addX x x (W.toAffine.slope x x y y)‖ ≤ 1 := h2x
    have hL : W.toAffine.slope x x y y * (2 * y + W.a₁ * x + W.a₃) = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y := by
      rw [slope_of_Y_ne rfl hyne]
      have hd : y - W.toAffine.negY x y = 2 * y + W.a₁ * x + W.a₃ := by
        simp only [negY]
        ring
      rw [hd]
      first
      | exact div_mul_cancel₀ _ hpsi_ne
      | field_simp
    obtain ⟨L, hLdef⟩ : ∃ L, L = W.toAffine.slope x x y y := ⟨_, rfl⟩
    rw [← hLdef] at hL e2
    have hLi : ‖L‖ ≤ 1 := i_of_quadratic (b := W.a₁) (c := W.toAffine.addX x x L + W.a₂ + x + x) h1
      (i_add (i_add (i_add e2 h2) hxi) hxi) (by simp only [addX]; ring)
    change ‖2 * y + W.a₁ * x + W.a₃‖ = 1
    by_contra hne
    have hpsi_lt : ‖2 * y + W.a₁ * x + W.a₃‖ < 1 := lt_of_le_of_ne (by integ) hne
    have hk : ‖3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y‖ = 1 := by
      rcases hN K W hW x y hxi hyi h.1 with h' | h'
      · exact absurd h' hne
      · exact h'
    have hlt : ‖L * (2 * y + W.a₁ * x + W.a₃)‖ < 1 := s_mul' hLi hpsi_lt
    rw [hL, hk] at hlt
    exact lt_irrefl _ hlt

theorem UnitDiff_of (hN : NonsingNorm) : UnitDiff := by
  intro K _ _ _ W hW P Q hP hQ hPQ hPmQ hxP hyP hxQ hyQ hxs hxd
  cases P with
  | zero => exact absurd rfl hP
  | some x₁ y₁ h₁ =>
    cases Q with
    | zero => exact absurd rfl hQ
    | some x₂ y₂ h₂ =>
      have hW' := hW
      obtain ⟨ha1, ha2, ha3, ha4, ha6, hΔ⟩ := hW'
      have hx1 : ‖x₁‖ ≤ 1 := hxP
      have hy1 : ‖y₁‖ ≤ 1 := hyP
      have hx2 : ‖x₂‖ ≤ 1 := hxQ
      have hy2 : ‖y₂‖ ≤ 1 := hyQ
      have e₁ : y₁ ^ 2 + W.a₁ * x₁ * y₁ + W.a₃ * y₁ = x₁ ^ 3 + W.a₂ * x₁ ^ 2 + W.a₄ * x₁ + W.a₆ := by
        have h0 := h₁.1
        rw [equation_iff] at h0
        exact h0
      have e₂ : y₂ ^ 2 + W.a₁ * x₂ * y₂ + W.a₃ * y₂ = x₂ ^ 3 + W.a₂ * x₂ ^ 2 + W.a₄ * x₂ + W.a₆ := by
        have h0 := h₂.1
        rw [equation_iff] at h0
        exact h0
      have hx12 : x₁ ≠ x₂ := by
        intro hxx
        have hprod : (y₁ - y₂) * (y₁ - W.toAffine.negY x₂ y₂) = 0 := by
          simp only [negY]
          rw [← hxx] at e₂ ⊢
          linear_combination e₁ - e₂
        rcases mul_eq_zero.mp hprod with hyy | hyy
        · have hyy' : y₁ = y₂ := sub_eq_zero.mp hyy
          subst hxx
          subst hyy'
          exact hPmQ (sub_self _)
        · have hy : y₁ = W.toAffine.negY x₂ y₂ := sub_eq_zero.mp hyy
          apply hPQ
          first
          | exact add_of_Y_eq hxx hy
          | (subst hxx; rw [add_eq_zero_iff_eq_neg, neg_some]; subst hy; rfl)
      have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx12
      rw [add_of_X_ne hx12] at hxs
      have es : ‖W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂)‖ ≤ 1 := hxs
      rw [slope_of_X_ne hx12] at es
      rw [sub_eq_add_neg, neg_some, add_of_X_ne hx12] at hxd
      have ed : ‖W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ (W.toAffine.negY x₂ y₂))‖ ≤ 1 := hxd
      rw [slope_of_X_ne hx12] at ed
      obtain ⟨Lp, hLpdef⟩ : ∃ L, L = (y₁ - y₂) / (x₁ - x₂) := ⟨_, rfl⟩
      obtain ⟨Lm, hLmdef⟩ : ∃ L, L = (y₁ - W.toAffine.negY x₂ y₂) / (x₁ - x₂) := ⟨_, rfl⟩
      rw [← hLpdef] at es
      rw [← hLmdef] at ed
      have hLp : Lp * (x₁ - x₂) = y₁ - y₂ := by
        rw [hLpdef]
        exact div_mul_cancel₀ _ hd
      have hLm : Lm * (x₁ - x₂) = y₁ + y₂ + W.a₁ * x₂ + W.a₃ := by
        rw [hLmdef, div_mul_cancel₀ _ hd]
        simp only [negY]
        ring
      have hLpi : ‖Lp‖ ≤ 1 := i_of_quadratic (b := W.a₁) (c := W.toAffine.addX x₁ x₂ Lp + W.a₂ + x₁ + x₂) ha1
        (i_add (i_add (i_add es ha2) hx1) hx2) (by simp only [addX]; ring)
      have hLmi : ‖Lm‖ ≤ 1 := i_of_quadratic (b := W.a₁) (c := W.toAffine.addX x₁ x₂ Lm + W.a₂ + x₁ + x₂) ha1
        (i_add (i_add (i_add ed ha2) hx1) hx2) (by simp only [addX]; ring)
      have hAB : (y₁ - y₂) * (y₁ + y₂ + W.a₁ * x₂ + W.a₃) =
          (x₁ - x₂) * (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₁) := by
        linear_combination e₁ - e₂
      have hprod : Lp * Lm * (x₁ - x₂) = x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₁ := by
        apply mul_right_cancel₀ hd
        linear_combination (Lm * (x₁ - x₂)) * hLp + (y₁ - y₂) * hLm + hAB
      have hpsi : 2 * y₁ + W.a₁ * x₁ + W.a₃ = (x₁ - x₂) * (Lp + Lm + W.a₁) := by
        linear_combination -hLp - hLm
      have hkap : 3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁ = (x₁ - x₂) * (Lp * Lm + 2 * x₁ + x₂ + W.a₂) := by
        linear_combination -hprod
      change ‖x₁ - x₂‖ = 1
      by_contra hne
      have hdlt : ‖x₁ - x₂‖ < 1 := lt_of_le_of_ne (i_sub hx1 hx2) hne
      rcases hN K W hW x₁ y₁ hx1 hy1 h₁.1 with h' | h'
      · rw [hpsi] at h'
        have hlt : ‖(x₁ - x₂) * (Lp + Lm + W.a₁)‖ < 1 := s_mul hdlt (by integ)
        rw [h'] at hlt
        exact lt_irrefl _ hlt
      · rw [hkap] at h'
        have hlt : ‖(x₁ - x₂) * (Lp * Lm + 2 * x₁ + x₂ + W.a₂)‖ < 1 := s_mul hdlt (by integ)
        rw [h'] at hlt
        exact lt_irrefl _ hlt

end Formalism.L2.Th1.E
