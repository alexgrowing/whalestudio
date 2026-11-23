import Mathlib

namespace GlobalTheory.UltrametricLineBounds

section aux
variable {K : Type} [NormedField K] [IsUltrametricDist K]

lemma add_le {a b : K} {r : ℝ} (ha : ‖a‖ ≤ r) (hb : ‖b‖ ≤ r) : ‖a + b‖ ≤ r :=
  (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)

lemma sub_le {a b : K} {r : ℝ} (ha : ‖a‖ ≤ r) (hb : ‖b‖ ≤ r) : ‖a - b‖ ≤ r := by
  rw [sub_eq_add_neg]
  exact add_le ha (by rwa [norm_neg])

lemma norm_add_of_lt {a b : K} (h : ‖b‖ < ‖a‖) : ‖a + b‖ = ‖a‖ := by
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h.ne', max_eq_left h.le]

lemma norm_one_add {b : K} (h : ‖b‖ < 1) : ‖1 + b‖ = 1 := by
  have := norm_add_of_lt (a := (1 : K)) (b := b) (by simpa using h)
  simpa using this

omit [IsUltrametricDist K] in
lemma mul_le {a b : K} {r s : ℝ} (ha : ‖a‖ ≤ r) (hb : ‖b‖ ≤ s) : ‖a * b‖ ≤ r * s := by
  rw [norm_mul]
  exact mul_le_mul ha hb (norm_nonneg _) ((norm_nonneg _).trans ha)

omit [IsUltrametricDist K] in
lemma one_mul_le {a b : K} {s : ℝ} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ s) : ‖a * b‖ ≤ s := by
  simpa using mul_le ha hb

lemma norm_two_le : ‖(2 : K)‖ ≤ 1 := by
  simpa using IsUltrametricDist.norm_natCast_le_one K 2

lemma norm_three_le : ‖(3 : K)‖ ≤ 1 := by
  simpa using IsUltrametricDist.norm_natCast_le_one K 3

lemma norm_y_sq {A B x y : K} (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) (hx : 1 < ‖x‖)
    (h : y ^ 2 = x ^ 3 + A * x + B) : ‖y‖ ^ 2 = ‖x‖ ^ 3 := by
  have h1 : ‖A * x + B‖ ≤ ‖x‖ := add_le (one_mul_le hA le_rfl) (hB.trans hx.le)
  have h2 : ‖x‖ < ‖x ^ 3‖ := by
    rw [norm_pow]
    have : 0 < ‖x‖ := by linarith
    nlinarith [mul_pos this this]
  rw [← norm_pow, h, add_assoc, norm_add_of_lt (h1.trans_lt h2), norm_pow]

lemma coord_bounds {A B x y : K} {M : ℝ} (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) (hM : 1 < M)
    (hx : M ≤ ‖x‖) (h : y ^ 2 = x ^ 3 + A * x + B) :
    y ≠ 0 ∧ ‖x / y‖ ≤ √(M⁻¹) ∧ ‖1 / y‖ ≤ √(M⁻¹) := by
  have hx1 : 1 < ‖x‖ := hM.trans_le hx
  have hx0 : 0 < ‖x‖ := by linarith
  have hM0 : 0 < M := by linarith
  have hy := norm_y_sq hA hB hx1 h
  have hy0 : y ≠ 0 := by
    rintro rfl
    have : 0 < ‖x‖ ^ 3 := by positivity
    simp at hy
    linarith
  have hinv : ‖x‖⁻¹ ≤ M⁻¹ := inv_anti₀ hM0 hx
  refine ⟨hy0, Real.le_sqrt_of_sq_le ?_, Real.le_sqrt_of_sq_le ?_⟩
  · rw [norm_div, div_pow, hy]
    refine le_trans (le_of_eq ?_) hinv
    field_simp
  · rw [norm_div, div_pow, hy, norm_one, one_pow, one_div]
    refine le_trans (inv_anti₀ hx0 ?_) hinv
    nlinarith [mul_pos hx0 hx0]

lemma line_bounds {A B z₁ z₂ w₁ w₂ : K} {s : ℝ} (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) (hs : s < 1)
    (hz₁ : ‖z₁‖ ≤ s) (hz₂ : ‖z₂‖ ≤ s) (hw₁ : ‖w₁‖ ≤ s) (hw₂ : ‖w₂‖ ≤ s) :
    ∃ n : K, 1 - A * (z₁ * (w₁ + w₂)) - B * (w₁ * w₁ + w₁ * w₂ + w₂ * w₂) ≠ 0 ∧
      n * (1 - A * (z₁ * (w₁ + w₂)) - B * (w₁ * w₁ + w₁ * w₂ + w₂ * w₂)) =
        z₁ * z₁ + z₁ * z₂ + z₂ * z₂ + A * (w₂ * w₂) ∧
      ‖n‖ ≤ s * s ∧ ‖w₁ - n * z₁‖ ≤ s := by
  have hs0 : 0 ≤ s := (norm_nonneg _).trans hz₁
  have hss : s * s < 1 := by nlinarith
  have hD : ‖1 - A * (z₁ * (w₁ + w₂)) - B * (w₁ * w₁ + w₁ * w₂ + w₂ * w₂)‖ = 1 := by
    have h : ‖-(A * (z₁ * (w₁ + w₂)) + B * (w₁ * w₁ + w₁ * w₂ + w₂ * w₂))‖ < 1 := by
      rw [norm_neg]
      exact (add_le (one_mul_le hA (mul_le hz₁ (add_le hw₁ hw₂)))
        (one_mul_le hB (add_le (add_le (mul_le hw₁ hw₁) (mul_le hw₁ hw₂))
          (mul_le hw₂ hw₂)))).trans_lt hss
    rw [← norm_one_add h]
    congr 1
    ring
  have hD0 : 1 - A * (z₁ * (w₁ + w₂)) - B * (w₁ * w₁ + w₁ * w₂ + w₂ * w₂) ≠ 0 := by
    intro h
    rw [h] at hD
    simp at hD
  have hN : ‖z₁ * z₁ + z₁ * z₂ + z₂ * z₂ + A * (w₂ * w₂)‖ ≤ s * s :=
    add_le (add_le (add_le (mul_le hz₁ hz₁) (mul_le hz₁ hz₂)) (mul_le hz₂ hz₂))
      (one_mul_le hA (mul_le hw₂ hw₂))
  have hn : ‖(z₁ * z₁ + z₁ * z₂ + z₂ * z₂ + A * (w₂ * w₂)) /
      (1 - A * (z₁ * (w₁ + w₂)) - B * (w₁ * w₁ + w₁ * w₂ + w₂ * w₂))‖ ≤ s * s := by
    rw [norm_div, hD, div_one]
    exact hN
  exact ⟨_, hD0, div_mul_cancel₀ _ hD0, hn, sub_le hw₁ (one_mul_le (hn.trans hss.le) hz₁)⟩

lemma third_point {A B x₁ x₂ x₃ y₁ y₂ y₃ m n : K} {M : ℝ} (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1)
    (hM : 1 < M) (hx₁ : M ≤ ‖x₁‖) (hx₂ : M ≤ ‖x₂‖) (hm0 : m ≠ 0)
    (l₁ : m * y₁ + n * x₁ = 1) (l₂ : m * y₂ + n * x₂ = 1) (l₃ : m * y₃ + n * x₃ = 1)
    (e₁ : (x₁ + x₂ + x₃) * m ^ 2 = n ^ 2)
    (e₂ : (x₁ * x₂ + x₁ * x₃ + x₂ * x₃) * m ^ 2 = A * (m * m) + 2 * n)
    (e₃ : x₁ * x₂ * x₃ * m ^ 2 = 1 - B * (m * m))
    (hn : ‖n‖ ≤ M⁻¹) (hm : ‖m * m‖ ≤ M⁻¹) :
    M ≤ ‖x₃‖ ∧ ‖x₃ / (-y₃) - x₁ / y₁ - x₂ / y₂‖ ≤ M⁻¹ := by
  have hM0 : 0 < M := by linarith
  have hMi : M⁻¹ < 1 := inv_lt_one_of_one_lt₀ hM
  have hm1 : ‖m‖ ≤ 1 := by
    have := hm.trans hMi.le
    rw [norm_mul] at this
    nlinarith [norm_nonneg m]
  have hn1 : ‖n‖ ≤ 1 := hn.trans hMi.le
  have hx₁0 : x₁ ≠ 0 := norm_pos_iff.mp (hM0.trans_le hx₁)
  have hx₂0 : x₂ ≠ 0 := norm_pos_iff.mp (hM0.trans_le hx₂)
  have hE : ‖1 - B * (m * m)‖ = 1 := by
    rw [sub_eq_add_neg]
    exact norm_one_add (by rw [norm_neg]; exact (one_mul_le hB hm).trans_lt hMi)
  have hE0 : 1 - B * (m * m) ≠ 0 := by
    intro h
    rw [h] at hE
    simp at hE
  have hx₃0 : x₃ ≠ 0 := by
    rintro rfl
    apply hE0
    rw [← e₃]
    ring
  have hD : ‖1 + (A * (n * n) + B * (n * (n * n)))‖ = 1 :=
    norm_one_add ((add_le (one_mul_le hA (one_mul_le hn1 hn))
      (one_mul_le hB (one_mul_le hn1 (one_mul_le hn1 hn)))).trans_lt hMi)
  have hD0 : 1 + (A * (n * n) + B * (n * (n * n))) ≠ 0 := by
    intro h
    rw [h] at hD
    simp at hD
  have hm2 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm0
  have u₁ : m * y₁ = 1 - n * x₁ := by linear_combination l₁
  have u₂ : m * y₂ = 1 - n * x₂ := by linear_combination l₂
  have u₃ : m * y₃ = 1 - n * x₃ := by linear_combination l₃
  have hprod : (m * y₁) * (m * y₂) * (m * y₃) = 1 + (A * (n * n) + B * (n * (n * n))) := by
    rw [u₁, u₂, u₃]
    apply mul_right_cancel₀ hm2
    linear_combination (-n) * e₁ + n ^ 2 * e₂ - n ^ 3 * e₃
  have hsum : x₁ * ((m * y₂) * (m * y₃)) + x₂ * ((m * y₁) * (m * y₃)) +
      x₃ * ((m * y₁) * (m * y₂)) = -(n * (2 * A + 3 * (B * n))) := by
    rw [u₁, u₂, u₃]
    apply mul_right_cancel₀ hm2
    linear_combination e₁ - 2 * n * e₂ + 3 * n ^ 2 * e₃
  have hy₁ : y₁ ≠ 0 := by
    rintro rfl
    apply hD0
    rw [← hprod]
    ring
  have hy₂ : y₂ ≠ 0 := by
    rintro rfl
    apply hD0
    rw [← hprod]
    ring
  have hy₃ : y₃ ≠ 0 := by
    rintro rfl
    apply hD0
    rw [← hprod]
    ring
  constructor
  · have hinv : x₃⁻¹ = (A * (m * m) + 2 * n) / (1 - B * (m * m)) - x₁⁻¹ - x₂⁻¹ := by
      rw [← e₂, ← e₃]
      field_simp
      ring
    have hle : ‖x₃⁻¹‖ ≤ M⁻¹ := by
      rw [hinv]
      refine sub_le (sub_le ?_ ?_) ?_
      · rw [norm_div, hE, div_one]
        exact add_le (one_mul_le hA hm) (one_mul_le norm_two_le hn)
      · rw [norm_inv]
        exact inv_anti₀ hM0 hx₁
      · rw [norm_inv]
        exact inv_anti₀ hM0 hx₂
    rw [norm_inv] at hle
    exact (inv_le_inv₀ (norm_pos_iff.mpr hx₃0) hM0).mp hle
  · have key : x₃ / (-y₃) - x₁ / y₁ - x₂ / y₂ =
        m * (n * (2 * A + 3 * (B * n))) / (1 + (A * (n * n) + B * (n * (n * n)))) := by
      rw [← hprod, ← neg_neg (n * (2 * A + 3 * (B * n))), ← hsum]
      field_simp
      ring
    rw [key, norm_div, hD, div_one, mul_comm n]
    exact one_mul_le hm1 (one_mul_le (add_le (one_mul_le norm_two_le hA)
      (one_mul_le norm_three_le (one_mul_le hB hn1))) hn)

lemma chord {A B x₁ x₂ y₁ y₂ l : K} {M : ℝ} (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1)
    (hM : 1 < M) (hx₁ : M ≤ ‖x₁‖) (hx₂ : M ≤ ‖x₂‖)
    (c₁ : y₁ ^ 2 = x₁ ^ 3 + A * x₁ + B) (c₂ : y₂ ^ 2 = x₂ ^ 3 + A * x₂ + B)
    (hl : (x₁ ≠ x₂ ∧ l * (x₁ - x₂) = y₁ - y₂) ∨
      (x₁ = x₂ ∧ y₁ = y₂ ∧ 2 * y₁ ≠ 0 ∧ l * (2 * y₁) = 3 * x₁ ^ 2 + A)) :
    M ≤ ‖l ^ 2 - x₁ - x₂‖ ∧
      ‖(l ^ 2 - x₁ - x₂) / (-(l * (l ^ 2 - x₁ - x₂ - x₁) + y₁)) - x₁ / y₁ - x₂ / y₂‖ ≤ M⁻¹ := by
  have hM0 : 0 < M := by linarith
  have hMi : M⁻¹ < 1 := inv_lt_one_of_one_lt₀ hM
  have hMi0 : 0 ≤ M⁻¹ := by positivity
  have hs : √(M⁻¹) < 1 := by
    rw [Real.sqrt_lt' one_pos]
    simpa using hMi
  have hss : √(M⁻¹) * √(M⁻¹) = M⁻¹ := Real.mul_self_sqrt hMi0
  obtain ⟨hy₁, hz₁, hw₁⟩ := coord_bounds hA hB hM hx₁ c₁
  obtain ⟨hy₂, hz₂, hw₂⟩ := coord_bounds hA hB hM hx₂ c₂
  obtain ⟨n, hD0, hnD, hn, hm⟩ := line_bounds hA hB hs hz₁ hz₂ hw₁ hw₂
  rw [hss] at hn
  have hmm := mul_le hm hm
  rw [hss] at hmm
  have d₁ : 1 / y₁ = (x₁ / y₁) ^ 3 + A * (x₁ / y₁) * (1 / y₁) ^ 2 + B * (1 / y₁) ^ 3 := by
    field_simp
    linear_combination c₁
  have d₂ : 1 / y₂ = (x₂ / y₂) ^ 3 + A * (x₂ / y₂) * (1 / y₂) ^ 2 + B * (1 / y₂) ^ 3 := by
    field_simp
    linear_combination c₂
  have p₁ : x₁ / y₁ * y₁ = x₁ := div_mul_cancel₀ _ hy₁
  have p₂ : x₂ / y₂ * y₂ = x₂ := div_mul_cancel₀ _ hy₂
  have q₁ : 1 / y₁ * y₁ = 1 := div_mul_cancel₀ _ hy₁
  have q₂ : 1 / y₂ * y₂ = 1 := div_mul_cancel₀ _ hy₂
  have hslope : 1 / y₂ - 1 / y₁ = n * (x₂ / y₂ - x₁ / y₁) := by
    apply mul_right_cancel₀ hD0
    linear_combination d₂ - d₁ - (x₂ / y₂ - x₁ / y₁) * hnD
  obtain ⟨m, hmdef⟩ : ∃ m, m = 1 / y₁ - n * (x₁ / y₁) := ⟨_, rfl⟩
  rw [← hmdef] at hmm
  have l₁ : m * y₁ + n * x₁ = 1 := by
    linear_combination y₁ * hmdef + q₁ - n * p₁
  have l₂ : m * y₂ + n * x₂ = 1 := by
    linear_combination y₂ * hmdef - y₂ * hslope + q₂ - n * p₂
  have hline : y₂ = l * (x₂ - x₁) + y₁ := by
    rcases hl with ⟨_, h⟩ | ⟨h, h', _⟩
    · linear_combination h
    · rw [h, h']
      ring
  have hml : m ≠ 0 ∧ l * m = -n := by
    rcases hl with ⟨hne, h⟩ | ⟨h, h', h2, hl⟩
    · have hsub : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hne
      constructor
      · rintro rfl
        apply hsub
        linear_combination x₁ * l₂ * (-1) + x₂ * l₁
      · apply mul_right_cancel₀ hsub
        linear_combination m * h + l₁ - l₂
    · subst h h'
      have hmD : m * (1 - A * (x₁ / y₁ * (1 / y₁ + 1 / y₁)) -
          B * (1 / y₁ * (1 / y₁) + 1 / y₁ * (1 / y₁) + 1 / y₁ * (1 / y₁))) = -2 * (1 / y₁) := by
        rw [hmdef]
        linear_combination 3 * d₁ - (x₁ / y₁) * hnD
      have hlw : l * 2 = (3 * x₁ ^ 2 + A) / y₁ := by
        rw [eq_div_iff hy₁]
        linear_combination hl
      constructor
      · rintro rfl
        apply h2
        linear_combination y₁ ^ 2 * hmD - 2 * y₁ * q₁
      · apply mul_right_cancel₀ hD0
        linear_combination l * hmD + hnD - (1 / y₁) * hlw
  obtain ⟨hm0, hlm⟩ := hml
  have hα : A - 2 * l * (y₁ - l * x₁) =
      x₁ * x₂ + x₁ * (l ^ 2 - x₁ - x₂) + x₂ * (l ^ 2 - x₁ - x₂) := by
    rcases hl with ⟨hne, h⟩ | ⟨h, h', h2, hl⟩
    · apply mul_right_cancel₀ (sub_ne_zero.mpr hne)
      rw [hline] at c₂
      linear_combination c₂ - c₁
    · subst h h'
      linear_combination (-1) * hl
  have hβ : x₁ * x₂ * (l ^ 2 - x₁ - x₂) = (y₁ - l * x₁) ^ 2 - B := by
    linear_combination x₁ * hα * (-1) - c₁
  have hc : (y₁ - l * x₁) * m = 1 := by
    linear_combination l₁ - x₁ * hlm
  have hn' : n = -(l * m) := by linear_combination hlm
  refine third_point hA hB hM hx₁ hx₂ hm0 l₁ l₂ ?_ ?_ ?_ ?_ hn hmm
  · linear_combination hc + (l ^ 2 - x₁ - x₂) * hlm
  · rw [hn']
    ring
  · rw [← hα, hn']
    linear_combination (-2 * l * m) * hc
  · rw [hβ]
    linear_combination ((y₁ - l * x₁) * m + 1) * hc

end aux

theorem large_add : (let d1 : {K : Type} → [inst : NormedField K] → {W : WeierstrassCurve.Affine K} → ℝ → WeierstrassCurve.Affine.Point W → Prop := @(fun {K : Type} [NormedField K] {W : WeierstrassCurve.Affine K} (M : ℝ) (x : WeierstrassCurve.Affine.Point W) ↦ match x with | WeierstrassCurve.Affine.Point.zero => True | WeierstrassCurve.Affine.Point.some x y h => M ≤ ‖x‖); let d2 : {K : Type} → [inst : NormedField K] → {W : WeierstrassCurve.Affine K} → WeierstrassCurve.Affine.Point W → K := @(fun {K : Type} [NormedField K] {W : WeierstrassCurve.Affine K} (x : WeierstrassCurve.Affine.Point W) ↦ match x with | WeierstrassCurve.Affine.Point.zero => (0 : K) | WeierstrassCurve.Affine.Point.some x y h => x / y); ∀ {K : Type} [inst : NormedField K] [IsUltrametricDist K] [inst_2 : DecidableEq K] {A B : K} {M : ℝ}, ‖A‖ ≤ (1 : ℝ) → ‖B‖ ≤ (1 : ℝ) → (1 : ℝ) < M → ∀ (P Q : WeierstrassCurve.Affine.Point (WeierstrassCurve.toAffine { a₁ := (0 : K), a₂ := (0 : K), a₃ := (0 : K), a₄ := A, a₆ := B : WeierstrassCurve K })), d1 M P → d1 M Q → d1 M (P + Q) ∧ ‖d2 (P + Q) - d2 P - d2 Q‖ ≤ M⁻¹) := by
  intro d1 d2 K _ _ _ A B M hA hB hM P Q hP hQ
  have hMi0 : 0 ≤ M⁻¹ := inv_nonneg.mpr (by linarith)
  have z2 : d2 (0 : WeierstrassCurve.Affine.Point (WeierstrassCurve.toAffine
    { a₁ := (0 : K), a₂ := (0 : K), a₃ := (0 : K), a₄ := A, a₆ := B : WeierstrassCurve K })) = 0 :=
    rfl
  rcases P with _ | ⟨x₁, y₁, h₁⟩
  · change d1 M (0 + Q) ∧ ‖d2 (0 + Q) - 0 - d2 Q‖ ≤ M⁻¹
    rw [zero_add]
    exact ⟨hQ, by simpa using hMi0⟩
  rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · change d1 M (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ + 0) ∧
      ‖d2 (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ + 0) -
        d2 (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁) - 0‖ ≤ M⁻¹
    rw [add_zero]
    exact ⟨hP, by simpa using hMi0⟩
  have hx₁ : M ≤ ‖x₁‖ := hP
  have hx₂ : M ≤ ‖x₂‖ := hQ
  have c₁ : y₁ ^ 2 = x₁ ^ 3 + A * x₁ + B := by
    have := (WeierstrassCurve.Affine.equation_iff _ _).mp h₁.1
    simpa using this
  have c₂ : y₂ ^ 2 = x₂ ^ 3 + A * x₂ + B := by
    have := (WeierstrassCurve.Affine.equation_iff _ _).mp h₂.1
    simpa using this
  by_cases hxy : x₁ = x₂ ∧ y₁ = (WeierstrassCurve.toAffine
    { a₁ := (0 : K), a₂ := (0 : K), a₃ := (0 : K), a₄ := A, a₆ := B : WeierstrassCurve K }).negY x₂ y₂
  · rw [WeierstrassCurve.Affine.Point.add_of_Y_eq hxy.1 hxy.2, z2]
    refine ⟨trivial, ?_⟩
    change ‖0 - x₁ / y₁ - x₂ / y₂‖ ≤ M⁻¹
    have hy : y₁ = -y₂ := by simpa using hxy.2
    rw [hxy.1, hy, div_neg]
    simpa using hMi0
  · rw [WeierstrassCurve.Affine.Point.add_some hxy]
    have key := chord (l := (WeierstrassCurve.toAffine
      { a₁ := (0 : K), a₂ := (0 : K), a₃ := (0 : K), a₄ := A, a₆ := B : WeierstrassCurve K }).slope
        x₁ x₂ y₁ y₂) hA hB hM hx₁ hx₂ c₁ c₂ (by
      by_cases hx : x₁ = x₂
      · right
        have hy := fun h => hxy ⟨hx, h⟩
        have hyy := WeierstrassCurve.Affine.Y_eq_of_Y_ne h₁.1 h₂.1 hx hy
        have h2 : 2 * y₁ ≠ 0 := by
          intro h
          apply hy
          simp only [WeierstrassCurve.Affine.negY, zero_mul, sub_zero]
          linear_combination h - hyy
        refine ⟨hx, hyy, h2, ?_⟩
        rw [WeierstrassCurve.Affine.slope_of_Y_ne hx hy]
        simp only [WeierstrassCurve.Affine.negY, zero_mul, mul_zero, sub_zero, add_zero]
        rw [show y₁ - -y₁ = 2 * y₁ by ring, div_mul_cancel₀ _ h2]
      · left
        refine ⟨hx, ?_⟩
        rw [WeierstrassCurve.Affine.slope_of_X_ne hx, div_mul_cancel₀ _ (sub_ne_zero.mpr hx)])
    simp only [d1, d2, WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY,
      WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.addX, zero_mul, sub_zero, add_zero]
    exact key

end GlobalTheory.UltrametricLineBounds
