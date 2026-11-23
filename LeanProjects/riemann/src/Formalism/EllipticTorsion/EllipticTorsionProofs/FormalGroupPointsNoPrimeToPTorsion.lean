import Mathlib
import Formalism.EllipticTorsion.FormalGroupPointsTorsionFree

noncomputable section

universe u

namespace Formalism.ELL.FormalGroupPointsTorsion

open WeierstrassCurve Polynomial

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

lemma add_le {a b : K} {c : ℝ} (ha : ‖a‖ ≤ c) (hb : ‖b‖ ≤ c) : ‖a + b‖ ≤ c :=
  (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)

lemma sub_le {a b : K} {c : ℝ} (ha : ‖a‖ ≤ c) (hb : ‖b‖ ≤ c) : ‖a - b‖ ≤ c := by
  rw [sub_eq_add_neg]; exact add_le ha (by rwa [norm_neg])

lemma add_lt {a b : K} {c : ℝ} (ha : ‖a‖ < c) (hb : ‖b‖ < c) : ‖a + b‖ < c :=
  (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ha hb)

lemma sub_lt {a b : K} {c : ℝ} (ha : ‖a‖ < c) (hb : ‖b‖ < c) : ‖a - b‖ < c := by
  rw [sub_eq_add_neg]; exact add_lt ha (by rwa [norm_neg])

lemma dom {a b : K} (h : ‖b‖ < ‖a‖) : ‖a + b‖ = ‖a‖ := by
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h.ne']
  exact max_eq_left h.le

lemma mul_le_of_one {a b : K} (ha : ‖a‖ ≤ 1) : ‖a * b‖ ≤ ‖b‖ := by
  rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) ha

lemma two_le : ‖(2 : K)‖ ≤ 1 := by
  simpa using IsUltrametricDist.norm_natCast_le_one K 2

lemma three_le : ‖(3 : K)‖ ≤ 1 := by
  simpa using IsUltrametricDist.norm_natCast_le_one K 3

variable {W : WeierstrassCurve K}

lemma vy (hW : IntegralModel W) {x y : K} (h : W.toAffine.Equation x y) (hx : 1 < ‖x‖) :
    ‖y‖ ^ 2 = ‖x‖ ^ 3 ∧ ‖x‖ < ‖y‖ := by
  obtain ⟨h1, h2, h3, h4, h6⟩ := hW
  rw [Affine.equation_iff] at h
  have key : y ^ 2 + (W.a₁ * x + W.a₃) * y = x ^ 3 + (W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) := by
    linear_combination h
  have hX0 : 0 ≤ ‖x‖ := norm_nonneg _
  have hc : ‖W.a₁ * x + W.a₃‖ ≤ ‖x‖ := add_le (mul_le_of_one h1) (h3.trans hx.le)
  have hXX : ‖x‖ ≤ ‖x‖ ^ 2 := by nlinarith
  have hr : ‖W.a₂ * x ^ 2 + W.a₄ * x + W.a₆‖ ≤ ‖x‖ ^ 2 := by
    refine add_le (add_le ?_ ?_) ?_
    · exact (mul_le_of_one h2).trans (by rw [norm_pow])
    · exact (mul_le_of_one h4).trans hXX
    · nlinarith
  have hR : ‖x ^ 3 + (W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)‖ = ‖x‖ ^ 3 := by
    have : ‖W.a₂ * x ^ 2 + W.a₄ * x + W.a₆‖ < ‖x ^ 3‖ := by
      rw [norm_pow]; nlinarith
    rw [dom this, norm_pow]
  have hyx : ‖x‖ < ‖y‖ := by
    by_contra hle
    push_neg at hle
    have : ‖y ^ 2 + (W.a₁ * x + W.a₃) * y‖ ≤ ‖x‖ ^ 2 := by
      refine add_le ?_ ?_
      · rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hle 2
      · rw [norm_mul, sq]; exact mul_le_mul hc hle (norm_nonneg _) hX0
    rw [key, hR] at this
    nlinarith
  refine ⟨?_, hyx⟩
  have hlt : ‖(W.a₁ * x + W.a₃) * y‖ < ‖y ^ 2‖ := by
    rw [norm_mul, norm_pow, sq]
    exact mul_lt_mul_of_pos_right (hc.trans_lt hyx) (by linarith)
  have : ‖y ^ 2 + (W.a₁ * x + W.a₃) * y‖ = ‖y‖ ^ 2 := by rw [dom hlt, norm_pow]
  rw [← this, key, hR]

lemma zfacts (hW : IntegralModel W) {x y : K} (h : W.toAffine.Equation x y) (hx : 1 < ‖x‖) :
    y ≠ 0 ∧ 0 < ‖x / y‖ ∧ ‖x / y‖ < 1 ∧ ‖x / y‖ ^ 2 * ‖x‖ = 1 := by
  obtain ⟨hy2, hxy⟩ := vy hW h hx
  have hYp : 0 < ‖y‖ := by linarith
  have hy0 : y ≠ 0 := norm_pos_iff.mp hYp
  refine ⟨hy0, ?_, ?_, ?_⟩
  · rw [norm_div]; exact div_pos (by linarith) hYp
  · rw [norm_div, div_lt_one hYp]; exact hxy
  · rw [norm_div, div_pow]
    field_simp
    nlinarith [hy2]

lemma negz (hW : IntegralModel W) {x y : K} (h : W.toAffine.Equation x y) (hx : 1 < ‖x‖) :
    ‖x / W.toAffine.negY x y + x / y‖ ≤ ‖x / y‖ ^ 2 := by
  obtain ⟨hy2, hxy⟩ := vy hW h hx
  have hy0 : y ≠ 0 := norm_pos_iff.mp (by linarith)
  have hc : ‖W.a₁ * x + W.a₃‖ ≤ ‖x‖ := add_le (mul_le_of_one hW.1) (hW.2.2.1.trans hx.le)
  have hn : W.toAffine.negY x y = -y + -(W.a₁ * x + W.a₃) := by
    simp only [Affine.negY]; ring
  have hnn : ‖W.toAffine.negY x y‖ = ‖y‖ := by
    have : ‖-(W.a₁ * x + W.a₃)‖ < ‖-y‖ := by rw [norm_neg, norm_neg]; linarith
    rw [hn, dom this, norm_neg]
  have hn0 : W.toAffine.negY x y ≠ 0 := norm_pos_iff.mp (by rw [hnn]; linarith)
  rw [div_add_div _ _ hn0 hy0]
  have : x * y + W.toAffine.negY x y * x = x * (-(W.a₁ * x + W.a₃)) := by rw [hn]; ring
  rw [this, norm_div, norm_mul, norm_mul, norm_neg, hnn, norm_div, div_pow, sq, sq]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_left hc (norm_nonneg _)

lemma lsq {l a b : K} {M : ℝ} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hM : 1 ≤ M)
    (h : ‖l ^ 2 + a * l - b‖ ≤ M) : ‖l‖ ^ 2 ≤ M := by
  by_cases hL : ‖l‖ ≤ 1
  · exact (pow_le_one₀ (norm_nonneg _) hL).trans hM
  · push_neg at hL
    have h1 : ‖a * l - b‖ < ‖l ^ 2‖ := by
      have : ‖a * l - b‖ ≤ ‖l‖ := sub_le (mul_le_of_one ha) (hb.trans hL.le)
      rw [norm_pow]; nlinarith
    rw [add_sub_assoc, dom h1, norm_pow] at h
    exact h

lemma realC {L V M : ℝ} (hL0 : 0 ≤ L) (hV0 : 0 ≤ V) (hLM : L ^ 2 ≤ M) (hM : 1 ≤ M)
    (hV : V ≤ max 1 L) : L ≤ M ∧ V ≤ M ∧ L * V ≤ M := by
  rcases le_total L 1 with h | h
  · have hV' : V ≤ 1 := by rw [max_eq_left h] at hV; exact hV
    refine ⟨by linarith, by linarith, ?_⟩
    nlinarith
  · have hV' : V ≤ L := by rw [max_eq_right h] at hV; exact hV
    refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

lemma bigx3 (hW : IntegralModel W) {x1 x2 x3 y3 l v : K} (hX1 : 1 < ‖x1‖) (hX2 : 1 < ‖x2‖)
    (h3 : W.toAffine.Equation x3 y3) (hy3 : y3 = l * x3 + v)
    (e1 : l ^ 2 + W.a₁ * l - W.a₂ = x1 + x2 + x3)
    (e2 : W.a₄ - 2 * l * v - W.a₁ * v - W.a₃ * l = x1 * x2 + x3 * (x1 + x2)) : 1 < ‖x3‖ := by
  by_contra hx3
  push_neg at hx3
  obtain ⟨h1, h2, h3', h4, h6⟩ := hW
  have hy3n : ‖y3‖ ≤ 1 := by

    rw [Affine.equation_iff] at h3
    by_contra hy
    push_neg at hy
    have key : y3 ^ 2 = -((W.a₁ * x3 + W.a₃) * y3) + (x3 ^ 3 + W.a₂ * x3 ^ 2 + W.a₄ * x3 + W.a₆) := by
      linear_combination h3
    have hA : ‖W.a₁ * x3 + W.a₃‖ ≤ 1 := add_le ((mul_le_of_one h1).trans hx3) h3'
    have hx2 : ‖x3‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) hx3
    have hB : ‖x3 ^ 3 + W.a₂ * x3 ^ 2 + W.a₄ * x3 + W.a₆‖ ≤ 1 := by
      refine add_le (add_le (add_le ?_ ?_) ?_) h6
      · rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx3
      · exact (mul_le_of_one h2).trans (by rw [norm_pow]; exact hx2)
      · exact (mul_le_of_one h4).trans hx3
    have hR : ‖-((W.a₁ * x3 + W.a₃) * y3) + (x3 ^ 3 + W.a₂ * x3 ^ 2 + W.a₄ * x3 + W.a₆)‖ ≤ ‖y3‖ := by
      refine add_le ?_ (hB.trans hy.le)
      rw [norm_neg, norm_mul]; nlinarith [norm_nonneg (W.a₁ * x3 + W.a₃), norm_nonneg y3]
    rw [← key, norm_pow] at hR
    nlinarith
  set M := max ‖x1‖ ‖x2‖ with hMdef
  have hM1 : 1 < M := lt_max_of_lt_left hX1
  have hs : ‖x1 + x2 + x3‖ ≤ M :=
    add_le (add_le (le_max_left _ _) (le_max_right _ _)) (hx3.trans hM1.le)
  have hL : ‖l‖ ^ 2 ≤ M := lsq h1 h2 hM1.le (by rw [e1]; exact hs)
  have hv : v = y3 - l * x3 := by rw [hy3]; ring
  have hV : ‖v‖ ≤ max 1 ‖l‖ := by
    rw [hv]
    refine sub_le (hy3n.trans (le_max_left _ _)) ?_
    rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) hx3).trans (le_max_right _ _)
  obtain ⟨hLM, hVM, hLVM⟩ := realC (norm_nonneg _) (norm_nonneg _) hL hM1.le hV
  have hlhs : ‖W.a₄ - 2 * l * v - W.a₁ * v - W.a₃ * l‖ ≤ M := by
    refine sub_le (sub_le (sub_le (h4.trans hM1.le) ?_) ((mul_le_of_one h1).trans hVM))
      ((mul_le_of_one h3').trans hLM)
    rw [mul_assoc]; exact (mul_le_of_one two_le).trans (by rw [norm_mul]; exact hLVM)
  have hprod : M < ‖x1 * x2‖ := by
    rw [norm_mul]
    rcases le_total ‖x1‖ ‖x2‖ with h | h
    · rw [hMdef, max_eq_right h]; nlinarith
    · rw [hMdef, max_eq_left h]; nlinarith
  have hsmall : ‖x3 * (x1 + x2)‖ < ‖x1 * x2‖ := by
    have : ‖x3 * (x1 + x2)‖ ≤ M := by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) hx3 |>.trans
        (add_le (le_max_left _ _) (le_max_right _ _))
    linarith
  have := dom hsmall
  rw [← e2] at this
  linarith

lemma realB {t1 t2 X1 X2 X3 V L : ℝ} (ht1 : 0 < t1) (ht2 : 0 < t2)
    (h1 : t1 ^ 2 * X1 = 1) (h2 : t2 ^ 2 * X2 = 1)
    (hX1 : 1 < X1) (hX2 : 1 < X2) (hX3 : 1 < X3) (hV0 : 0 ≤ V) (hV : V ^ 2 = X1 * X2 * X3)
    (hL0 : 0 ≤ L) (hL : L ^ 2 ≤ max (max X1 X2) X3) :
    1 < max t1 t2 * V ∧ L < max t1 t2 * V := by
  set S := max t1 t2
  have hS1 : t1 ≤ S := le_max_left _ _
  have hS2 : t2 ≤ S := le_max_right _ _
  have hSV0 : 0 ≤ S * V := mul_nonneg (ht1.le.trans hS1) hV0
  have hA : X2 * X3 ≤ (S * V) ^ 2 := by
    have : t1 ^ 2 ≤ S ^ 2 := pow_le_pow_left₀ ht1.le hS1 2
    have : X2 * X3 = t1 ^ 2 * V ^ 2 := by rw [hV]; linear_combination (-(X2 * X3)) * h1
    rw [this, mul_pow]; exact mul_le_mul_of_nonneg_right (by assumption) (sq_nonneg _)
  have hB : X1 * X3 ≤ (S * V) ^ 2 := by
    have : t2 ^ 2 ≤ S ^ 2 := pow_le_pow_left₀ ht2.le hS2 2
    have : X1 * X3 = t2 ^ 2 * V ^ 2 := by rw [hV]; linear_combination (-(X1 * X3)) * h2
    rw [this, mul_pow]; exact mul_le_mul_of_nonneg_right (by assumption) (sq_nonneg _)
  constructor
  · have : 1 < (S * V) ^ 2 := by nlinarith
    by_contra hc; push_neg at hc
    nlinarith
  · have : L ^ 2 < (S * V) ^ 2 := by
      refine hL.trans_lt ?_
      refine max_lt (max_lt ?_ ?_) ?_ <;> nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 hSV0 this

lemma sumz (hW : IntegralModel W) {x1 x2 x3 y1 y2 y3 l v : K}
    (hX1 : 1 < ‖x1‖) (hX2 : 1 < ‖x2‖) (hX3 : 1 < ‖x3‖)
    (hE1 : W.toAffine.Equation x1 y1) (hE2 : W.toAffine.Equation x2 y2)
    (hE3 : W.toAffine.Equation x3 y3)
    (e1 : l ^ 2 + W.a₁ * l - W.a₂ = x1 + x2 + x3)
    (e3 : v ^ 2 + W.a₃ * v - W.a₆ = x1 * x2 * x3)
    (hN : x1 * y2 * y3 + x2 * y1 * y3 + x3 * y1 * y2 =
      -(W.a₁ * (l * v ^ 2)) - W.a₂ * v ^ 2 + W.a₃ * (l ^ 2 * v) + (2 * W.a₄) * (l * v)
        - (3 * W.a₆) * l ^ 2) :
    ‖x1 / y1 + x2 / y2 + x3 / y3‖ < max ‖x1 / y1‖ ‖x2 / y2‖ := by
  obtain ⟨hy10, ht1, ht1', hq1⟩ := zfacts hW hE1 hX1
  obtain ⟨hy20, ht2, ht2', hq2⟩ := zfacts hW hE2 hX2
  obtain ⟨hy30, -, -, -⟩ := zfacts hW hE3 hX3
  have hY1 := (vy hW hE1 hX1).1
  have hY2 := (vy hW hE2 hX2).1
  have hY3 := (vy hW hE3 hX3).1
  obtain ⟨h1, h2, h3, h4, h6⟩ := hW

  have hP : 1 < ‖x1 * x2 * x3‖ := by
    rw [norm_mul, norm_mul]
    have : 1 < ‖x1‖ * ‖x2‖ := by nlinarith
    nlinarith
  have hV1 : 1 < ‖v‖ := by
    by_contra hc; push_neg at hc
    have : ‖v ^ 2 + W.a₃ * v - W.a₆‖ ≤ 1 :=
      sub_le (add_le (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hc)
        ((mul_le_of_one h3).trans hc)) h6
    rw [e3] at this; linarith
  have hV : ‖v‖ ^ 2 = ‖x1‖ * ‖x2‖ * ‖x3‖ := by
    have hlt : ‖W.a₃ * v - W.a₆‖ < ‖v ^ 2‖ := by
      have : ‖W.a₃ * v - W.a₆‖ ≤ ‖v‖ := sub_le (mul_le_of_one h3) (h6.trans hV1.le)
      rw [norm_pow]; nlinarith
    have := dom hlt
    rw [← add_sub_assoc, e3, norm_pow, norm_mul, norm_mul] at this
    exact this.symm

  have hL : ‖l‖ ^ 2 ≤ max (max ‖x1‖ ‖x2‖) ‖x3‖ := by
    refine lsq h1 h2 ((hX1.le.trans (le_max_left _ _)).trans (le_max_left _ _)) ?_
    rw [e1]
    refine add_le (add_le ?_ ?_) (le_max_right _ _)
    · exact (le_max_left _ _).trans (le_max_left _ _)
    · exact (le_max_right _ _).trans (le_max_left _ _)
  obtain ⟨hSV, hLSV⟩ := realB ht1 ht2 hq1 hq2 hX1 hX2 hX3 (norm_nonneg _) hV (norm_nonneg _) hL
  set S := max ‖x1 / y1‖ ‖x2 / y2‖ with hSdef
  have hS0 : 0 < S := lt_max_of_lt_left ht1
  have hS1 : S < 1 := max_lt ht1' ht2'

  have hYp : ‖y1 * y2 * y3‖ = ‖v‖ ^ 3 := by
    rw [norm_mul, norm_mul]
    rw [← pow_left_inj₀ (by positivity) (by positivity) (two_ne_zero)]
    rw [mul_pow, mul_pow, hY1, hY2, hY3]
    have : (‖v‖ ^ 3) ^ 2 = (‖v‖ ^ 2) ^ 3 := by ring
    rw [this, hV]; ring
  set V := ‖v‖
  set L := ‖l‖
  have hV0 : 0 < V := by linarith
  have hB : ‖x1 * y2 * y3 + x2 * y1 * y3 + x3 * y1 * y2‖ < S * V ^ 3 := by
    rw [hN]
    have hLV : L * V < S * V * V := mul_lt_mul_of_pos_right hLSV hV0
    have hL2 : L ^ 2 < (S * V) ^ 2 := pow_lt_pow_left₀ hLSV (norm_nonneg _) two_ne_zero
    have hS1' : S ≤ V := by linarith
    have hSV2 : S * S * V ^ 2 ≤ S * V ^ 3 := by
      have : S * S * V ^ 2 ≤ S * V * V ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hS1' hS0.le) (by positivity)
      linarith [show S * V * V ^ 2 = S * V ^ 3 by ring]
    have h2a4 : ‖2 * W.a₄‖ ≤ 1 := by
      rw [norm_mul]; exact mul_le_one₀ two_le (norm_nonneg _) h4
    have h3a6 : ‖3 * W.a₆‖ ≤ 1 := by
      rw [norm_mul]; exact mul_le_one₀ three_le (norm_nonneg _) h6
    refine sub_lt (add_lt (add_lt (sub_lt ?_ ?_) ?_) ?_) ?_
    · rw [norm_neg]
      refine (mul_le_of_one h1).trans_lt ?_
      rw [norm_mul, norm_pow]
      have := mul_lt_mul_of_pos_right hLSV (pow_pos hV0 2)
      linarith [show S * V * V ^ 2 = S * V ^ 3 by ring]
    · refine (mul_le_of_one h2).trans_lt ?_
      rw [norm_pow]
      have := mul_lt_mul_of_pos_right hSV (pow_pos hV0 2)
      linarith [show S * V * V ^ 2 = S * V ^ 3 by ring]
    · refine (mul_le_of_one h3).trans_lt ?_
      rw [norm_mul, norm_pow]
      have := mul_lt_mul_of_pos_right hL2 hV0
      linarith [show (S * V) ^ 2 * V = S * S * V ^ 2 * V by ring,
        mul_le_mul_of_nonneg_right hSV2 hV0.le, show S * V ^ 3 * V = S * V ^ 3 * V by ring,
        show S * S * V ^ 2 * V ≤ S * V ^ 3 * 1 by
          have : S * S * V ^ 2 * V ≤ S * S * V ^ 2 * V := le_rfl
          nlinarith [mul_pos hS0 hS0, pow_pos hV0 3]]
    · refine (mul_le_of_one h2a4).trans_lt ?_
      rw [norm_mul]
      have : S * V * V ≤ S * V * V * V := le_mul_of_one_le_right (by positivity) hV1.le
      linarith [show S * V * V * V = S * V ^ 3 by ring]
    · refine (mul_le_of_one h3a6).trans_lt ?_
      rw [norm_pow]
      linarith [show (S * V) ^ 2 = S * S * V ^ 2 by ring]
  have hsum : x1 / y1 + x2 / y2 + x3 / y3 =
      (x1 * y2 * y3 + x2 * y1 * y3 + x3 * y1 * y2) / (y1 * y2 * y3) := by
    field_simp
  rw [hsum, norm_div, hYp, div_lt_iff₀ (by positivity)]
  exact hB

lemma chord [DecidableEq K] (hW : IntegralModel W) {x1 x2 y1 y2 : K}
    (h1 : W.toAffine.Equation x1 y1) (h2 : W.toAffine.Equation x2 y2)
    (hX1 : 1 < ‖x1‖) (hX2 : 1 < ‖x2‖) (hxy : ¬(x1 = x2 ∧ y1 = W.toAffine.negY x2 y2)) :
    1 < ‖W.toAffine.addX x1 x2 (W.toAffine.slope x1 x2 y1 y2)‖ ∧
    ‖W.toAffine.addX x1 x2 (W.toAffine.slope x1 x2 y1 y2) /
        W.toAffine.addY x1 x2 y1 (W.toAffine.slope x1 x2 y1 y2) - x1 / y1 - x2 / y2‖ <
      max ‖x1 / y1‖ ‖x2 / y2‖ := by
  have hp := W.toAffine.addPolynomial_slope h1 h2 hxy
  rw [Affine.addPolynomial_eq, neg_inj, Cubic.prod_X_sub_C_eq, Cubic.toPoly_injective] at hp
  have h3 := W.toAffine.equation_negAdd h1 h2 hxy
  have hl2 : y2 = W.toAffine.slope x1 x2 y1 y2 * (x2 - x1) + y1 := by
    by_cases hx : x1 = x2
    · have hy := Affine.Y_eq_of_Y_ne h1 h2 hx (fun h => hxy ⟨hx, h⟩)
      rw [hx, hy]; ring
    · rw [Affine.slope_of_X_ne hx]
      field_simp [sub_ne_zero.mpr hx]
      ring
  rw [Affine.addY]
  generalize W.toAffine.slope x1 x2 y1 y2 = l at hp h3 hl2 ⊢
  have hx3 : W.toAffine.addX x1 x2 l = l ^ 2 + W.a₁ * l - W.a₂ - x1 - x2 := rfl
  have hy3 : W.toAffine.negAddY x1 x2 y1 l = l * (W.toAffine.addX x1 x2 l - x1) + y1 := rfl
  generalize W.toAffine.negAddY x1 x2 y1 l = y3 at h3 hy3 ⊢
  generalize W.toAffine.addX x1 x2 l = x3 at hp h3 hy3 hx3 ⊢
  simp only [Cubic.mk.injEq] at hp
  obtain ⟨-, -, hc, hd⟩ := hp
  obtain ⟨v, hv⟩ : ∃ v, v = y1 - l * x1 := ⟨_, rfl⟩
  have e1 : l ^ 2 + W.a₁ * l - W.a₂ = x1 + x2 + x3 := by rw [hx3]; ring
  have e2 : W.a₄ - 2 * l * v - W.a₁ * v - W.a₃ * l = x1 * x2 + x3 * (x1 + x2) := by
    rw [hv]; linear_combination hc
  have e3 : v ^ 2 + W.a₃ * v - W.a₆ = x1 * x2 * x3 := by
    rw [hv]; linear_combination -hd
  have hy1' : y1 = l * x1 + v := by rw [hv]; ring
  have hy2' : y2 = l * x2 + v := by rw [hl2, hv]; ring
  have hy3' : y3 = l * x3 + v := by rw [hy3, hv]; ring
  have hX3 := bigx3 hW hX1 hX2 h3 hy3' e1 e2
  refine ⟨hX3, ?_⟩
  have hN : x1 * y2 * y3 + x2 * y1 * y3 + x3 * y1 * y2 =
      -(W.a₁ * (l * v ^ 2)) - W.a₂ * v ^ 2 + W.a₃ * (l ^ 2 * v) + (2 * W.a₄) * (l * v)
        - (3 * W.a₆) * l ^ 2 := by
    rw [hy1', hy2', hy3']
    linear_combination (-3 * l ^ 2) * e3 - (2 * l * v) * e2 - v ^ 2 * e1
  have hs := sumz hW hX1 hX2 hX3 h1 h2 h3 e1 e3 hN
  have hng := negz hW h3 hX3
  obtain ⟨-, ht1, ht1', -⟩ := zfacts hW h1 hX1
  obtain ⟨-, ht2, ht2', -⟩ := zfacts hW h2 hX2
  set S := max ‖x1 / y1‖ ‖x2 / y2‖
  have hS0 : 0 < S := lt_max_of_lt_left ht1
  have hS1 : S < 1 := max_lt ht1' ht2'
  have ht3S : ‖x3 / y3‖ ≤ S := by
    have : x3 / y3 = (x1 / y1 + x2 / y2 + x3 / y3) - x1 / y1 - x2 / y2 := by ring
    rw [this]; exact sub_le (sub_le hs.le (le_max_left _ _)) (le_max_right _ _)
  have hsq : ‖x3 / y3‖ ^ 2 < S := by
    have := pow_le_pow_left₀ (norm_nonneg _) ht3S 2
    nlinarith
  have : x3 / W.toAffine.negY x3 y3 - x1 / y1 - x2 / y2 =
      (x3 / W.toAffine.negY x3 y3 + x3 / y3) - (x1 / y1 + x2 / y2 + x3 / y3) := by ring
  rw [this]
  exact sub_lt (hng.trans_lt hsq) hs

def zf : W.toAffine.Point → K
  | .zero => 0
  | .some x y _ => x / y

lemma key [DecidableEq K] (hW : IntegralModel W) (P Q : W.toAffine.Point) (hP : InFormalGroupPoints P)
    (hQ : InFormalGroupPoints Q) (hne : P ≠ 0 ∨ Q ≠ 0) :
    InFormalGroupPoints (P + Q) ∧ ‖zf (P + Q) - zf P - zf Q‖ < max ‖zf P‖ ‖zf Q‖ := by
  rcases P with _ | ⟨x1, y1, h1⟩ <;> rcases Q with _ | ⟨x2, y2, h2⟩
  · rw [← Affine.Point.zero_def] at hne; simp at hne
  · have hz : (Affine.Point.zero : W.toAffine.Point) + .some x2 y2 h2 = .some x2 y2 h2 := by
      rw [← Affine.Point.zero_def, zero_add]
    rw [hz]
    refine ⟨hQ, ?_⟩
    obtain ⟨-, ht, -, -⟩ := zfacts hW h2.1 hQ
    simp only [zf, sub_zero, sub_self, norm_zero]
    exact lt_max_of_lt_right ht
  · have hz : .some x1 y1 h1 + (Affine.Point.zero : W.toAffine.Point) = .some x1 y1 h1 := by
      rw [← Affine.Point.zero_def, add_zero]
    rw [hz]
    refine ⟨hP, ?_⟩
    obtain ⟨-, ht, -, -⟩ := zfacts hW h1.1 hP
    simp only [zf, sub_zero, sub_self, norm_zero]
    exact lt_max_of_lt_left ht
  · by_cases hxy : x1 = x2 ∧ y1 = W.toAffine.negY x2 y2
    · rw [Affine.Point.add_of_Y_eq hxy.1 hxy.2, Affine.Point.zero_def]
      refine ⟨trivial, ?_⟩
      simp only [zf, zero_sub]
      rw [hxy.1, hxy.2]
      have : -(x2 / W.toAffine.negY x2 y2) - x2 / y2 = -(x2 / W.toAffine.negY x2 y2 + x2 / y2) := by
        ring
      rw [this, norm_neg]
      have hng := negz hW h2.1 hQ
      obtain ⟨-, ht, ht', -⟩ := zfacts hW h2.1 hQ
      have : ‖x2 / y2‖ ^ 2 < ‖x2 / y2‖ := by nlinarith
      exact (hng.trans_lt this).trans_le (le_max_right _ _)
    · rw [Affine.Point.add_some hxy]
      exact chord hW h1.1 h2.1 hP hQ hxy

lemma mulz [DecidableEq K] (hW : IntegralModel W) (P : W.toAffine.Point) (hP : InFormalGroupPoints P)
    (hP0 : P ≠ 0) (k : ℕ) :
    InFormalGroupPoints ((k + 1) • P) ∧ ‖zf ((k + 1) • P) - ((k + 1 : ℕ) : K) * zf P‖ < ‖zf P‖ := by
  have ht : 0 < ‖zf P‖ := by
    rcases P with _ | ⟨x, y, h⟩
    · exact absurd Affine.Point.zero_def.symm hP0
    · exact (zfacts hW h.1 hP).2.1
  induction k with
  | zero =>
    rw [zero_add, one_nsmul]
    refine ⟨hP, ?_⟩
    simpa using ht
  | succ k ih =>
    obtain ⟨hQ, hQz⟩ := ih
    rw [succ_nsmul]
    obtain ⟨hR, hRz⟩ := key hW _ P hQ hP (Or.inr hP0)
    refine ⟨hR, ?_⟩
    have hQn : ‖zf ((k + 1) • P)‖ ≤ ‖zf P‖ := by
      have : zf ((k + 1) • P) =
          (zf ((k + 1) • P) - ((k + 1 : ℕ) : K) * zf P) + ((k + 1 : ℕ) : K) * zf P := by ring
      rw [this]
      refine add_le hQz.le ?_
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one K _)
    rw [max_eq_right hQn] at hRz
    have : zf ((k + 1) • P + P) - ((k + 1 + 1 : ℕ) : K) * zf P =
        (zf ((k + 1) • P + P) - zf ((k + 1) • P) - zf P) +
          (zf ((k + 1) • P) - ((k + 1 : ℕ) : K) * zf P) := by
      push_cast; ring
    rw [this]
    exact add_lt hRz hQz

end Formalism.ELL.FormalGroupPointsTorsion

namespace Formalism.ELL

open WeierstrassCurve

open Classical in

theorem formal_group_points_no_prime_to_p_torsion : FormalGroupPointsTorsionFree.{u} := by
  intro K _ _ W hW _ n hn P hP hnP
  by_contra hP0
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 :=
    Nat.exists_eq_succ_of_ne_zero (by rintro rfl; simp at hn)
  have h := (FormalGroupPointsTorsion.mulz hW P hP hP0 m).2
  rw [hnP, Affine.Point.zero_def] at h
  simp only [FormalGroupPointsTorsion.zf, zero_sub, norm_neg, norm_mul, hn, one_mul] at h
  exact lt_irrefl _ h

end Formalism.ELL
