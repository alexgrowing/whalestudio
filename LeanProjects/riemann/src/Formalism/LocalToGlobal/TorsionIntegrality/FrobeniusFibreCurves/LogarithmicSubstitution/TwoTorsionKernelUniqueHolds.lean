import Mathlib
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementK

noncomputable section

namespace Formalism.L2.Th1.B.KNorm

open Formalism.ELL (InFormalGroupPoints)
open Formalism.L2.Th1.E (px py IntCurve)
open WeierstrassCurve.Affine (Point)

section Norm

variable {K : Type} [NormedField K] [IsUltrametricDist K]

lemma nadd_le {a b : K} {r : ℝ} (ha : ‖a‖ ≤ r) (hb : ‖b‖ ≤ r) : ‖a + b‖ ≤ r :=
  (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)

lemma nadd_lt {a b : K} {r : ℝ} (ha : ‖a‖ < r) (hb : ‖b‖ < r) : ‖a + b‖ < r :=
  lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max a b) (max_lt ha hb)

lemma nsub_le {a b : K} {r : ℝ} (ha : ‖a‖ ≤ r) (hb : ‖b‖ ≤ r) : ‖a - b‖ ≤ r := by
  rw [sub_eq_add_neg]
  exact nadd_le ha (by rwa [norm_neg])

lemma ndom {a b : K} (h : ‖b‖ < ‖a‖) : ‖a + b‖ = ‖a‖ := by
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h.ne', max_eq_left h.le]

lemma nmul1 {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a * b‖ ≤ 1 := by
  rw [norm_mul]
  exact mul_le_one₀ ha (norm_nonneg _) hb

lemma npow1 {a : K} (ha : ‖a‖ ≤ 1) (n : ℕ) : ‖a ^ n‖ ≤ 1 := by
  rw [norm_pow]
  exact pow_le_one₀ (norm_nonneg _) ha

lemma n2le : ‖(2 : K)‖ ≤ 1 := by
  rw [show (2 : K) = 1 + 1 by norm_num]
  exact nadd_le norm_one.le norm_one.le

lemma n4le : ‖(4 : K)‖ ≤ 1 := by
  rw [show (4 : K) = 2 * 2 by norm_num]
  exact nmul1 n2le n2le

lemma n4 (h2 : ‖(2 : K)‖ = 2⁻¹) : ‖(4 : K)‖ = 4⁻¹ := by
  rw [show (4 : K) = 2 * 2 by norm_num, norm_mul, h2]
  norm_num

lemma n3 (h2 : ‖(2 : K)‖ = 2⁻¹) : ‖(3 : K)‖ = 1 := by
  rw [show (3 : K) = 1 + 2 by norm_num, ndom (by rw [h2, norm_one]; norm_num), norm_one]

lemma two_ne (h2 : ‖(2 : K)‖ = 2⁻¹) : (2 : K) ≠ 0 := by
  intro h
  rw [h, norm_zero] at h2
  norm_num at h2

lemma b_int (W : WeierstrassCurve K) (h1 : ‖W.a₁‖ ≤ 1) (h2 : ‖W.a₂‖ ≤ 1) (h3 : ‖W.a₃‖ ≤ 1)
    (h4 : ‖W.a₄‖ ≤ 1) (h6 : ‖W.a₆‖ ≤ 1) :
    ‖W.b₂‖ ≤ 1 ∧ ‖W.b₄‖ ≤ 1 ∧ ‖W.b₆‖ ≤ 1 ∧ ‖W.b₈‖ ≤ 1 := by
  simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  refine ⟨nadd_le (npow1 h1 2) (nmul1 n4le h2), nadd_le (nmul1 n2le h4) (nmul1 h1 h3),
    nadd_le (npow1 h3 2) (nmul1 n4le h6), ?_⟩
  exact nsub_le (nadd_le (nsub_le (nadd_le (nmul1 (npow1 h1 2) h6) (nmul1 (nmul1 n4le h2) h6))
    (nmul1 (nmul1 h1 h3) h4)) (nmul1 h2 (npow1 h3 2))) (npow1 h4 2)

lemma t4 (h2 : ‖(2 : K)‖ = 2⁻¹) (x : K) : ‖4 * x ^ 3‖ = ‖x‖ ^ 3 / 4 := by
  rw [norm_mul, norm_pow, n4 h2]
  ring

lemma tb2 {b : K} (hb : ‖b‖ ≤ 1) (x : K) : ‖b * x ^ 2‖ ≤ ‖x‖ ^ 2 := by
  rw [norm_mul, norm_pow]
  exact mul_le_of_le_one_left (by positivity) hb

lemma tb4 (h2 : ‖(2 : K)‖ = 2⁻¹) {b : K} (hb : ‖b‖ ≤ 1) (x : K) : ‖2 * b * x‖ ≤ ‖x‖ / 2 := by
  rw [norm_mul, norm_mul, h2]
  nlinarith [mul_le_mul_of_nonneg_right hb (norm_nonneg x)]

variable {b2 b4 b6 b8 x : K}

lemma psi_le (h2 : ‖(2 : K)‖ = 2⁻¹) (hb2 : ‖b2‖ ≤ 1) (hb4 : ‖b4‖ ≤ 1) (hb6 : ‖b6‖ ≤ 1)
    (hx : 4 ≤ ‖x‖) : ‖4 * x ^ 3 + b2 * x ^ 2 + 2 * b4 * x + b6‖ ≤ ‖x‖ ^ 3 / 4 := by
  have r0 : 0 ≤ ‖x‖ := norm_nonneg _
  have e1 : ‖x‖ ^ 2 ≤ ‖x‖ ^ 3 / 4 := by nlinarith [mul_nonneg (sq_nonneg ‖x‖) (sub_nonneg.2 hx)]
  have e2 : ‖x‖ / 2 ≤ ‖x‖ ^ 3 / 4 := by nlinarith [mul_nonneg r0 (sub_nonneg.2 hx)]
  have e3 : 1 ≤ ‖x‖ ^ 3 / 4 := by nlinarith [pow_le_pow_left₀ (by norm_num) hx 3]
  exact nadd_le (nadd_le (nadd_le (t4 h2 x).le ((tb2 hb2 x).trans e1)) ((tb4 h2 hb4 x).trans e2))
    (hb6.trans e3)

lemma psi_zero_le (h2 : ‖(2 : K)‖ = 2⁻¹) (hb2 : ‖b2‖ ≤ 1) (hb4 : ‖b4‖ ≤ 1) (hb6 : ‖b6‖ ≤ 1)
    (h0 : 4 * x ^ 3 + b2 * x ^ 2 + 2 * b4 * x + b6 = 0) : ‖x‖ ≤ 4 := by
  by_contra hlt
  push_neg at hlt
  have r0 : 0 ≤ ‖x‖ := norm_nonneg _
  have e1 : ‖x‖ ^ 2 < ‖x‖ ^ 3 / 4 := by nlinarith [mul_pos (pow_pos (by linarith : (0:ℝ) < ‖x‖) 2) (sub_pos.2 hlt)]
  have e2 : ‖x‖ / 2 < ‖x‖ ^ 3 / 4 := by nlinarith [mul_pos (by linarith : (0:ℝ) < ‖x‖) (sub_pos.2 hlt)]
  have e3 : 1 < ‖x‖ ^ 3 / 4 := by nlinarith [pow_le_pow_left₀ (by norm_num) hlt.le 3]
  have hr : ‖b2 * x ^ 2 + 2 * b4 * x + b6‖ < ‖4 * x ^ 3‖ := by
    rw [t4 h2]
    exact nadd_lt (nadd_lt ((tb2 hb2 x).trans_lt e1) ((tb4 h2 hb4 x).trans_lt e2)) (hb6.trans_lt e3)
  have key := ndom hr
  rw [show 4 * x ^ 3 + (b2 * x ^ 2 + 2 * b4 * x + b6) = 4 * x ^ 3 + b2 * x ^ 2 + 2 * b4 * x + b6 by ring,
    h0, norm_zero, t4 h2] at key
  nlinarith [pow_pos (by linarith : (0:ℝ) < ‖x‖) 3]

lemma num_norm (h2 : ‖(2 : K)‖ = 2⁻¹) (hb4 : ‖b4‖ ≤ 1) (hb6 : ‖b6‖ ≤ 1) (hb8 : ‖b8‖ ≤ 1)
    (hx : 4 ≤ ‖x‖) : ‖x ^ 4 - b4 * x ^ 2 - 2 * b6 * x - b8‖ = ‖x‖ ^ 4 := by
  have r0 : 0 ≤ ‖x‖ := norm_nonneg _
  have r2 : 16 ≤ ‖x‖ ^ 2 := by nlinarith
  have r4 : ‖x‖ ^ 4 = (‖x‖ ^ 2) ^ 2 := by ring
  have e1 : ‖x‖ ^ 2 < ‖x‖ ^ 4 := by rw [r4]; nlinarith
  have e2 : ‖x‖ / 2 < ‖x‖ ^ 4 := by rw [r4]; nlinarith
  have e3 : 1 < ‖x‖ ^ 4 := by rw [r4]; nlinarith
  rw [show x ^ 4 - b4 * x ^ 2 - 2 * b6 * x - b8 = x ^ 4 + -(b4 * x ^ 2 + 2 * b6 * x + b8) by ring]
  rw [ndom, norm_pow]
  rw [norm_neg, norm_pow]
  exact nadd_lt (nadd_lt ((tb2 hb4 x).trans_lt e1) ((tb4 h2 hb6 x).trans_lt e2)) (hb8.trans_lt e3)

lemma dup_core (h2 : ‖(2 : K)‖ = 2⁻¹) (hb2 : ‖b2‖ ≤ 1) (hb4 : ‖b4‖ ≤ 1) (hb6 : ‖b6‖ ≤ 1)
    (hb8 : ‖b8‖ ≤ 1) (hx : 4 ≤ ‖x‖) {X : K}
    (hX : X * (4 * x ^ 3 + b2 * x ^ 2 + 2 * b4 * x + b6)
      = x ^ 4 - b4 * x ^ 2 - 2 * b6 * x - b8) : 4 < ‖X‖ := by
  have hn := num_norm h2 hb4 hb6 hb8 hx
  have hp := psi_le h2 hb2 hb4 hb6 hx
  have hm := congrArg norm hX
  rw [norm_mul, hn] at hm
  by_contra hle
  push_neg at hle
  have hb : ‖X‖ * ‖4 * x ^ 3 + b2 * x ^ 2 + 2 * b4 * x + b6‖ ≤ 4 * (‖x‖ ^ 3 / 4) :=
    mul_le_mul hle hp (norm_nonneg _) (by norm_num)
  have r3 : 0 < ‖x‖ ^ 3 := pow_pos (by linarith) 3
  nlinarith

lemma psi_zero_eq (h2 : ‖(2 : K)‖ = 2⁻¹) (hb2 : ‖b2‖ = 1) (hb4 : ‖b4‖ ≤ 1) (hb6 : ‖b6‖ ≤ 1)
    (hx : 1 < ‖x‖) (h0 : 4 * x ^ 3 + b2 * x ^ 2 + 2 * b4 * x + b6 = 0) : ‖x‖ = 4 := by
  refine le_antisymm (psi_zero_le h2 hb2.le hb4 hb6 h0) ?_
  by_contra hlt
  push_neg at hlt
  have e1 : ‖x‖ ^ 3 / 4 < ‖x‖ ^ 2 := by nlinarith [mul_pos (pow_pos (by linarith : (0:ℝ) < ‖x‖) 2) (sub_pos.2 hlt)]
  have e2 : ‖x‖ / 2 < ‖x‖ ^ 2 := by nlinarith
  have e3 : 1 < ‖x‖ ^ 2 := by nlinarith
  have hd : ‖b2 * x ^ 2‖ = ‖x‖ ^ 2 := by rw [norm_mul, hb2, one_mul, norm_pow]
  have hr : ‖4 * x ^ 3 + 2 * b4 * x + b6‖ < ‖b2 * x ^ 2‖ := by
    rw [hd]
    exact nadd_lt (nadd_lt ((t4 h2 x).trans_lt e1) ((tb4 h2 hb4 x).trans_lt e2)) (hb6.trans_lt e3)
  have key := ndom hr
  rw [show b2 * x ^ 2 + (4 * x ^ 3 + 2 * b4 * x + b6) = 4 * x ^ 3 + b2 * x ^ 2 + 2 * b4 * x + b6 by ring,
    h0, norm_zero, hd] at key
  nlinarith

lemma four_add_le (h2 : ‖(2 : K)‖ = 2⁻¹) (hb4 : ‖b4‖ ≤ 1) (hb6 : ‖b6‖ ≤ 1)
    (hx : ‖x‖ = 4) (h0 : 4 * x ^ 3 + b2 * x ^ 2 + 2 * b4 * x + b6 = 0) :
    ‖4 * x + b2‖ ≤ 1 / 8 := by
  have e : x ^ 2 * (4 * x + b2) = -(2 * b4 * x + b6) := by linear_combination h0
  have hr : ‖2 * b4 * x + b6‖ ≤ 2 :=
    nadd_le ((tb4 h2 hb4 x).trans (by rw [hx]; norm_num)) (hb6.trans (by norm_num))
  have hm := congrArg norm e
  rw [norm_mul, norm_pow, hx, norm_neg] at hm
  nlinarith [norm_nonneg (4 * x + b2)]

lemma psi_zero_unique (h2 : ‖(2 : K)‖ = 2⁻¹) (hb2 : ‖b2‖ ≤ 1) (hb4 : ‖b4‖ ≤ 1) (hb6 : ‖b6‖ ≤ 1)
    {x' : K} (hx : ‖x‖ = 4) (hx' : ‖x'‖ = 4)
    (h0 : 4 * x ^ 3 + b2 * x ^ 2 + 2 * b4 * x + b6 = 0)
    (h0' : 4 * x' ^ 3 + b2 * x' ^ 2 + 2 * b4 * x' + b6 = 0) : x = x' := by
  have f := four_add_le h2 hb4 hb6 hx h0
  have f' := four_add_le h2 hb4 hb6 hx' h0'
  have hfac : (x - x') * (4 * x * x' + (x * (4 * x + b2) + x' * (4 * x' + b2) + 2 * b4)) = 0 := by
    linear_combination h0 - h0'
  rcases mul_eq_zero.1 hfac with h | h
  · exact sub_eq_zero.1 h
  exfalso
  have hdom : ‖4 * x * x'‖ = 4 := by
    rw [norm_mul, norm_mul, n4 h2, hx, hx']
    norm_num
  have a1 : ‖x * (4 * x + b2)‖ < 4 := by
    rw [norm_mul, hx]
    linarith
  have a2 : ‖x' * (4 * x' + b2)‖ < 4 := by
    rw [norm_mul, hx']
    linarith
  have a3 : ‖2 * b4‖ < 4 := by
    rw [norm_mul, h2]
    nlinarith [norm_nonneg b4]
  have hr : ‖x * (4 * x + b2) + x' * (4 * x' + b2) + 2 * b4‖ < ‖4 * x * x'‖ := by
    rw [hdom]
    exact nadd_lt (nadd_lt a1 a2) a3
  have key := ndom hr
  rw [h, norm_zero, hdom] at key
  norm_num at key

end Norm

section Curve

variable {K : Type} [Field K] {W : WeierstrassCurve K} {x y : K}

lemma psi_eq (h : W.toAffine.Equation x y) :
    (2 * y + W.a₁ * x + W.a₃) ^ 2 = 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ := by
  rw [WeierstrassCurve.Affine.equation_iff] at h
  simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
  linear_combination 4 * h

lemma negY_iff : y = W.toAffine.negY x y ↔ 2 * y + W.a₁ * x + W.a₃ = 0 := by
  rw [WeierstrassCurve.Affine.negY]
  constructor <;> intro h <;> linear_combination h

variable [DecidableEq K]

lemma dup (h : W.toAffine.Equation x y) (hy : y ≠ W.toAffine.negY x y) :
    W.toAffine.addX x x (W.toAffine.slope x x y y)
        * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆)
      = x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈ := by
  have hden : y - W.toAffine.negY x y ≠ 0 := sub_ne_zero.2 hy
  have hdd : y - W.toAffine.negY x y = 2 * y + W.a₁ * x + W.a₃ := by
    rw [WeierstrassCurve.Affine.negY]
    ring
  have hl : W.toAffine.slope x x y y * (2 * y + W.a₁ * x + W.a₃)
      = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y := by
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy, ← hdd, div_mul_cancel₀ _ hden]
  rw [← psi_eq h, WeierstrassCurve.Affine.addX]
  rw [WeierstrassCurve.Affine.equation_iff] at h
  simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  linear_combination (W.toAffine.slope x x y y * (2 * y + W.a₁ * x + W.a₃)
      + (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) + W.a₁ * (2 * y + W.a₁ * x + W.a₃)) * hl
    + (-(W.a₁ ^ 2 + 4 * W.a₂ + 8 * x)) * h

lemma add_self_iff (h : W.toAffine.Nonsingular x y) :
    (Point.some x y h + Point.some x y h = 0) ↔ 2 * y + W.a₁ * x + W.a₃ = 0 := by
  rw [add_eq_zero_iff_eq_neg, WeierstrassCurve.Affine.Point.neg_some, WeierstrassCurve.Affine.Point.some.injEq]
  simp only [true_and]
  exact negY_iff

lemma px_add_self (h : W.toAffine.Nonsingular x y) (hy : y ≠ W.toAffine.negY x y) :
    px W (Point.some x y h + Point.some x y h)
      = W.toAffine.addX x x (W.toAffine.slope x x y y) := by
  rw [WeierstrassCurve.Affine.Point.add_some (fun hxy => hy hxy.2)]
  rfl

end Curve

section Main

variable {K : Type} [NormedField K] [IsUltrametricDist K] [DecidableEq K]
  {W : WeierstrassCurve K}

lemma two_tors_le (hW : IntCurve W) (h2 : ‖(2 : K)‖ = 2⁻¹) (P : W.toAffine.Point)
    (hP : P + P = 0) : ‖px W P‖ ≤ 4 := by
  obtain ⟨h1, h2a, h3, h4, h6, -⟩ := hW
  obtain ⟨hb2, hb4, hb6, -⟩ := b_int W h1 h2a h3 h4 h6
  cases P with
  | zero =>
    change ‖(0 : K)‖ ≤ 4
    rw [norm_zero]
    norm_num
  | some x y h =>
    have hd := (add_self_iff h).1 hP
    have h0 := psi_eq h.1
    rw [hd] at h0
    exact psi_zero_le (x := x) h2 hb2 hb4 hb6 (by rw [← h0]; ring)

lemma dup_big (hW : IntCurve W) (h2 : ‖(2 : K)‖ = 2⁻¹) (P : W.toAffine.Point)
    (hx : 4 ≤ ‖px W P‖) (hP : P + P ≠ 0) : 4 < ‖px W (P + P)‖ := by
  obtain ⟨h1, h2a, h3, h4, h6, -⟩ := hW
  obtain ⟨hb2, hb4, hb6, hb8⟩ := b_int W h1 h2a h3 h4 h6
  cases P with
  | zero =>
    change 4 ≤ ‖(0 : K)‖ at hx
    rw [norm_zero] at hx
    norm_num at hx
  | some x y h =>
    have hy : y ≠ W.toAffine.negY x y := fun e => hP ((add_self_iff h).2 (negY_iff.1 e))
    rw [px_add_self h hy]
    exact dup_core h2 hb2 hb4 hb6 hb8 hx (dup h.1 hy)

lemma tors_bound (hW : IntCurve W) (h2 : ‖(2 : K)‖ = 2⁻¹) (P : W.toAffine.Point) (k : ℕ)
    (hk : (2 ^ k) • P = 0) (hP : P + P ≠ 0) : ‖px W P‖ < 4 := by
  by_contra hge
  push_neg at hge
  have claim : ∀ j : ℕ, 4 < ‖px W ((2 ^ (j + 1)) • P)‖ := by
    intro j
    induction j with
    | zero =>
      rw [zero_add, pow_one, two_nsmul]
      exact dup_big hW h2 P hge hP
    | succ j ih =>
      have hQ : (2 ^ (j + 1)) • P + (2 ^ (j + 1)) • P ≠ 0 := by
        intro e
        have := two_tors_le hW h2 _ e
        linarith
      have e : (2 ^ (j + 1 + 1)) • P = (2 ^ (j + 1)) • P + (2 ^ (j + 1)) • P := by
        rw [← add_nsmul]
        congr 1
        ring
      rw [e]
      exact dup_big hW h2 _ ih.le hQ
  cases k with
  | zero =>
    rw [pow_zero, one_nsmul] at hk
    rw [hk, add_zero] at hP
    exact hP rfl
  | succ k =>
    have hc := claim k
    rw [hk] at hc
    change 4 < ‖(0 : K)‖ at hc
    rw [norm_zero] at hc
    norm_num at hc

lemma two_torsion_kernel_norm_unique (hW : IntCurve W) (h2 : ‖(2 : K)‖ = 2⁻¹) (ha : ‖W.a₁‖ = 1)
    (P Q : W.toAffine.Point) (hP0 : P ≠ 0) (hP : P + P = 0) (hPE : InFormalGroupPoints P) :
    ‖px W P‖ = 4 ∧ (Q ≠ 0 → Q + Q = 0 → InFormalGroupPoints Q → P = Q) := by
  obtain ⟨h1, h2a, h3, h4, h6, -⟩ := hW
  obtain ⟨-, hb4, hb6, -⟩ := b_int W h1 h2a h3 h4 h6
  have hb2 : ‖W.b₂‖ = 1 := by
    simp only [WeierstrassCurve.b₂]
    rw [ndom (by rw [norm_pow, ha, one_pow, norm_mul, n4 h2]; nlinarith [norm_nonneg W.a₂]),
      norm_pow, ha, one_pow]
  cases P with
  | zero => exact (hP0 rfl).elim
  | some x y h =>
    have hd := (add_self_iff h).1 hP
    have h0 : 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ = 0 := by
      have e := psi_eq h.1
      rw [hd] at e
      rw [← e]
      ring
    have hx4 : ‖x‖ = 4 := psi_zero_eq (x := x) h2 hb2 hb4 hb6 hPE h0
    refine ⟨hx4, fun hQ0 hQ hQE => ?_⟩
    cases Q with
    | zero => exact (hQ0 rfl).elim
    | some x' y' h' =>
      have hd' := (add_self_iff h').1 hQ
      have h0' : 4 * x' ^ 3 + W.b₂ * x' ^ 2 + 2 * W.b₄ * x' + W.b₆ = 0 := by
        have e := psi_eq h'.1
        rw [hd'] at e
        rw [← e]
        ring
      have hx4' : ‖x'‖ = 4 := psi_zero_eq (x := x') h2 hb2 hb4 hb6 hQE h0'
      have hxx := psi_zero_unique h2 hb2.le hb4 hb6 hx4 hx4' h0 h0'
      subst hxx
      have hyy : y = y' := by
        have e2 : (2 : K) * y = 2 * y' := by linear_combination hd - hd'
        exact mul_left_cancel₀ (two_ne h2) e2
      subst hyy
      rfl

end Main

open Classical in
theorem two_torsion_kernel_unique_holds : TwoTorsionKernelUnique := by
  intro K _ _ W hW h2 ha P Q hP0 hP hPE
  exact two_torsion_kernel_norm_unique hW h2 ha P Q hP0 hP hPE

open Classical in
theorem torsion_norm_bound_holds : TorsBound := by
  intro K _ _ W hW h2 P k hk hP
  exact tors_bound hW h2 P k hk hP

theorem kappa_norm_holds : KapNorm := by
  intro K _ _ _ W hM h2 x
  obtain ⟨h1, h2a, h3, h4, h6⟩ := hM
  obtain ⟨hb2, hb4, -, -⟩ := b_int W h1 h2a h3 h4 h6
  have e : 3 * (x + W.b₂ / 12) ^ 2 - Formalism.L2.Th1.A.g₂ W / 4
      = 3 * x ^ 2 + 2⁻¹ * W.b₂ * x + 2⁻¹ * W.b₄ := by
    simp only [Formalism.L2.Th1.A.g₂, WeierstrassCurve.c₄]
    ring
  have ni : ‖(2 : K)⁻¹‖ = 2 := by rw [norm_inv, h2, inv_inv]
  have t1 : ‖3 * x ^ 2‖ = ‖x‖ ^ 2 := by rw [norm_mul, n3 h2, one_mul, norm_pow]
  have t2 : ‖2⁻¹ * W.b₂ * x‖ ≤ 2 * ‖x‖ := by
    rw [norm_mul, norm_mul, ni]
    nlinarith [mul_le_mul_of_nonneg_right hb2 (norm_nonneg x), norm_nonneg W.b₂]
  have t3 : ‖2⁻¹ * W.b₄‖ ≤ 2 := by
    rw [norm_mul, ni]
    linarith
  rw [e]
  constructor
  · intro hx
    have hr : ‖2⁻¹ * W.b₂ * x + 2⁻¹ * W.b₄‖ < ‖3 * x ^ 2‖ := by
      rw [t1, hx]
      exact nadd_lt (t2.trans_lt (by rw [hx]; norm_num)) (t3.trans_lt (by norm_num))
    rw [add_assoc, ndom hr, t1, hx]
    norm_num
  · intro hx
    have r0 := norm_nonneg x
    exact nadd_lt (nadd_lt (by rw [t1]; nlinarith) (t2.trans_lt (by linarith))) (t3.trans_lt (by norm_num))

end Formalism.L2.Th1.B.KNorm
