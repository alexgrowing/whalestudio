import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementF

universe u

namespace Formalism.L2.Th1.A
namespace QuadraticFlow

variable {A : Type u} [CommRing A] {D : A → A}

lemma der_add (h : IsDer D) (a b : A) : D (a + b) = D a + D b := h.1 a b

lemma der_mul (h : IsDer D) (a b : A) : D (a * b) = a * D b + b * D a := h.2 a b

lemma der_zero (h : IsDer D) : D 0 = 0 := by
  have e := h.1 0 0
  rw [add_zero] at e
  linear_combination -e

lemma der_one (h : IsDer D) : D 1 = 0 := by
  have e := h.2 1 1
  simp only [mul_one, one_mul] at e
  linear_combination -e

lemma der_neg (h : IsDer D) (a : A) : D (-a) = -D a := by
  have e := h.1 a (-a)
  rw [add_neg_cancel, der_zero h] at e
  linear_combination -e

lemma der_sub (h : IsDer D) (a b : A) : D (a - b) = D a - D b := by
  rw [sub_eq_add_neg, der_add h, der_neg h, ← sub_eq_add_neg]

lemma der_natCast (h : IsDer D) (n : ℕ) : D (n : A) = 0 := by
  induction n with
  | zero => simpa using der_zero h
  | succ n ih => rw [Nat.cast_succ, der_add h, ih, der_one h, add_zero]

lemma der_ofNat (h : IsDer D) (n : ℕ) [n.AtLeastTwo] : D (OfNat.ofNat n : A) = 0 := by
  simpa using der_natCast h (OfNat.ofNat n)

lemma der_sq (h : IsDer D) (a : A) : D (a ^ 2) = 2 * a * D a := by
  rw [sq, der_mul h]
  ring

lemma der_inv (h : IsDer D) {t s : A} (hts : t * s = 1) : D t = -t ^ 2 * D s := by
  have e := h.2 t s
  rw [hts, der_one h] at e
  linear_combination (-t) * e + (-D t) * hts

lemma cancel_unit {k a b : A} (hk : IsUnit k) (e : k * a = k * b) : a = b := hk.mul_left_cancel e

lemma unit_four (h6 : IsUnit (6 : A)) : IsUnit (4 : A) := by
  have e6 : (6 : A) = 2 * 3 := by norm_num
  rw [e6] at h6
  have h2 : IsUnit (2 : A) := isUnit_of_mul_isUnit_left h6
  have e4 : (4 : A) = 2 * 2 := by norm_num
  rw [e4]
  exact h2.mul h2

lemma unit_twelve (h6 : IsUnit (6 : A)) : IsUnit (12 : A) := by
  have e6 : (6 : A) = 2 * 3 := by norm_num
  have h2 : IsUnit (2 : A) := isUnit_of_mul_isUnit_left (e6 ▸ h6)
  have e12 : (12 : A) = 6 * 2 := by norm_num
  rw [e12]
  exact h6.mul h2

lemma weierstrassSubstitution_unit_fact (h6 : IsUnit (6 : A)) : IsUnit (432 : A) := by
  have e : (432 : A) = 6 * 6 * 12 := by norm_num
  rw [e]
  exact (h6.mul h6).mul (unit_twelve h6)

end QuadraticFlow

open QuadraticFlow

theorem twoTorsionTranslation : FlowTwoTorsion.{u} := by
  intro A _ W D x y xT yT t hD hC hF hT hDxT hDyT h2 ht
  obtain ⟨hE, hDx, hDy⟩ := hF
  obtain ⟨ha1, ha2, ha3, ha4, ha6⟩ := hC
  rw [WeierstrassCurve.Affine.equation_iff] at hE hT
  have hDt : D t = -t ^ 2 * (2 * y + W.a₁ * x + W.a₃) := by
    rw [der_inv hD ht, der_sub hD, hDxT, sub_zero, hDx]
  refine ⟨?_, ?_, ?_⟩
  · simp only [WeierstrassCurve.Affine.addX]
    linear_combination t ^ 2 * hE - t ^ 2 * hT - t ^ 2 * (y - yT) * h2 +
      ((3 * xT + (x - xT) + W.a₂) + t * ((x ^ 2 + x * xT + xT ^ 2 + W.a₂ * (x + xT) + W.a₄) - W.a₁ * yT) - W.a₁ * (y - yT) * t) * ht
  · rw [hDt]
    simp only [WeierstrassCurve.b₂]
    linear_combination 4 * t ^ 4 * hE - 4 * t ^ 4 * hT + t ^ 4 * ((2 * yT + W.a₁ * xT + W.a₃) + 2 * W.a₁ * (x - xT)) * h2 +
      (4 * (3 * xT ^ 2 + 2 * W.a₂ * xT + W.a₄ - W.a₁ * yT) * t ^ 3 + (12 * xT + (W.a₁ ^ 2 + 4 * W.a₂)) * t ^ 2 * (2 + (t * (x - xT) - 1)) + 4 * t * (3 + 3 * (t * (x - xT) - 1) + (t * (x - xT) - 1) ^ 2)) * ht
  · rw [hDt]
    simp only [der_neg hD, der_mul hD, der_add hD, der_sq hD, der_ofNat hD, hDx, hDy, hDt, ha1, ha3,
      WeierstrassCurve.b₂]
    linear_combination 8 * t ^ 3 * hE - 8 * t ^ 3 * hT +
      (2 * t ^ 3 * ((2 * yT + W.a₁ * xT + W.a₃) + 2 * W.a₁ * (x - xT)) - W.a₁ * t ^ 2) * h2 +
      (8 * (3 * xT ^ 2 + 2 * W.a₂ * xT + W.a₄ - W.a₁ * yT) * t ^ 2 + (12 * xT + (W.a₁ ^ 2 + 4 * W.a₂)) * t * (3 + 2 * (t * (x - xT) - 1)) + 12 + 18 * (t * (x - xT) - 1) + 8 * (t * (x - xT) - 1) ^ 2) * ht

theorem twoTorsionTranslationWeierstrassForm : FlowTwoTorsionWp.{u} := by
  intro A _ W D x y xT yT t c g2 g3 kap hD hC hF hT hDxT hDyT h2 ht h6 hc hg2 hg3 hk
  have H1 := twoTorsionTranslation A W D x y xT yT t hD hC hF hT hDxT hDyT h2 ht
  rw [WeierstrassCurve.Affine.equation_iff] at hT
  have hkap : kap = (3 * xT ^ 2 + 2 * W.a₂ * xT + W.a₄ - W.a₁ * yT) := by
    apply cancel_unit ((unit_four h6).mul (unit_twelve h6))
    simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.c₄] at hc hg2
    linear_combination 12 * hk + (24 * xT + 12 * c + (W.a₁ ^ 2 + 4 * W.a₂)) * hc - hg2 + 24 * W.a₁ * h2
  have ha : 4 * (xT + c) ^ 3 - g2 * (xT + c) - g3 = 0 := by
    apply cancel_unit (weierstrassSubstitution_unit_fact h6)
    simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.c₄,
      WeierstrassCurve.c₆] at hc hg2 hg3
    linear_combination ((12 * xT + 12 * c) ^ 2 + (12 * xT + 12 * c) * (12 * xT + (W.a₁ ^ 2 + 4 * W.a₂)) + (12 * xT + (W.a₁ ^ 2 + 4 * W.a₂)) ^ 2 - 3 * ((W.a₁ ^ 2 + 4 * W.a₂) ^ 2 - 24 * (2 * W.a₄ + W.a₁ * W.a₃))) * hc - 36 * (xT + c) * hg2 -
      2 * hg3 + 432 * (2 * yT + W.a₁ * xT + W.a₃) * h2 - 1728 * hT
  have hd : D t ^ 2 = 4 * t * (1 + 3 * (xT + c) * t + kap * t ^ 2) := by
    linear_combination H1.2.1 - t ^ 2 * hc - 4 * t ^ 3 * hkap
  refine ⟨ha, hkap, ?_, hd, ?_⟩
  · rw [H1.1, hkap]
    ring
  · intro e2 e3 hs he
    linear_combination hd + (4 * t ^ 2 + 8 * (xT + c) * t ^ 3) * hs + t ^ 3 * hk - t ^ 3 * he

end Formalism.L2.Th1.A
