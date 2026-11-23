import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementF

universe u

namespace Formalism.L2.Th1.A

variable {A : Type u} [CommRing A]

theorem IsDer.exists_derivation {D : A → A} (h : IsDer D) :
    ∃ d : Derivation ℤ A A, ∀ a, D a = d a := by
  refine ⟨Derivation.mk' (AddMonoidHom.mk' D h.1).toIntLinearMap (fun a b => ?_), fun a => rfl⟩
  simp only [AddMonoidHom.coe_toIntLinearMap, AddMonoidHom.mk'_apply, smul_eq_mul]
  exact h.2 a b

theorem der_mul (d : Derivation ℤ A A) (a b : A) : d (a * b) = a * d b + b * d a := by
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]

theorem der_sq (d : Derivation ℤ A A) (a : A) : d (a ^ 2) = 2 * a * d a := by
  rw [pow_two, der_mul]
  ring

theorem der_two_mul (d : Derivation ℤ A A) (a : A) : d (2 * a) = 2 * d a := by
  rw [two_mul, map_add, two_mul]

theorem der_three_mul (d : Derivation ℤ A A) (a : A) : d (3 * a) = 3 * d a := by
  rw [show (3 : A) * a = a + a + a by ring, map_add, map_add]
  ring

theorem der_inv (d : Derivation ℤ A A) {t s : A} (ht : t * s = 1) : d t = -t ^ 2 * d s := by
  have h0 : t * d s + s * d t = 0 := by rw [← der_mul, ht, Derivation.map_one_eq_zero]
  have h1 : d t = t * s * d t := by rw [ht, one_mul]
  rw [h1]
  linear_combination t * h0

theorem chord_rel {a₁ a₂ a₃ a₄ a₆ x y xP yP t L : A}
    (hE : y ^ 2 + a₁ * x * y + a₃ * y = x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆)
    (hEP : yP ^ 2 + a₁ * xP * yP + a₃ * yP = xP ^ 3 + a₂ * xP ^ 2 + a₄ * xP + a₆)
    (ht : t * (x - xP) = 1) (hL : L * (x - xP) = y - yP) :
    (a₄ - 2 * L * (y - L * x) - a₁ * (y - L * x) - a₃ * L)
        - (x * xP + (x + xP) * (L ^ 2 + a₁ * L - a₂ - x - xP)) = 0 ∧
      (a₆ - (y - L * x) ^ 2 - a₃ * (y - L * x))
        + x * xP * (L ^ 2 + a₁ * L - a₂ - x - xP) = 0 := by
  have hα : (a₄ - 2 * L * (y - L * x) - a₁ * (y - L * x) - a₃ * L)
      - (x * xP + (x + xP) * (L ^ 2 + a₁ * L - a₂ - x - xP)) = 0 := by
    linear_combination (-((a₄ - 2 * L * (y - L * x) - a₁ * (y - L * x) - a₃ * L)
      - (x * xP + (x + xP) * (L ^ 2 + a₁ * L - a₂ - x - xP)))) * ht - t * hE + t * hEP
      - t * (L * xP + (y - L * x) + yP + a₁ * xP + a₃) * hL
  refine ⟨hα, ?_⟩
  linear_combination (-1 : A) * hE - x * hα

theorem der_slope (W : WeierstrassCurve A) (d : Derivation ℤ A A) {x y xP yP t : A}
    (hE : W.toAffine.Equation x y) (hx : d x = 2 * y + W.a₁ * x + W.a₃)
    (hy : d y = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y)
    (hEP : W.toAffine.Equation xP yP) (hxP : d xP = 0) (hyP : d yP = 0)
    (ht : t * (x - xP) = 1) :
    d ((y - yP) * t) = x - W.toAffine.addX x xP ((y - yP) * t) := by
  have hE' := (WeierstrassCurve.Affine.equation_iff x y).1 hE
  have hEP' := (WeierstrassCurve.Affine.equation_iff xP yP).1 hEP
  have hL : ((y - yP) * t) * (x - xP) = y - yP := by linear_combination (y - yP) * ht
  obtain ⟨hα, -⟩ := chord_rel hE' hEP' ht hL
  have hdt : d t = -t ^ 2 * d (x - xP) := der_inv d ht
  have hdxs : d (x - xP) = d x := by rw [map_sub, hxP, sub_zero]
  rw [der_mul, map_sub, hyP, sub_zero, hdt, hdxs, hx, hy]
  simp only [WeierstrassCurve.Affine.addX]
  linear_combination (x - (((y - yP) * t) ^ 2 + W.a₁ * ((y - yP) * t) - W.a₂ - x - xP)) * ht + t * hα

theorem flowTranslation : FlowTranslate.{u} := by
  intro A _ W D x y xP yP t hD hC hF hEP hxP hyP ht
  obtain ⟨d, hd⟩ := hD.exists_derivation
  obtain ⟨hE, hx, hy⟩ := hF
  obtain ⟨c1, c2, c3, c4, c6⟩ := hC
  rw [hd] at hx hy hxP hyP c1 c2 c3 c4 c6
  have hDL := der_slope W d hE hx hy hEP hxP hyP ht
  have hE' := (WeierstrassCurve.Affine.equation_iff x y).1 hE
  have hEP' := (WeierstrassCurve.Affine.equation_iff xP yP).1 hEP
  have hL : ((y - yP) * t) * (x - xP) = y - yP := by linear_combination (y - yP) * ht
  obtain ⟨hα, hβ⟩ := chord_rel hE' hEP' ht hL
  set L := (y - yP) * t with hLdef
  have hDL' : d L = x - (L ^ 2 + W.a₁ * L - W.a₂ - x - xP) := hDL
  refine ⟨?_, ?_, ?_⟩
  · rw [WeierstrassCurve.Affine.equation_iff]
    simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.negAddY,
      WeierstrassCurve.Affine.addX]
    linear_combination (-1 : A) * hβ - (L ^ 2 + W.a₁ * L - W.a₂ - x - xP) * hα
  · rw [hd]
    simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.negAddY,
      WeierstrassCurve.Affine.addX, map_sub, map_add, der_sq, der_mul, c1, c2, hx, hxP, hDL']
    ring
  · rw [hd]
    simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.negAddY,
      WeierstrassCurve.Affine.addX, map_neg, map_sub, map_add, der_sq, der_mul, c1, c2, c3, hx, hy, hxP, hDL']
    linear_combination (-2 : A) * hα

theorem flowLogDerivative : FlowLogDeriv.{u} := by
  intro A _ W D x y xP yP t hD hC hF hEP hxP hyP ht
  obtain ⟨d, hd⟩ := hD.exists_derivation
  obtain ⟨hE, hx, hy⟩ := hF
  obtain ⟨c1, c2, c3, c4, c6⟩ := hC
  rw [hd] at hx hy hxP hyP c1 c2 c3 c4 c6
  have hEQ : W.toAffine.Equation xP (W.toAffine.negY xP yP) :=
    (WeierstrassCurve.Affine.equation_neg xP yP).2 hEP
  have hyQ : d (W.toAffine.negY xP yP) = 0 := by
    simp only [WeierstrassCurve.Affine.negY, map_sub, map_neg, der_mul, hyP, hxP, c1, c3]
    ring
  have hP := der_slope W d hE hx hy hEP hxP hyP ht
  have hQ := der_slope W d hE hx hy hEQ hxP hyQ ht

  have hsplit : t * (2 * y + W.a₁ * x + W.a₃) =
      (y - yP) * t + (y - W.toAffine.negY xP yP) * t + W.a₁ * (t * (x - xP)) := by
    simp only [WeierstrassCurve.Affine.negY]
    ring
  simp only [hd]
  rw [hx, hsplit, map_add, map_add, hP, hQ, ht, mul_one, c1]
  ring

end Formalism.L2.Th1.A
