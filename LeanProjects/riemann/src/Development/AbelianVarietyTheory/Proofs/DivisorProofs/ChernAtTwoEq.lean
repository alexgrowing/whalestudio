import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPosFrameQuotIn

set_option autoImplicit false

noncomputable section

open Set Matrix Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.HermFrame GlobalTheory.CxForm GlobalTheory.SecForm
open GlobalTheory.GoodMetric (coordVec)
open scoped ContDiff ComplexOrder

namespace GlobalTheory.SecForm.ChernTwo

variable {n : ℕ}

theorem sym_mul_swap (a b c d : Fin n) : sym (a, b) * sym (c, d) = -(sym (a, d) * sym (c, b)) := by
  apply Subtype.ext
  have h (u w : Fin n ⊕ Fin n → ℂ) : ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ w =
      -(ExteriorAlgebra.ι ℂ w * ExteriorAlgebra.ι ℂ u) :=
    eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap u w)
  have h3 : dzb b * (dz c * dzb d) = -(dzb d * (dz c * dzb b)) := by
    have e1 : dzb b * dz c = -(dz c * dzb b) := h _ _
    have e2 : dzb b * dzb d = -(dzb d * dzb b) := h _ _
    have e3 : dz c * dzb d = -(dzb d * dz c) := h _ _
    rw [← mul_assoc, e1, neg_mul, mul_assoc, e2, mul_neg, ← mul_assoc, e3, neg_mul, neg_neg, mul_assoc]
  change dz a * dzb b * (dz c * dzb d) = -(dz a * dzb d * (dz c * dzb b))
  rw [mul_assoc, h3, mul_neg, mul_assoc]

def four (f : Fin n → Fin n → Fin n → Fin n → ℂ) : Ev n :=
  ∑ a, ∑ b, ∑ c, ∑ d, f a b c d • (sym (a, b) * sym (c, d))

theorem four_eq (f : Fin n → Fin n → Fin n → Fin n → ℂ) :
    four f = ∑ x : (Fin n × Fin n) × (Fin n × Fin n), f x.1.1 x.1.2 x.2.1 x.2.2 • (sym x.1 * sym x.2) := by
  simp only [four, Fintype.sum_prod_type]

theorem four_swap (f : Fin n → Fin n → Fin n → Fin n → ℂ) : four (fun a b c d => f c d a b) = four f := by
  rw [four_eq, four_eq]
  refine Fintype.sum_equiv (Equiv.prodComm _ _) _ _ fun x => ?_
  simp [mul_comm]

theorem four_swap' (f : Fin n → Fin n → Fin n → Fin n → ℂ) : four (fun a b c d => f a d c b) = -four f := by
  rw [four_eq, four_eq, ← Finset.sum_neg_distrib]
  refine Fintype.sum_equiv (⟨fun x => ((x.1.1, x.2.2), (x.2.1, x.1.2)), fun x => ((x.1.1, x.2.2), (x.2.1, x.1.2)),
    fun _ => rfl, fun _ => rfl⟩) _ _ ?_
  rintro ⟨⟨a, b⟩, c, d⟩
  simp only [Equiv.coe_fn_mk]
  rw [sym_mul_swap, smul_neg]

theorem four_add (f g : Fin n → Fin n → Fin n → Fin n → ℂ) :
    four (fun a b c d => f a b c d + g a b c d) = four f + four g := by
  simp only [four, add_smul, Finset.sum_add_distrib]

theorem four_sub (f g : Fin n → Fin n → Fin n → Fin n → ℂ) :
    four (fun a b c d => f a b c d - g a b c d) = four f - four g := by
  simp only [four, sub_smul, Finset.sum_sub_distrib]

theorem four_mul (t : ℂ) (f : Fin n → Fin n → Fin n → Fin n → ℂ) :
    four (fun a b c d => t * f a b c d) = t • four f := by
  simp only [four, mul_smul, Finset.smul_sum]

theorem four_wedge (α β : V n → V n → ℂ) :
    four (fun a b c d => wedge α β (coordVec a) (coordVec b) (coordVec c) (coordVec d)) =
      (4 : ℂ) • (ofValues α * ofValues β) := by
  set f : Fin n → Fin n → Fin n → Fin n → ℂ :=
    fun a b c d => α (coordVec a) (coordVec b) * β (coordVec c) (coordVec d) with hf
  have e0 : ofValues α * ofValues β = four f := by
    simp only [ofValues, four, Finset.sum_mul]
    simp only [Finset.mul_sum, smul_mul_smul_comm, hf]
  have e1 := four_swap f
  have e2 := four_swap' f
  have e3 := four_swap' fun a b c d => f c d a b
  have e : four (fun a b c d => wedge α β (coordVec a) (coordVec b) (coordVec c) (coordVec d)) =
      four f + four (fun a b c d => f c d a b) - four (fun a b c d => f a d c b) - four (fun a b c d => f c b a d) := by
    rw [← four_add, ← four_sub, ← four_sub]; rfl
  rw [e, e3, e1, e2, e0]
  module

theorem coeff_two {R : Type} [CommRing R] (F : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) R) :
    (Matrix.charpolyRev (-F)).coeff 2 =
      F (.inl 0) (.inl 0) * F (.inr 0) (.inr 0) - F (.inl 0) (.inr 0) * F (.inr 0) (.inl 0) := by
  rw [Matrix.charpolyRev, ← Matrix.det_submatrix_equiv_self (finSumFinEquiv (m := 1) (n := 1)).symm]
  have h0 : (finSumFinEquiv (m := 1) (n := 1)).symm (0 : Fin 2) = .inl 0 := rfl
  have h1 : (finSumFinEquiv (m := 1) (n := 1)).symm (1 : Fin 2) = .inr 0 := rfl
  rw [Matrix.det_fin_two]
  simp only [Matrix.submatrix_apply, h0, h1]
  have : ∀ p q : Fin 1 ⊕ Fin 1, (1 - (Polynomial.X : Polynomial R) • (-F).map Polynomial.C) p q =
      (if p = q then 1 else 0) + Polynomial.C (F p q) * Polynomial.X := by
    intro p q
    rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.neg_apply, Matrix.one_apply, map_neg, smul_eq_mul]
    ring
  simp only [this]
  have e : ∀ a b c d : R, ((1 + Polynomial.C a * Polynomial.X) * (1 + Polynomial.C d * Polynomial.X) -
      (0 + Polynomial.C b * Polynomial.X) * (0 + Polynomial.C c * Polynomial.X)) =
      1 + Polynomial.C (a + d) * Polynomial.X + Polynomial.C (a * d - b * c) * Polynomial.X ^ 2 := by
    intro a b c d
    simp only [map_add, map_sub, map_mul]; ring
  simp only [if_true, reduceCtorEq, if_false, e]
  simp [Polynomial.coeff_one, Polynomial.coeff_X, -map_add, -map_sub, -map_mul]

theorem aeval_curvPoly {r : Type} [Fintype r] [DecidableEq r] (G : V n → Matrix r r ℂ) (v : V n) (p q : r) :
    MvPolynomial.aeval sym (GlobalTheory.GoodMetric.curvPoly G v p q) = ofValues (fun ξ η => curv G v ξ η p q) := by
  simp [GlobalTheory.GoodMetric.curvPoly, ofValues, Algebra.smul_def]

end GlobalTheory.SecForm.ChernTwo

namespace GlobalTheory.SecForm

open ChernTwo

theorem chernAt_two_eq {n : ℕ} (G : V n → Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ) (v : V n) :
    chernAt G v 2 = ofValuesTwo (chernTwo G v) := by
  have hc : ∀ a b c d, chernTwo G v a b c d = kappa ^ 2 * curvMinor G v (.inl 0) (.inr 0) a b c d := by
    intro a b c d
    simp only [chernTwo, Fintype.sum_sum_type, Finset.univ_unique, Finset.sum_singleton, curvMinor_self,
      Fin.default_eq_zero, curvMinor_comm G v (.inr 0) (.inl 0)]
    ring
  have e : ofValuesTwo (chernTwo G v) = (1 / 4 : ℂ) • four fun a b c d =>
      kappa ^ 2 * curvMinor G v (.inl 0) (.inr 0) (coordVec a) (coordVec b) (coordVec c) (coordVec d) := by
    simp only [ofValuesTwo, four, hc]
  rw [e, four_mul]
  simp only [curvMinor]
  rw [four_sub, four_wedge, four_wedge, chernAt, GlobalTheory.GoodMetric.chernPoly, coeff_two, map_sub, map_mul, map_mul]
  simp only [aeval_curvPoly]
  module

end GlobalTheory.SecForm
