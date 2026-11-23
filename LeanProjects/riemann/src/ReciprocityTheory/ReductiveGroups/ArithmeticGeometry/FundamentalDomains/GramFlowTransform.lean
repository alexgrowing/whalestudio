import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.PositiveMinorUnits

namespace ReciprocityTheory.ChartRestriction.G.FD.GramFlowTransform
open Complex Matrix ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal
open scoped ComplexConjugate
noncomputable section

variable {E : Type} [Field E] {r : ℕ} {τ : E →+* ℂ} {G : Matrix (Fin r) (Fin r) E}

def flw (α : ℂ) (e : Fin r → ℂ) (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) {n : ℕ}
    (f : Fin n → Fin r → ℂ) : Fin n → Fin r → ℂ :=
  fun a => f a + (α * hermC τ G (f a) e) • e

theorem cv_flw (hG : ∀ a b, τ (G b a) = conj (τ (G a b))) (e : Fin r → ℂ)
    (he : hermC τ G e e = 0) (α : ℂ) {n : ℕ} (f : Fin n → Fin r → ℂ) :
    cv τ G (flw α e τ G f) e = cv τ G f e := by
  funext a
  show hermC τ G e (f a + (α * hermC τ G (f a) e) • e) = hermC τ G e (f a)
  rw [GramDeterminantReal.hC_add_right, GramDeterminantReal.hermC_smul_right, he, mul_zero, add_zero]
  all_goals exact hG

theorem gramF_flw (hG : ∀ a b, τ (G b a) = conj (τ (G a b))) (e : Fin r → ℂ)
    (he : hermC τ G e e = 0) (α : ℂ) {n : ℕ} (f : Fin n → Fin r → ℂ) :
    gramF τ G (flw α e τ G f) = gramF τ G f +
      replicateCol Unit (fun a => (α + conj α) * conj (cv τ G f e a)) *
        replicateRow Unit (cv τ G f e) := by
  ext a b
  have hc := GramDeterminantReal.hC_conj hG
  simp only [Matrix.add_apply, Matrix.mul_apply, replicateCol, replicateRow, Matrix.of_apply,
    Finset.univ_unique, Finset.sum_singleton, GramDeterminantReal.gramF, flw]
  rw [GramDeterminantReal.hC_add_left, GramDeterminantReal.hC_add_right, GramDeterminantReal.hC_add_right,
    GramDeterminantReal.hermC_smul_left, GramDeterminantReal.hermC_smul_left, GramDeterminantReal.hermC_smul_right,
    GramDeterminantReal.hermC_smul_right, he, hc e (f a)]
  all_goals try exact hG
  simp only [GramDeterminantReal.cv, map_mul]
  rw [← hc (f b) e]
  ring

theorem mt_y {n : ℕ} (f : Fin n → Fin r → ℂ) (e : Fin r → ℂ) :
    GramDeterminantReal.mt τ G f e = ∑ b, yv τ G f e b * conj (cv τ G f e b) := by
  simp only [GramDeterminantReal.mt, GramDeterminantReal.yv, Matrix.vecMul, dotProduct, Finset.sum_mul]
  exact Finset.sum_comm

theorem det_flw (hG : ∀ a b, τ (G b a) = conj (τ (G a b))) (e : Fin r → ℂ)
    (he : hermC τ G e e = 0) (α : ℂ) {n : ℕ} (f : Fin n → Fin r → ℂ)
    (hA : IsUnit (gramF τ G f).det) : (gramF τ G (flw α e τ G f)).det =
      (gramF τ G f).det * (1 + (α + conj α) * GramDeterminantReal.mt τ G f e) := by
  rw [gramF_flw hG e he α f, Matrix.det_add_replicateCol_mul_replicateRow hA]
  congr 1
  rw [Matrix.det_unique]
  simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.mul_apply, replicateCol, replicateRow,
    Matrix.of_apply, Finset.univ_unique, Finset.sum_singleton, GramDeterminantReal.mt, Finset.mul_sum,
    Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem mt_flw (hG : ∀ a b, τ (G b a) = conj (τ (G a b))) (e : Fin r → ℂ)
    (he : hermC τ G e e = 0) (α : ℂ) {n : ℕ} (f : Fin n → Fin r → ℂ)
    (hA : IsUnit (gramF τ G f).det) (h1 : 1 + (α + conj α) * GramDeterminantReal.mt τ G f e ≠ 0) :
    GramDeterminantReal.mt τ G (flw α e τ G f) e =
      GramDeterminantReal.mt τ G f e / (1 + (α + conj α) * GramDeterminantReal.mt τ G f e) := by
  set s := α + conj α with hs
  set m := GramDeterminantReal.mt τ G f e with hm
  have hA' : IsUnit (gramF τ G (flw α e τ G f)).det := by
    rw [det_flw hG e he α f hA]
    exact hA.mul (isUnit_iff_ne_zero.mpr h1)
  have hyA : Matrix.vecMul (yv τ G f e) (gramF τ G f) = cv τ G f e := by
    simp only [GramDeterminantReal.yv, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hA, Matrix.vecMul_one]
  have hyB : Matrix.vecMul (yv τ G f e)
      (replicateCol Unit (fun a => s * conj (cv τ G f e a)) * replicateRow Unit (cv τ G f e)) =
      (s * m) • cv τ G f e := by
    funext j
    simp only [Matrix.vecMul, dotProduct, Matrix.mul_apply, replicateCol, replicateRow,
      Matrix.of_apply, Finset.univ_unique, Finset.sum_singleton, Pi.smul_apply, smul_eq_mul]
    rw [hm, mt_y, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have key : Matrix.vecMul (yv τ G f e) (gramF τ G (flw α e τ G f)) =
      (1 + s * m) • cv τ G f e := by
    rw [gramF_flw hG e he α f, Matrix.vecMul_add, hyA, hyB, add_smul, one_smul]
  have hy : yv τ G (flw α e τ G f) e = (1 + s * m)⁻¹ • yv τ G f e := by
    have h2 : yv τ G f e = (1 + s * m) • yv τ G (flw α e τ G f) e := by
      conv_rhs => rw [GramDeterminantReal.yv, cv_flw hG e he α f, ← Matrix.smul_vecMul, ← key,
        Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hA', Matrix.vecMul_one]
    rw [h2, smul_smul, inv_mul_cancel₀ h1, one_smul]
  rw [mt_y (flw α e τ G f) e, hy, cv_flw hG e he α f, div_eq_inv_mul]
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
  congr 1
  exact (mt_y f e).symm

end

end ReciprocityTheory.ChartRestriction.G.FD.GramFlowTransform
