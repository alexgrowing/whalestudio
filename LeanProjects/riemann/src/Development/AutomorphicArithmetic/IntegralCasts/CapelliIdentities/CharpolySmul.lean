import Mathlib

theorem UpperTheory.Reformulated.B.Qh50.charpoly_smul_alt.{u_1, u_2} :
    ∀ {k : Type u_1} {ι : Type u_2} [inst : Field k] [inst_1 : Fintype ι] [inst_2 : DecidableEq ι]
    (M : Matrix ι ι k) {c : k},
    c ≠ (0 : k) →
      (c • M).charpoly =
        (Polynomial.C : k → Polynomial k) (c ^ Fintype.card ι) *
          M.charpoly.comp ((Polynomial.C : k → Polynomial k) c⁻¹ * Polynomial.X) := by
  intro k ι _ _ _ M c hc
  have h1 : M.charpoly.comp (Polynomial.C c⁻¹ * Polynomial.X) =
      ((Polynomial.compRingHom (Polynomial.C c⁻¹ * Polynomial.X)).mapMatrix M.charmatrix).det := by
    rw [← RingHom.map_det]
    rfl
  have h2 : (Polynomial.C c : Polynomial k) * Polynomial.C c⁻¹ = 1 := by
    rw [← Polynomial.C_mul, mul_inv_cancel₀ hc, Polynomial.C_1]
  rw [h1, Polynomial.C_pow, ← Matrix.det_smul, Matrix.charpoly]
  congr 1
  refine Matrix.ext fun i j => ?_
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.smul_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
      Matrix.charmatrix_apply_eq, smul_eq_mul, Polynomial.coe_compRingHom_apply,
      Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp, Polynomial.C_mul]
    rw [mul_sub, ← mul_assoc, h2, one_mul]
  · simp only [Matrix.smul_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
      Matrix.charmatrix_apply_ne _ _ _ hij, smul_eq_mul, Polynomial.coe_compRingHom_apply,
      Polynomial.neg_comp, Polynomial.C_comp, Polynomial.C_mul, mul_neg]
