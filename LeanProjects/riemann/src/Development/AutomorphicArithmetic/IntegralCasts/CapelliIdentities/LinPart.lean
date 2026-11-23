import Mathlib

noncomputable def UpperTheory.Reformulated.B.ComplexLinearPart.linPart :
    {a b : ℕ} → ((Fin a → ℂ) →ₗ[ℝ] Fin b → ℂ) → (Fin a → ℂ) →ₗ[ℂ] Fin b → ℂ :=
  fun {a b} T =>
    { toFun := fun v => (1 / 2 : ℂ) • (T v - Complex.I • T (Complex.I • v))
      map_add' := fun v w => by
        simp only [smul_add, map_add]
        module
      map_smul' := fun c v => by
        have hc : ∀ {n : ℕ} (x : Fin n → ℂ), c • x = c.re • x + c.im • (Complex.I • x) := by
          intro n x
          ext j
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul]
          rw [← mul_assoc, ← add_mul, Complex.re_add_im]
        have hI : Complex.I • Complex.I • v = -v := by
          rw [smul_smul, Complex.I_mul_I, neg_one_smul]
        have h1 : T (c • v) = c.re • T v + c.im • T (Complex.I • v) := by
          rw [hc v, T.map_add, T.map_smul, T.map_smul]
        have h2 : T (Complex.I • c • v) = c.re • T (Complex.I • v) - c.im • T v := by
          rw [smul_comm Complex.I c v, hc (Complex.I • v), hI, T.map_add, T.map_smul, T.map_smul,
            map_neg, smul_neg, sub_eq_add_neg]
        rw [h1, h2, RingHom.id_apply]
        ext j
        simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul]
        conv_rhs => rw [← Complex.re_add_im c]
        linear_combination (1 / 2 : ℂ) * c.im * T (Complex.I • v) j * Complex.I_mul_I }
