import Mathlib
import Formalism.GelfandTransference.Statement

namespace Bl.DetNormLeProdRows

private theorem det_norm_le_prod_rows (ρ : ℕ) (A : Matrix (Fin ρ) (Fin ρ) ℂ) :
    ‖A.det‖ ≤ ∏ i, ‖(WithLp.toLp 2 (A i) : EuclideanSpace ℂ (Fin ρ))‖ := by
  classical
  let v : Fin ρ → EuclideanSpace ℂ (Fin ρ) := fun i => WithLp.toLp 2 (A i)
  have h : Module.finrank ℂ (EuclideanSpace ℂ (Fin ρ)) = Fintype.card (Fin ρ) := by simp
  let e := (EuclideanSpace.basisFun (Fin ρ) ℂ).toBasis
  let b := InnerProductSpace.gramSchmidtOrthonormalBasis h v
  have he : e.det v = A.det := by
    rw [Module.Basis.det_apply, ← Matrix.det_transpose A]
    congr 1
  have hbv : b.toBasis.det v = b.toBasis.det e * e.det v := by
    rw [Module.Basis.det_apply, Module.Basis.det_apply, Module.Basis.det_apply, ← Matrix.det_mul,
      Module.Basis.toMatrix_mul_toMatrix]
  have hb1 : ‖b.toBasis.det e‖ = 1 := by
    simp [e]
  have key : ‖A.det‖ = ‖b.toBasis.det v‖ := by
    rw [hbv, norm_mul, hb1, one_mul, he]
  rw [key, InnerProductSpace.gramSchmidtOrthonormalBasis_det h v, norm_prod]
  apply Finset.prod_le_prod (fun i _ => norm_nonneg _)
  intro i _
  calc ‖inner ℂ (b i) (v i)‖ ≤ ‖b i‖ * ‖v i‖ := norm_inner_le_norm _ _
    _ = ‖v i‖ := by rw [b.orthonormal.1 i, one_mul]

theorem goal1 :
  Formalism.HadamardInequality.Hadamard := by
  intro ρ A
  have h0 := det_norm_le_prod_rows ρ A
  calc ‖A.det‖ ^ 2 ≤ (∏ i, ‖(WithLp.toLp 2 (A i) : EuclideanSpace ℂ (Fin ρ))‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h0 2
    _ = ∏ i, ∑ j, ‖A i j‖ ^ 2 := by
        rw [← Finset.prod_pow]
        refine Finset.prod_congr rfl (fun i _ => ?_)
        rw [EuclideanSpace.norm_sq_eq]

end Bl.DetNormLeProdRows
