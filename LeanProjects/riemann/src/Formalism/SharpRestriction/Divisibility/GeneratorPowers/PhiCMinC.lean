import Formalism.SharpRestriction.Divisibility.GeneratorPowers.PhiCMinSt

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin

open Matrix

theorem whiten_holds : WhitenStatement := by
  intro d L hL
  have hH := hL.isHermitian
  set U : Matrix (Fin d) (Fin d) ℝ := (hH.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ) with hU
  set s : Matrix (Fin d) (Fin d) ℝ := Matrix.diagonal (fun i => Real.sqrt (hH.eigenvalues i)) with hs
  have hspec := hH.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hspec
  have hstar : star U = Uᵀ := by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  have hsq : s * s = Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) := by
    rw [hs, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    simp [Real.mul_self_sqrt (hL.eigenvalues_pos i).le]
  refine ⟨s * Uᵀ, ?_, ?_⟩
  · have hUU : star U * U = 1 := Unitary.star_mul_self_of_mem hH.eigenvectorUnitary.2
    have h1 : (star U).det * U.det = 1 := by
      rw [← Matrix.det_mul, hUU, Matrix.det_one]
    have hdU : IsUnit U.det := isUnit_iff_ne_zero.mpr (right_ne_zero_of_mul_eq_one h1)
    rw [Matrix.det_mul, Matrix.det_transpose]
    refine IsUnit.mul ?_ hdU
    rw [hs, Matrix.det_diagonal, isUnit_iff_ne_zero]
    exact (Finset.prod_pos fun i _ => Real.sqrt_pos.mpr (hL.eigenvalues_pos i)).ne'
  · rw [Matrix.transpose_mul, Matrix.transpose_transpose, hs, Matrix.diagonal_transpose, ← hs,
      Matrix.mul_assoc, ← Matrix.mul_assoc s s, hsq, ← Matrix.mul_assoc, ← hstar]
    exact hspec

end Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin
