import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableHermC
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousBlkM
open MeasureTheory Matrix
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt

theorem det_one_add_sq_eq_prod_eigenvalues (n : ℕ) (b : Matrix (Fin n) (Fin n) ℂ) (hb : b.IsHermitian) :
    Matrix.det (1 + b * b) = ((∏ i, (1 + hb.eigenvalues i ^ 2) : ℝ) : ℂ) := by
  set U : Matrix (Fin n) (Fin n) ℂ := (hb.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  set D : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.diagonal (fun i => ((hb.eigenvalues i : ℝ) : ℂ)) with hD
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self hb.eigenvectorUnitary
  have hUU' : U * star U = 1 := Unitary.coe_mul_star_self hb.eigenvectorUnitary
  have hs : b = U * D * star U := by
    have := hb.spectral_theorem
    simpa [Unitary.conjStarAlgAut_apply, hU, hD, Function.comp_def] using this
  have h1 : 1 + b * b = U * (1 + D * D) * star U := by
    rw [hs]
    calc 1 + U * D * star U * (U * D * star U)
        = U * star U + U * D * (star U * U) * D * star U := by
          rw [hUU']; simp only [Matrix.mul_assoc]
      _ = U * (1 + D * D) * star U := by
          rw [hUU]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_assoc]
  have hdet : (star U).det * U.det = 1 := by
    rw [← Matrix.det_mul, hUU, Matrix.det_one]
  have h2 : 1 + D * D = Matrix.diagonal (fun i => (((1 + hb.eigenvalues i ^ 2 : ℝ)) : ℂ)) := by
    rw [hD, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one, Matrix.diagonal_add]
    congr 1
    ext i
    push_cast
    ring
  rw [h1, Matrix.det_mul, Matrix.det_mul, h2, Matrix.det_diagonal]
  push_cast
  calc U.det * (∏ i, (1 + ((hb.eigenvalues i : ℝ) : ℂ) ^ 2)) * (star U).det
      = ((star U).det * U.det) * ∏ i, (1 + ((hb.eigenvalues i : ℝ) : ℂ) ^ 2) := by ring
    _ = _ := by rw [hdet, one_mul]

theorem one_le_detW : ∀ (n : ℕ) (b : Matrix (Fin n) (Fin n) ℂ), b.IsHermitian → 1 ≤ detW b := by
  intro n b hb
  unfold detW
  rw [det_one_add_sq_eq_prod_eigenvalues n b hb, Complex.ofReal_re]
  have : ∀ i ∈ (Finset.univ : Finset (Fin n)), (1 : ℝ) ≤ 1 + hb.eigenvalues i ^ 2 := fun i _ => by
    nlinarith [sq_nonneg (hb.eigenvalues i)]
  calc (1 : ℝ) = ∏ _i : Fin n, (1 : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one) this

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
