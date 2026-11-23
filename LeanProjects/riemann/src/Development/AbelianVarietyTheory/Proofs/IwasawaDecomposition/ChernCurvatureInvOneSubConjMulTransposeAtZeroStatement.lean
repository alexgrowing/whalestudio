import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernCurvatureInvOneSubConjMulTransposeAtZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernCurvature_inv_one_sub_conj_mul_transpose_at_zero : ∀ {n r s : ℕ} (f g : Fin r → Fin s → Fin n) (ξ η : ReciprocityTheory.L2DbarEstimates.V n), GlobalTheory.HermFrame.curv (fun u : ReciprocityTheory.L2DbarEstimates.V n => (1 - (Matrix.of fun i j => u (f i j)).map (starRingEnd ℂ) * (Matrix.of fun i j => u (g i j))ᵀ)⁻¹) 0 ξ η = -((Matrix.of fun i j => ξ (g i j)) * (Matrix.of fun i j => η (f i j))ᴴ) := by
  first | exact @GlobalTheory.HermFrame.curv_inv_one_sub_conj_mul_transpose_zero | exact GlobalTheory.HermFrame.curv_inv_one_sub_conj_mul_transpose_zero | (intros; apply GlobalTheory.HermFrame.curv_inv_one_sub_conj_mul_transpose_zero <;> assumption)
