import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.GramMinorDetTriangularMul
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsKMeas
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_minor_det_triangular_mul : ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) ℂ) (u : Matrix (Fin m) (Fin m) ℂ) (j : ℕ) (hj : j ≤ m), u.BlockTriangular id → (((A * u)ᴴ * (A * u)).submatrix (Fin.castLE hj) (Fin.castLE hj)).det = ((∏ b : Fin j, Complex.normSq (u (Fin.castLE hj b) (Fin.castLE hj b)) : ℝ) : ℂ) * ((Aᴴ * A).submatrix (Fin.castLE hj) (Fin.castLE hj)).det := by
  first | exact @GlobalTheory.HCXi.det_leading_gram_mul_upperTriangular | exact GlobalTheory.HCXi.det_leading_gram_mul_upperTriangular | (intros; apply GlobalTheory.HCXi.det_leading_gram_mul_upperTriangular <;> assumption)
