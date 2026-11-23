import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopDegreeFormCoeffProdDetHermitianSquarePowNonne
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNegSqZero
open Matrix MvPolynomial GlobalTheory.GoodMetric GlobalTheory.HermFrame GlobalTheory.PointFormSign
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexOrder Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topDegreeFormCoeff_prod_det_hermitianSquare_pow_nonneg : ∀ {n : ℕ} {κ : Type} [Fintype κ] (m r e : κ → ℕ) (T : ∀ t, V n →ₗ[ℂ] Matrix (Fin (m t)) (Fin (r t)) ℂ),
    0 ≤ topCoeff (∏ t, (sqPoly (T t)).det ^ e t) := by
  first | exact @GlobalTheory.PointFormSign.topCoeff_prod_det_sqPoly_pow_nonneg | exact GlobalTheory.PointFormSign.topCoeff_prod_det_sqPoly_pow_nonneg | (intros; apply GlobalTheory.PointFormSign.topCoeff_prod_det_sqPoly_pow_nonneg <;> assumption)
