import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCompLinearMapMatrixNonarchLocalField
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParP
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_comp_linearMap_matrix_nonarchLocalField : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (a b : ℕ) (L : Matrix (Fin a) (Fin b) F →ₗ[F] Matrix (Fin a) (Fin b) F) (hL : LinearMap.det L ≠ 0) (φ : Matrix (Fin a) (Fin b) F → ℂ) (μ : @MeasureTheory.Measure (Matrix (Fin a) (Fin b) F) (borel _)), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∫ x, φ (L x) ∂μ = ((((MeasureTheory.distribHaarChar F (Units.mk0 _ hL) : NNReal) : ℝ) : ℂ))⁻¹ * ∫ x, φ x ∂μ := by
  first | exact @GlobalTheory.DetScale.integral_comp_matrix | exact GlobalTheory.DetScale.integral_comp_matrix | (intros; apply GlobalTheory.DetScale.integral_comp_matrix <;> assumption)
