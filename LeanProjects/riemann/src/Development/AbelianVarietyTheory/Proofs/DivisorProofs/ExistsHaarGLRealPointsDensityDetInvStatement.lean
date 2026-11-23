import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarGLRealPointsDensityDetInv
import Development.AbelianVarietyTheory.Definitions.Divisors.GlRes
import Development.AbelianVarietyTheory.Definitions.Divisors.IsExpLieAlgebraComplexUnits
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.HCA GroundTheory.Automorphic
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_haar_GL_realPoints_density_det_inv : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), ∀ (ν : Measure (Lie E a)), ν.IsAddHaarMeasure → ∀ [MeasurableSpace (glG E a)] [BorelSpace (glG E a)], ∃ μ : Measure (glG E a), μ.IsHaarMeasure ∧ ∀ (Φ : Lie E a → ℂ), ContinuousOn Φ (invSet E a) → (∀ x ∉ invSet E a, Φ x = 0) → ∫ y, Φ (toL y.1.val) ∂μ = ∫ x, ((|LinearMap.det ((lmul x : Lie E a →L[ℝ] Lie E a) : Lie E a →ₗ[ℝ] Lie E a)|⁻¹ : ℝ) : ℂ) * Φ x ∂ν := by
  first | exact @GlobalTheory.GLHaar.glHaar | exact GlobalTheory.GLHaar.glHaar | (intros; apply GlobalTheory.GLHaar.glHaar <;> assumption)
