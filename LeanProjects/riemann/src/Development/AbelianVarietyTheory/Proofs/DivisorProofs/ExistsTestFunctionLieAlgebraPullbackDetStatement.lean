import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTestFunctionLieAlgebraPullbackDet
import Development.AbelianVarietyTheory.Definitions.Divisors.GlRes
import Development.AbelianVarietyTheory.Definitions.Divisors.IsExpLieAlgebraComplexUnits
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.HCA GroundTheory.Automorphic
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_test_function_lie_algebra_pullback_det : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), ∀ α : glG E a → ℂ, (glH E a).IsSmoothFun α → HasCompactSupport α → ∃ β : Lie E a → ℂ, GlobalTheory.CuspQuot.IsTest (invSet E a) β ∧ ∀ y : glG E a, β (toL y.1.val) = ((|LinearMap.det ((lmul (toL y.1.val) : Lie E a →L[ℝ] Lie E a) : Lie E a →ₗ[ℝ] Lie E a)|⁻¹ : ℝ) : ℂ) * α y := by
  first | exact @GlobalTheory.GLExt.exists_isTest_ext | exact GlobalTheory.GLExt.exists_isTest_ext | (intros; apply GlobalTheory.GLExt.exists_isTest_ext <;> assumption)
