import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIntegralOrInvIsIntegralFiniteExtUltrametric
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_or_inv_isIntegral_finite_ext_ultrametric : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F] (k : Type) [Field k] [Algebra F k] [FiniteDimensional F k] (y : k), y ≠ 0 → IsIntegral (NormedField.valuation (K := F)).integer y ∨ IsIntegral (NormedField.valuation (K := F)).integer y⁻¹ := by
  first | exact @GlobalTheory.JR.Spec.isIntegral_or_isIntegral_inv | exact GlobalTheory.JR.Spec.isIntegral_or_isIntegral_inv | (intros; apply GlobalTheory.JR.Spec.isIntegral_or_isIntegral_inv <;> assumption)
