import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MahlerMeasureOfProduct
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IsScaleStable
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mahler_measure_of_product : ∀ (n e : ℕ) (h : HermNorm n) {ι : Type} (s : Finset ι) (q : ι → MvPolynomial (Fin e × Fin n) ℂ) (d : ι → ℕ) (a : ι → ℕ) (c : ℂ), c ≠ 0 → (∀ i ∈ s, q i ≠ 0 ∧ IsMultiHomog (d i) (q i)) → mahler h e (C c * ∏ i ∈ s, q i ^ a i) = Real.log ‖c‖ + ∑ i ∈ s, (a i : ℝ) * mahler h e (q i) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Short.Crofton.mahler_C_mul_prod_pow | exact GlobalTheory.CompanionTheory.Ar.Short.Crofton.mahler_C_mul_prod_pow | (intros; apply GlobalTheory.CompanionTheory.Ar.Short.Crofton.mahler_C_mul_prod_pow <;> assumption)
