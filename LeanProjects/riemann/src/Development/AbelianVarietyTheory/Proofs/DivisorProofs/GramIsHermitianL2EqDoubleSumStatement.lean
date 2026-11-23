import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramIsHermitianL2EqDoubleSum
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
open Filter Topology MeasureTheory GlobalTheory.HSAmp
open scoped ComplexOrder Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_isHermitian_l2_eq_double_sum : ∀ (S : Type) (Y : S → Type) [∀ σ, MeasurableSpace (Y σ)] (ι : Type) [Fintype ι] [DecidableEq ι] (μ : ∀ σ, Measure (Y σ)) (v : ∀ σ, Y σ → ι → ℂ), IsFam μ v → (gram μ v).IsHermitian ∧ ∀ c : ι → ℂ, (∀ σ, Integrable (cmb v c σ) (μ σ)) ∧ 0 ≤ l2 μ v c ∧ (l2 μ v c : ℂ) = ∑ i, ∑ j, c i * (starRingEnd ℂ) (c j) * gram μ v i j := by
  first | exact @GlobalTheory.HSAmp.gram_isHermitian_and_l2_eq_quadratic_form | exact GlobalTheory.HSAmp.gram_isHermitian_and_l2_eq_quadratic_form | (intros; apply GlobalTheory.HSAmp.gram_isHermitian_and_l2_eq_quadratic_form <;> assumption)
