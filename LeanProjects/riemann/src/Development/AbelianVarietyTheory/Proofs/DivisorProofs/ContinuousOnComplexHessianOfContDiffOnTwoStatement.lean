import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOnComplexHessianOfContDiffOnTwo
import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
open Filter Topology MeasureTheory Metric ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuousOn_complex_hessian_of_contDiffOn_two : ∀ (n : ℕ) (U : Set (V n)) (φ : V n → ℝ), IsOpen U → ContDiffOn ℝ 2 φ U → ∀ j l, ContinuousOn (fun z => cHess n (fun v => (φ v : ℂ)) z j l) U := by
  first | exact @GlobalTheory.continuousOn_cHess_of_contDiffOn_two | exact GlobalTheory.continuousOn_cHess_of_contDiffOn_two | (intros; apply GlobalTheory.continuousOn_cHess_of_contDiffOn_two <;> assumption)
