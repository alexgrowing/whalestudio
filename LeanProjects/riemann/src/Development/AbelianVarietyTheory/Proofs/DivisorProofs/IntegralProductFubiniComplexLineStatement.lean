import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralProductFubiniComplexLine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppendVMemFamAtlasTarget
open Set MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.CxForm GlobalTheory.BcUnique
open scoped ContDiff Real Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_product_fubini_complex_line : ∀ f : V (1 + 1) → ℝ, Integrable f → ∫ x, f x = ∫ w : ℂ, ∫ v : V 1, f (appendV 1 1 (v, EuclideanSpace.single 0 w)) := by
  first | exact @GlobalTheory.BcUnique.integral_eq_integral_last_head | exact GlobalTheory.BcUnique.integral_eq_integral_last_head | (intros; apply GlobalTheory.BcUnique.integral_eq_integral_last_head <;> assumption)
