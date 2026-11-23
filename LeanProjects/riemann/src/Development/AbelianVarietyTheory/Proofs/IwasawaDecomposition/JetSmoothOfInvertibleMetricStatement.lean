import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JetSmoothOfInvertibleMetric
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolSprayApply
open Filter Topology Matrix
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jet_smooth_of_invertible_metric : ∀ (d : ℕ) (U : Set (ReciprocityTheory.L2DbarEstimates.V d)) (b : ReciprocityTheory.L2DbarEstimates.V d → Matrix (Fin d) (Fin d) ℂ), IsOpen U → (∀ k l, ContDiffOn ℝ ∞ (fun v => b v k l) U) → (∀ v ∈ U, IsUnit (b v).det) → ∀ n, ContDiffOn ℝ ∞ (GlobalTheory.ChernReg.jet b n) (U ×ˢ (Set.univ : Set (ReciprocityTheory.L2DbarEstimates.V d))) := by
  first | exact @GlobalTheory.ChernReg.contDiffOn_jet | exact GlobalTheory.ChernReg.contDiffOn_jet | (intros; apply GlobalTheory.ChernReg.contDiffOn_jet <;> assumption)
