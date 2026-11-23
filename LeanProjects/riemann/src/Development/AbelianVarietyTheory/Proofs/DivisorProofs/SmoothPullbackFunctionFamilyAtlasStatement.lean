import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothPullbackFunctionFamilyAtlas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppendVMemFamAtlasTarget
open Set MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.CxForm GlobalTheory.BcUnique
open scoped ContDiff Real Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_pullback_function_family_atlas : ∀ (M : Type) [TopologicalSpace M] (A : HolAtlas M 1) (φ : ℂ → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ → (famAtlas A).SmoothOn univ fun y => ((y.2.elim 0 φ : ℝ) : ℂ) := by
  first | exact @GlobalTheory.BcUnique.smoothOn_extend_sphere | exact GlobalTheory.BcUnique.smoothOn_extend_sphere | (intros; apply GlobalTheory.BcUnique.smoothOn_extend_sphere <;> assumption)
