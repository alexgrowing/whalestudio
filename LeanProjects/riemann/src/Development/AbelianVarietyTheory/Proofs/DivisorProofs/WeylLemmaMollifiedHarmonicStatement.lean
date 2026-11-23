import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylLemmaMollifiedHarmonic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppendVMemFamAtlasTarget
open Set MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.CxForm GlobalTheory.BcUnique
open scoped ContDiff Real Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weyl_lemma_mollified_harmonic : ∀ (u : ℂ → ℝ), Continuous u → (∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → ∫ w : ℂ, u w * Laplacian.laplacian φ w = 0) → ∀ ψ : ℂ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → InnerProductSpace.HarmonicOnNhd (MeasureTheory.convolution ψ u (ContinuousLinearMap.lsmul ℝ ℝ) volume) univ := by
  first | exact @GlobalTheory.WeakHarmonicConv.harmonicOnNhd_convolution | exact GlobalTheory.WeakHarmonicConv.harmonicOnNhd_convolution | (intros; apply GlobalTheory.WeakHarmonicConv.harmonicOnNhd_convolution <;> assumption)
