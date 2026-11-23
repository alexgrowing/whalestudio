import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalUnitaryNormalFrame2x2
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ContDiffAtFrameEntry
import Development.AutomorphicSpectrum.Proofs.MetricProofs.WeightedPolynomialHomogeneousCoeffBoundStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsHolomorphicNormalFrameStatement
open MeasureTheory Filter Topology Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_unitary_normal_frame_2x2 : ∀ (d : ℕ) (G : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (y : Fin d → ℂ), (∀ᶠ y' in 𝓝 y, (G y').PosDef) → (∀ p q, ContDiffAt ℝ 2 (fun y' => G y' p q) y) → ∃ g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ, (∀ p q, Differentiable ℂ fun y' => g y' p q) ∧ IsUnit (g y).det ∧ (∀ᶠ y' in 𝓝 y, ((g y')ᴴ * G y' * g y').PosDef) ∧ (∀ p q, ContDiffAt ℝ 2 (fun y' => ((g y')ᴴ * G y' * g y') p q) y) ∧ (g y)ᴴ * G y * g y = 1 ∧ ∀ p q, fderiv ℝ (fun y' => ((g y')ᴴ * G y' * g y') p q) y = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FibPt.exists_frame_normal_near | exact GlobalTheory.CompanionTheory.Ar.PB.FibPt.exists_frame_normal_near | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FibPt.exists_frame_normal_near <;> assumption)
