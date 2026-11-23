import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CauchyRiemannIffDifferentiableOnComplex
open Complex Matrix
open scoped ContDiff BigOperators Real
theorem _root_.GlobalTheory.T.cauchyRiemann_iff_differentiableOn : ∀ (g : ℕ) (U : Set (Fin g → ℂ)) (f : (Fin g → ℂ) → ℂ), IsOpen U → (DifferentiableOn ℝ f U → ((∀ a, ∀ z ∈ U, (fderiv ℝ f z (Pi.single a 1 : Fin g → ℂ) + I * fderiv ℝ f z (I • (Pi.single a 1 : Fin g → ℂ))) = 0) ↔ DifferentiableOn ℂ f U)) ∧ (DifferentiableOn ℂ f U → ContDiffOn ℝ ∞ f U ∧ ∀ v, DifferentiableOn ℂ (fun z => fderiv ℂ f z v) U) := by
  first | exact @GlobalTheory.cauchyRiemann_iff_differentiableOn_complex | exact GlobalTheory.cauchyRiemann_iff_differentiableOn_complex | (intros; apply GlobalTheory.cauchyRiemann_iff_differentiableOn_complex <;> assumption)
