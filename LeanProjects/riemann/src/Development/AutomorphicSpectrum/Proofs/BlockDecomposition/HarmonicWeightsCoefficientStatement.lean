import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HarmonicWeightsCoefficient
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.HighestVectorsRegularLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WtRInjective
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harmonic_weights_coefficient : ∀ {n : ℕ} (lam : Fin n → ℤ), Antitone lam → ∀ (F : Finset (Fin n → ℤ)), (∀ ν ∈ F, Antitone ν) → ∀ c : (Fin n → ℤ) → ℂ, (∀ z : Fin n → ℂ, (∀ a, ‖z a‖ = 1) → Function.Injective (fun a => z a ^ 2) → ∑ ν ∈ F, c ν * weylChar ν z = (∏ a, ∏ b, (1 + z a / z b)) * weylChar lam (fun a => z a ^ 2)) → ∀ μ ∈ harmZ lam, μ ∈ F ∧ c μ = 2 ^ n := by
  first | exact @GlobalTheory.CompanionTheory.CoefId.coef_harm | exact GlobalTheory.CompanionTheory.CoefId.coef_harm | (intros; apply GlobalTheory.CompanionTheory.CoefId.coef_harm <;> assumption)
