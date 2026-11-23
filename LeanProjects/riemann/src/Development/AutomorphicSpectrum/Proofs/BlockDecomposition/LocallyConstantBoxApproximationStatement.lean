import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocallyConstantBoxApproximation
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetOff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarMeasureLocalBallStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locally_constant_box_approximation : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → ∀ (ι : Type) [Fintype ι] (ψ : (ι → Fv F v) → ℝ), Continuous ψ → HasCompactSupport ψ → ∃ B : ℝ, 0 ≤ B ∧ ∀ δ : ℝ, 0 < δ → ∃ (k : ℕ) (C : Finset (ι → Fv F v)), (∀ y, |ψ y - ∑ c ∈ C, ψ c * boxInd v k c y| ≤ δ * ∑ c ∈ C, boxInd v k c y) ∧ (C.card : ℝ) * (((Ideal.absNorm v.asIdeal : ℝ) ^ k) ^ Fintype.card ι)⁻¹ ≤ B ∧ |(∫ y, ψ y ∂(Measure.pi fun _ => lam)) - ∑ c ∈ C, ψ c * (((Ideal.absNorm v.asIdeal : ℝ) ^ k) ^ Fintype.card ι)⁻¹| ≤ δ * B := by
  first | exact @GlobalTheory.CompanionTheory.Equi.LocApprox.loc_approx | exact GlobalTheory.CompanionTheory.Equi.LocApprox.loc_approx | (intros; apply GlobalTheory.CompanionTheory.Equi.LocApprox.loc_approx <;> assumption)
