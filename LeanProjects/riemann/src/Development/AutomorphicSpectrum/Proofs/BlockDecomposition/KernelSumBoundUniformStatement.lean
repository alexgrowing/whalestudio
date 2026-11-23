import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelSumBoundUniform
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.InfinitesimalCharacterGlue
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab
open scoped Classical
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_sum_bound_uniform : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)]
  (μ : Measure (GA E N)) [μ.IsHaarMeasure] (δ : ℝ) (α : GA E N → ℂ) (F Ω : Set (GA E N)),
  Continuous α → HasCompactSupport α → 0 < δ → IsFundamentalDomain (latticeGL E N) F μ → IsCompact Ω →
  ∃ B : ENNReal, B ≠ ⊤ ∧ ∀ (n : ℕ) (ψ : Fin n → GA E N → ℂ), (∀ i, Continuous (ψ i)) →
    (∀ i, ∀ γ ∈ latticeGL E N, ∀ x, ψ i (γ * x) = ψ i x) →
    (∀ i, ∃ s : ℂ, δ ≤ ‖s‖ ∧ ∀ x, ∫ y, α y * ψ i (x * y) ∂μ = s * ψ i x) →
    (∀ i, (∫⁻ x in F, ‖ψ i x‖ₑ ^ 2 ∂μ) = 1) →
    (∀ i j, i ≠ j → ∫ x in F, ψ i x * (starRingEnd ℂ) (ψ j x) ∂μ = 0) →
    ∑ i, ∫⁻ x in Ω, ‖ψ i x‖ₑ ^ 2 ∂μ ≤ B := by
  first | exact @GlobalTheory.CompanionTheory.FinDisc.bessel_lintegral_le | exact GlobalTheory.CompanionTheory.FinDisc.bessel_lintegral_le | (intros; apply GlobalTheory.CompanionTheory.FinDisc.bessel_lintegral_le <;> assumption)
