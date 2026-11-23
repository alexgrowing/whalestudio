import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralMulEqZeroOfCosetIntegralEqZero
import Development.AbelianVarietyTheory.Definitions.Foundations.ContinuousOfMemCcSmooth
open MeasureTheory GlobalTheory.AutomorphicL2Unitary
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_mul_eq_zero_of_coset_integral_eq_zero_alt : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G), IsClosed (H : Set G) → ∀ (ν : Measure H) [ν.IsHaarMeasure] (μ : Measure G) [μ.IsHaarMeasure] (f w : G → ℂ), Continuous f → HasCompactSupport f → LocallyIntegrable w μ → (∀ u ∈ H, (fun g => w (u * g)) =ᵐ[μ] w) → (∀ g, ∫ u : H, f (u * g) ∂ν = 0) → ∫ g, f g * w g ∂μ = 0 := by
  first | exact @GlobalTheory.CosetIntegralZero.integral_mul_eq_zero_of_coset_integral_eq_zero | exact GlobalTheory.CosetIntegralZero.integral_mul_eq_zero_of_coset_integral_eq_zero | (intros; apply GlobalTheory.CosetIntegralZero.integral_mul_eq_zero_of_coset_integral_eq_zero <;> assumption)
