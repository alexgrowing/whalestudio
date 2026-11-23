import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaxSlopeSqLeOfNoShortVector
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.MeanHeightDescent.DivisionInequalityWithCovolume
import Formalism.MeanHeightDescent.CovolumeFullAssemblyWeighted
open NumberField GlobalTheory.AllWt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maxSlope_sq_le_of_no_short_vector : ∀ (K V : Type) [Field K] [NumberField K] [IsTotallyComplex K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (N : (K →+* ℂ) → V → ℝ) (L : Submodule (𝓞 K) V) (La : ℝ), HasGram N → (∀ σ x, N ((starRingEnd ℂ).comp σ) x = N σ x) → L.FG → L ≠ ⊥ → (∀ x ∈ L, x ≠ 0 → -La ≤ (∑ σ : K →+* ℂ, Real.log (N σ x)) / (Module.finrank ℚ K : ℝ)) → slopeMax_sq N L ≤ 2 * La + Real.log (Module.finrank K V : ℝ) + Real.log |(discr K : ℝ)| / (Module.finrank ℚ K : ℝ) := by
  first | exact @GlobalTheory.SlopeMink.slopeMax_sq_le_of_no_short | exact GlobalTheory.SlopeMink.slopeMax_sq_le_of_no_short | (intros; apply GlobalTheory.SlopeMink.slopeMax_sq_le_of_no_short <;> assumption)
