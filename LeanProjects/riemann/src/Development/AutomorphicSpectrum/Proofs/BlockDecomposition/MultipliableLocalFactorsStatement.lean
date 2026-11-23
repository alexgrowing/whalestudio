import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultipliableLocalFactors
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TruncSum
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.Mass.MeanV PositivityTheory.Rg.Mass NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped ENNReal NNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multipliable_local_factors : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (C : ℝ) (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ), (∀ v, v ∉ S → ∀ s : Fv F v, Valued.v s = 1 → |g v s - 1| ≤ C / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) → ∀ β : F, β ≠ 0 → Multipliable fun v => g v (algebraMap F (Fv F v) β) := by
  first | exact @GlobalTheory.CompanionTheory.Mass.MeanV.multipliable_localFactors | exact GlobalTheory.CompanionTheory.Mass.MeanV.multipliable_localFactors | (intros; apply GlobalTheory.CompanionTheory.Mass.MeanV.multipliable_localFactors <;> assumption)
