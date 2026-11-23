import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreVolumeCoverCountable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_volume_cover_countable : ∀ (V K ι : Type) [Countable ι] [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] [T2Space V] [TopologicalSpace K] [MeasurableSpace K] [BorelSpace K] [T2Space K] (μ : Measure V) (lam : Measure K) (Q : V → K) (Z : Set V) (m : K → Measure V), Continuous Q → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ Q id Z lam Set.univ m → ∀ [IsLocallyFiniteMeasure lam], μ Zᶜ = 0 → ∀ A : Set V, IsCompact A → IsOpen A → ∀ (P : ι → Set V) (c : ι → ℝ≥0), (∀ i, IsCompact (P i) ∧ IsOpen (P i) ∧ P i ⊆ Z) → A ∩ Z ⊆ ⋃ i, P i → Summable c → (∀ i (S : Set K), MeasurableSet S → μ (P i ∩ Q ⁻¹' S) ≤ (c i : ℝ≥0∞) * lam S) → (∀ i s, m s (P i) ≤ (c i : ℝ≥0∞)) → ∀ s₀ : K, m s₀ A < ⊤ ∧ ∀ ε : ℝ, 0 < ε → ∃ U ∈ 𝓝 s₀, ∀ S : Set K, MeasurableSet S → S ⊆ U → |(μ (A ∩ Q ⁻¹' S)).toReal - (m s₀ A).toReal * (lam S).toReal| ≤ ε * (lam S).toReal := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.FibreDensity.density_of_summable_cover | exact GlobalTheory.CompanionTheory.WeilSiegel.FibreDensity.density_of_summable_cover | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.FibreDensity.density_of_summable_cover <;> assumption)
