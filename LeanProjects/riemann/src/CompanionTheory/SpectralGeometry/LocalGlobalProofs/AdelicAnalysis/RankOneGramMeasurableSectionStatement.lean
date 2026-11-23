import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RankOneGramMeasurableSection
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_one_gram_measurable_section : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ x : Fin 1 → Fin M → R ⊗[F] E, IsUnit (gramR R σ J x).det → ∃ s : (Fin 1 → Fin M → R ⊗[F] E) → HA R σ J, Measurable s ∧ (∀ y, gramR R σ J y = gramR R σ J x → actW R σ J (s y) x = y) ∧ ∀ C : Set (Fin 1 → Fin M → R ⊗[F] E), IsCompact C → ∃ C' : Set (HA R σ J), IsCompact C' ∧ ∀ y ∈ C, gramR R σ J y = gramR R σ J x → s y ∈ C' := by
  first | exact @GlobalTheory.CompanionTheory.SW.OrbitSection.orbit_section | exact GlobalTheory.CompanionTheory.SW.OrbitSection.orbit_section | (intros; apply GlobalTheory.CompanionTheory.SW.OrbitSection.orbit_section <;> assumption)
