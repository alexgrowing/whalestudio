import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalRankOneDensityUniformizerPower
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_rank_one_density_uniformizer_power : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → ∀ m, IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b lam 1 M) (coordHerm (Fv F v) σ b lam 1) m → 1 ≤ M → ∀ (a : ℕ) (e : ℕ), 0 < a → (Ideal.span {(a : 𝓞 F)}) ≤ v.asIdeal ^ e → ¬ (Ideal.span {(a : 𝓞 F)}) ≤ v.asIdeal ^ (e + 1) → ∀ (s : Fv F v) (A : Set (Fin 1 → Fin M → Fv F v ⊗[F] E)), MeasurableSet A → m (hermScal (Fv F v) σ s) {X | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ A} = (Ideal.absNorm v.asIdeal : ℝ≥0∞) ^ (e * (2 * M - 2)) * m (hermScal (Fv F v) σ ((a : Fv F v) ^ 2 * s)) A := by
  first | exact @GlobalTheory.CompanionTheory.SW.Dil.dilation | exact GlobalTheory.CompanionTheory.SW.Dil.dilation | (intros; apply GlobalTheory.CompanionTheory.SW.Dil.dilation <;> assumption)
