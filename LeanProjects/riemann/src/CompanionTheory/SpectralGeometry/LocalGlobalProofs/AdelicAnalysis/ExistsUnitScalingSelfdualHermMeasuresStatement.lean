import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsUnitScalingSelfdualHermMeasures
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_scaling_selfdual_herm_measures : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf laminf → (∀ v, IsStdV v (lam v)) → ∀ ψ, IsCharAF F ψ → ∀ n : ℕ, ∃ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c ∧ (∀ ν, SdHerm F E σ (Ainf F) (psiInf F ψ) n ν ↔ ν = cinf • coordHerm (Ainf F) σ b laminf n) ∧ ∀ v : HeightOneSpectrum (𝓞 F), (∀ ν, SdHerm F E σ (Fv F v) (psiV F ψ v) n ν ↔ ν = c v • coordHerm (Fv F v) σ b (lam v) n) := by
  first | exact @GlobalTheory.CompanionTheory.SW.sdHerm_eq_coord | exact GlobalTheory.CompanionTheory.SW.sdHerm_eq_coord | (intros; apply GlobalTheory.CompanionTheory.SW.sdHerm_eq_coord <;> assumption)
