import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ScalarMultiplicationEulerProduct
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scalar_multiplication_euler_product : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ t : E, t ≠ 0 → ∃ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c ∧ (∀ μ : Measure (Ainf F ⊗[F] E), μ.IsAddHaarMeasure → μ.map (fun y => inclR (Ainf F) t * y) = cinf • μ) ∧ ∀ v : HeightOneSpectrum (𝓞 F), (∀ μ : Measure (Fv F v ⊗[F] E), μ.IsAddHaarMeasure → μ.map (fun y => inclR (Fv F v) t * y) = c v • μ) := by
  first | exact @GlobalTheory.CompanionTheory.SW.map_inclR_prodFormula | exact GlobalTheory.CompanionTheory.SW.map_inclR_prodFormula | (intros; apply GlobalTheory.CompanionTheory.SW.map_inclR_prodFormula <;> assumption)
