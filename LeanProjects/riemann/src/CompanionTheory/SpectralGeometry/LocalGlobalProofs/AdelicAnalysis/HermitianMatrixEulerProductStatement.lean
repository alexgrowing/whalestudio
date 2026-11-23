import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianMatrixEulerProduct
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_matrix_euler_product : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) E), g.det ≠ 0 → ∃ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c ∧ (∀ ν : Measure (HermR (Ainf F) σ n), ν.IsAddHaarMeasure → ∀ τ : HermR (Ainf F) σ n → HermR (Ainf F) σ n, (∀ S, (τ S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) = cT (sigR (Ainf F) σ) (g.map (inclR (Ainf F))) * (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) * g.map (inclR (Ainf F))) → ν.map τ = cinf • ν) ∧ ∀ v : HeightOneSpectrum (𝓞 F), (∀ ν : Measure (HermR (Fv F v) σ n), ν.IsAddHaarMeasure → ∀ τ : HermR (Fv F v) σ n → HermR (Fv F v) σ n, (∀ S, (τ S : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) = cT (sigR (Fv F v) σ) (g.map (inclR (Fv F v))) * (S : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) * g.map (inclR (Fv F v))) → ν.map τ = c v • ν) := by
  first | exact @GlobalTheory.CompanionTheory.SW.pf_herm | exact GlobalTheory.CompanionTheory.SW.pf_herm | (intros; apply GlobalTheory.CompanionTheory.SW.pf_herm <;> assumption)
