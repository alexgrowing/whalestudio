import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ArchimedeanFrameKTypeDecomposition
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CoefS
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasureStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalRankOneDensityUniformizerPower
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal NNReal Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_measure_scaling_transform : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure (Ainf F)), lam.IsAddHaarMeasure → ∀ t : Ainf F, IsUnit t → ∀ c : ℝ≥0, lam.map (fun y => t * y) = c • lam → ∀ τ : HermR (Ainf F) σ 1 → HermR (Ainf F) σ 1, Measurable τ → (∀ S i j, (τ S : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)) i j = algebraMap (Ainf F) (Ainf F ⊗[F] E) t * (S : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)) i j) → (GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b lam 1).map τ = c • GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b lam 1 := by
  first | exact @GlobalTheory.CompanionTheory.SW.DilU.coordHerm_map_ainf | exact GlobalTheory.CompanionTheory.SW.DilU.coordHerm_map_ainf | (intros; apply GlobalTheory.CompanionTheory.SW.DilU.coordHerm_map_ainf <;> assumption)
