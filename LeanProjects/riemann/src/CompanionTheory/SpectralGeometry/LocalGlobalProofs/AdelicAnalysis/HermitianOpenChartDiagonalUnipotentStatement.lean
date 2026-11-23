import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianOpenChartDiagonalUnipotent
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_open_chart_diagonal_unipotent : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ n : ℕ, ∃ o : (Fin n → Rˣ) × ({p : Fin n × Fin n // p.1 < p.2} → R ⊗[F] E) → HermR R σ n, IsOpenEmbedding o ∧ ∀ d u, ∀ N : Matrix (Fin n) (Fin n) (R ⊗[F] E), (N = Matrix.of fun i j => if i = j then 1 else if h : i < j then u ⟨(i, j), h⟩ else 0) → (o (d, u) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = cT (sigR R σ) N * Matrix.diagonal (fun i => ((d i : R) ⊗ₜ[F] (1 : E) : R ⊗[F] E)) * N := by
  first | exact @GlobalTheory.CompanionTheory.SW.LDL.ldl_isOpenEmbedding | exact GlobalTheory.CompanionTheory.SW.LDL.ldl_isOpenEmbedding | (intros; apply GlobalTheory.CompanionTheory.SW.LDL.ldl_isOpenEmbedding <;> assumption)
