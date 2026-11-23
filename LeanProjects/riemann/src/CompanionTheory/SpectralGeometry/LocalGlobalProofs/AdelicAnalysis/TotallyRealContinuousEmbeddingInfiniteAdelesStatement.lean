import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TotallyRealContinuousEmbeddingInfiniteAdeles
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.totally_real_continuous_embedding_infinite_adeles : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → (∃ θ : ℝ →+* InfiniteAdeleRing F, Continuous θ) ∧ ∀ θ : ℝ →+* InfiniteAdeleRing F, Continuous θ → ∀ (t : ℝ) (w : InfinitePlace F), ‖θ t w‖ = |t| := by
  first | exact @GlobalTheory.CompanionTheory.AdelicRealLine.exists_continuous_real_embedding | exact GlobalTheory.CompanionTheory.AdelicRealLine.exists_continuous_real_embedding | (intros; apply GlobalTheory.CompanionTheory.AdelicRealLine.exists_continuous_real_embedding <;> assumption)
