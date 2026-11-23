import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerEmbeddingInjective
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsTrDataGaussianIntOne
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tower_embedding_injective : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω) (n : ℕ), 1 ≤ n → ∀ ι : On p n →ₐ[O0 p] Ω, IsEmb T n ι → Function.Injective ι := by
  first | exact @GlobalTheory.K5.EmbInj.emb_injective | exact GlobalTheory.K5.EmbInj.emb_injective | (intros; apply GlobalTheory.K5.EmbInj.emb_injective <;> assumption)
