import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankBoxSeparation
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubMemTwistSpan
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.full_rank_box_separation : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ) (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (Bf : GlobalTheory.FullRankCoinv.fullRk k n d →ₗ[ℂ] GlobalTheory.FullRankCoinv.fullRk k n d →ₗ⋆[ℂ] ℂ),
    (∀ Y₁ Y₂ : Matrix (Fin n) (Fin d) k, Y₁.rank = n → Y₂.rank = n → (∀ a : GL (Fin n) k, Y₁ ≠ a.1 * Y₂) →
      ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ Z₁ ∈ GlobalTheory.RankCoinv.box ϖ Y₁ (fun _ => N₀), ∀ Z₂ ∈ GlobalTheory.RankCoinv.box ϖ Y₂ (fun _ => N₀),
      ∀ Ψ₁ Ψ₂ : GlobalTheory.FullRankCoinv.fullRk k n d, Ψ₁.1 = GlobalTheory.RankCoinv.boxFn ϖ Z₁ (fun _ => N) →
        Ψ₂.1 = GlobalTheory.RankCoinv.boxFn ϖ Z₂ (fun _ => N) → Bf Ψ₁ Ψ₂ = 0) →
    ∀ Ψ₁ Ψ₂ : GlobalTheory.FullRankCoinv.fullRk k n d,
      (∀ (Y₁ Y₂ : Matrix (Fin n) (Fin d) k), Ψ₁.1 Y₁ ≠ 0 → Ψ₂.1 Y₂ ≠ 0 → ∀ a : GL (Fin n) k, Y₁ ≠ a.1 * Y₂) →
      Bf Ψ₁ Ψ₂ = 0 := by
  first | exact @GlobalTheory.RankCoinv.OffDiagAssemble.bf_eq_zero_of_local | exact GlobalTheory.RankCoinv.OffDiagAssemble.bf_eq_zero_of_local | (intros; apply GlobalTheory.RankCoinv.OffDiagAssemble.bf_eq_zero_of_local <;> assumption)
