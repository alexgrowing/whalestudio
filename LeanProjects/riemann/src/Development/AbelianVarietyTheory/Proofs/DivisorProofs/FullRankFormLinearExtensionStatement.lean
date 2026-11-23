import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankFormLinearExtension
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fullRank_form_linear_extension : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ)
    (F : (Matrix (Fin n) (Fin d) k → ℂ) → Matrix (Fin n) (Fin d) k → ℂ)
    (Bf : GlobalTheory.FullRankCoinv.fullRk k n d →ₗ[ℂ] GlobalTheory.FullRankCoinv.fullRk k n d →ₗ⋆[ℂ] ℂ),
    (∀ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, ∀ Ψ' ∈ GlobalTheory.FullRankCoinv.fullRk k n d, ∀ c : ℂ, F (c • Ψ + Ψ') = c • F Ψ + F Ψ') →
    (∀ Ψ₁ Ψ₂ : GlobalTheory.FullRankCoinv.fullRk k n d, (∀ Y, Ψ₂.1 Y ≠ 0 → F Ψ₁.1 Y = 0) → Bf Ψ₁ Ψ₂ = 0) →
    ∃ Λ : (Matrix (Fin n) (Fin d) k → ℂ) →ₗ[ℂ] ℂ, ∀ Ψ₁ Ψ₂ : GlobalTheory.FullRankCoinv.fullRk k n d,
      Bf Ψ₁ Ψ₂ = Λ (fun Y => F Ψ₁.1 Y * (starRingEnd ℂ) (Ψ₂.1 Y)) := by
  first | exact @GlobalTheory.FullRankLocalForm.formP | exact GlobalTheory.FullRankLocalForm.formP | (intros; apply GlobalTheory.FullRankLocalForm.formP <;> assumption)
