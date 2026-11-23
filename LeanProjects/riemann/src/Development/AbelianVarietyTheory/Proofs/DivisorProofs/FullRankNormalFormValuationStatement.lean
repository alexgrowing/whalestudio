import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankNormalFormValuation
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubMemTwistSpan
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.full_rank_normal_form_valuation : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ) (Y₁ Y₂ : Matrix (Fin n) (Fin d) k), Y₁.rank = n → Y₂.rank = n →
    (∀ a : GL (Fin n) k, Y₁ ≠ a.1 * Y₂) →
    ∃ (i₀ : Fin n) (j₀ : Fin d) (g : GL (Fin n) k) (h : GL (Fin d) k),
      (∀ i j, ValuativeRel.valuation k (((g.1)ᵀ * Y₁ * h.1) i j) ≤ 1) ∧
      (∀ j, ((g.1)ᵀ * Y₁ * h.1) i₀ j = if j = j₀ then 1 else 0) ∧
      (∀ i, i ≠ i₀ → ((g.1)ᵀ * Y₁ * h.1) i j₀ = 0) ∧ (∀ i, (Y₂ * h.1) i j₀ = 0) ∧
      ∃ S : Matrix (Fin d) (Fin n) k, (∀ j i, ValuativeRel.valuation k (S j i) ≤ 1) ∧ (∀ i, S j₀ i = 0) ∧
        Y₂ * h.1 * S = 1 := by
  first | exact @GlobalTheory.FullRankPair.pair_normal_form | exact GlobalTheory.FullRankPair.pair_normal_form | (intros; apply GlobalTheory.FullRankPair.pair_normal_form <;> assumption)
