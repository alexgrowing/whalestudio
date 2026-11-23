import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantBilinearNontrivialCharacter
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubMemTwistSpan
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariant_bilinear_nontrivial_character : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ) (ν : kˣ →* ℂˣ) (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → GlobalTheory.SmGL.IsUnitaryChar ν → ν ≠ 1 →
    ∀ (Bf : GlobalTheory.FullRankCoinv.fullRk k n d →ₗ[ℂ] GlobalTheory.FullRankCoinv.fullRk k n d →ₗ⋆[ℂ] ℂ) (hG : ∀ (g : GL (Fin n) k) (Ψ₁ Ψ₁' Ψ₂ : GlobalTheory.FullRankCoinv.fullRk k n d), Ψ₁'.1 = GlobalTheory.FullRankCoinv.lact ν g Ψ₁.1 →
        Bf Ψ₁' Ψ₂ = Bf Ψ₁ Ψ₂)
    (hH : ∀ h : GL (Fin d) k, ∃ m : ℝ, 0 < m ∧ ∀ Ψ₁ Ψ₁' Ψ₂ Ψ₂' : GlobalTheory.FullRankCoinv.fullRk k n d,
        Ψ₁'.1 = (fun Y => Ψ₁.1 (Y * h.1)) → Ψ₂'.1 = (fun Y => Ψ₂.1 (Y * h.1)) → (m : ℂ) * Bf Ψ₁' Ψ₂' = Bf Ψ₁ Ψ₂)
    (i₀ : Fin n) (j₀ : Fin d) (Y₁ Y₂ : Matrix (Fin n) (Fin d) k),
    (∀ i j, ValuativeRel.valuation k (Y₁ i j) ≤ 1) → (∀ j, Y₁ i₀ j = if j = j₀ then 1 else 0) →
    (∀ i, i ≠ i₀ → Y₁ i j₀ = 0) → (∀ i, Y₂ i j₀ = 0) →
    (∃ S : Matrix (Fin d) (Fin n) k, (∀ j i, ValuativeRel.valuation k (S j i) ≤ 1) ∧ (∀ i, S j₀ i = 0) ∧ Y₂ * S = 1) →
    ∀ Z₁ ∈ GlobalTheory.RankCoinv.box ϖ Y₁ (fun _ => 1), ∀ Z₂ ∈ GlobalTheory.RankCoinv.box ϖ Y₂ (fun _ => 1), ∀ N : ℕ, 1 ≤ N →
      ∀ Ψ₁ Ψ₂ : GlobalTheory.FullRankCoinv.fullRk k n d, Ψ₁.1 = GlobalTheory.RankCoinv.boxFn ϖ Z₁ (fun _ => N) →
        Ψ₂.1 = GlobalTheory.RankCoinv.boxFn ϖ Z₂ (fun _ => N) → Bf Ψ₁ Ψ₂ = 0 := by
  first | exact @GlobalTheory.NormalCore.normal_core | exact GlobalTheory.NormalCore.normal_core | (intros; apply GlobalTheory.NormalCore.normal_core <;> assumption)
