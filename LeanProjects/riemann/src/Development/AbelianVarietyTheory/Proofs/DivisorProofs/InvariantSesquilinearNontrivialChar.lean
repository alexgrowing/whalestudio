import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubMemTwistSpan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantBilinearNontrivialCharacterStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankNormalFormValuationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantBilinearDoubleCosetStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankBoxSeparationStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.OffDiagVanish

theorem offDiag_vanish : GlobalTheory.ThK.KP → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n d : ℕ) (ν : kˣ →* ℂˣ), n < d → GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsUnitaryChar ν → ν ≠ 1 →
    ∀ Bf : GlobalTheory.FullRankCoinv.fullRk k n d →ₗ[ℂ] GlobalTheory.FullRankCoinv.fullRk k n d →ₗ⋆[ℂ] ℂ,
      (∀ (g : GL (Fin n) k) (Ψ₁ Ψ₁' Ψ₂ : GlobalTheory.FullRankCoinv.fullRk k n d), Ψ₁'.1 = GlobalTheory.FullRankCoinv.lact ν g Ψ₁.1 →
        Bf Ψ₁' Ψ₂ = Bf Ψ₁ Ψ₂) →
      (∀ h : GL (Fin d) k, ∃ m : ℝ, 0 < m ∧ ∀ Ψ₁ Ψ₁' Ψ₂ Ψ₂' : GlobalTheory.FullRankCoinv.fullRk k n d,
        Ψ₁'.1 = (fun Y => Ψ₁.1 (Y * h.1)) → Ψ₂'.1 = (fun Y => Ψ₂.1 (Y * h.1)) → (m : ℂ) * Bf Ψ₁' Ψ₂' = Bf Ψ₁ Ψ₂) →
      (∀ Ψ₁ Ψ₂ : GlobalTheory.FullRankCoinv.fullRk k n d,
        (∀ (Y₁ Y₂ : Matrix (Fin n) (Fin d) k), Ψ₁.1 Y₁ ≠ 0 → Ψ₂.1 Y₂ ≠ 0 → ∀ a : GL (Fin n) k, Y₁ ≠ a.1 * Y₂) →
        Bf Ψ₁ Ψ₂ = 0) := by
  intro _ k _ _ _ _ n d ν _ _ hU hν Bf hG hH
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.SplitFlip.exists_isUnif (k := k)
  refine GlobalTheory.T.full_rank_box_separation k n d ϖ hϖ Bf ?_
  intro Y₁ Y₂ h₁ h₂ hD
  obtain ⟨i₀, j₀, g, h, hint, hrow, hcol, hcol2, hS⟩ := GlobalTheory.T.full_rank_normal_form_valuation k n d Y₁ Y₂ h₁ h₂ hD
  exact GlobalTheory.T.invariant_bilinear_double_coset k n d ν ϖ hϖ Bf hG hH Y₁ Y₂ g h
    (GlobalTheory.T.invariant_bilinear_nontrivial_character k n d ν ϖ hϖ hU hν Bf hG hH i₀ j₀ _ _ hint hrow hcol hcol2 hS)

end GlobalTheory.OffDiagVanish
