import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralRowSectionExists
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledBoxRadiiAtEntry
open ValuativeRel Matrix GlobalTheory.SplitFlip GlobalTheory.FullRankCoinv GlobalTheory.RankCoinv GlobalTheory.NormalCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_row_section_exists : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ) (i₀ : Fin n) (j₀ : Fin d) (ϖ : kˣ), IsUnif ϖ → ∀ (p₁ p₂ : Matrix (Fin n) (Fin d) k) (N : ℕ), 1 ≤ N → (∀ i j, valuation k (p₁ i j) ≤ 1) → (∀ j, p₁ i₀ j = if j = j₀ then 1 else 0) → (∀ i, i ≠ i₀ → p₁ i j₀ = 0) → (∀ i, p₂ i j₀ = 0) → (∃ S : Matrix (Fin d) (Fin n) k, (∀ j i, valuation k (S j i) ≤ 1) ∧ (∀ i, S j₀ i = 0) ∧ p₂ * S = 1) → ∀ x₁ ∈ box ϖ p₁ (fun _ => N), ∀ x₂ ∈ box ϖ p₂ (fun _ => N), ∃ (g : GL (Fin n) k) (h : GL (Fin d) k), gdet g = 1 ∧ {Y : Matrix (Fin n) (Fin d) k | (g.1)ᵀ * Y * h.1 ∈ ebox ϖ p₁ (baseCellRadiiAtEntry i₀ j₀ N)} = ebox ϖ x₁ (baseCellRadiiAtEntry i₀ j₀ N) ∧ {Y : Matrix (Fin n) (Fin d) k | Y * h.1 ∈ ebox ϖ p₂ (baseCellRadiiAtColumn j₀ N)} = ebox ϖ x₂ (baseCellRadiiAtColumn j₀ N) := by
  first | exact @GlobalTheory.NormalCore.UnipMove.exists_unip_move | exact GlobalTheory.NormalCore.UnipMove.exists_unip_move | (intros; apply GlobalTheory.NormalCore.UnipMove.exists_unip_move <;> assumption)
