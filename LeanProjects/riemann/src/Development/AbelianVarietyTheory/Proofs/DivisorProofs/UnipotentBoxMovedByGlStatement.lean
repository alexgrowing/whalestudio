import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentBoxMovedByGl
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledBoxRadiiAtEntry
open ValuativeRel Matrix GlobalTheory.SplitFlip GlobalTheory.FullRankCoinv GlobalTheory.RankCoinv GlobalTheory.NormalCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_box_moved_by_gl : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ) (i₀ : Fin n) (j₀ : Fin d) (ϖ : kˣ), IsUnif ϖ → ∀ (p₁ p₂ : Matrix (Fin n) (Fin d) k) (N : ℕ), 1 ≤ N → (∀ j, p₁ i₀ j = if j = j₀ then 1 else 0) → (∀ i, i ≠ i₀ → p₁ i j₀ = 0) → (∀ i, p₂ i j₀ = 0) → ∀ x₁ ∈ ebox ϖ p₁ (scaledBoxRadiiAtEntry i₀ j₀ N), ∃ h : GL (Fin d) k, {Y : Matrix (Fin n) (Fin d) k | Y * h.1 ∈ ebox ϖ p₁ (baseCellRadiiAtEntry i₀ j₀ N)} = ebox ϖ x₁ (baseCellRadiiAtEntry i₀ j₀ N) ∧ {Y : Matrix (Fin n) (Fin d) k | Y * h.1 ∈ ebox ϖ p₂ (baseCellRadiiAtColumn j₀ N)} = ebox ϖ p₂ (baseCellRadiiAtColumn j₀ N) := by
  first | exact @GlobalTheory.NormalCore.ColumnMove.exists_unipotent_move | exact GlobalTheory.NormalCore.ColumnMove.exists_unipotent_move | (intros; apply GlobalTheory.NormalCore.ColumnMove.exists_unipotent_move <;> assumption)
