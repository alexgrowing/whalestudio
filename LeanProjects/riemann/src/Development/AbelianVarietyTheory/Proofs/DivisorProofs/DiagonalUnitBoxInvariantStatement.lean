import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalUnitBoxInvariant
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledBoxRadiiAtEntry
open ValuativeRel Matrix GlobalTheory.SplitFlip GlobalTheory.FullRankCoinv GlobalTheory.RankCoinv GlobalTheory.NormalCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagonal_unit_box_invariant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ) (i₀ : Fin n) (j₀ : Fin d) (ϖ u : kˣ) (p₁ p₂ : Matrix (Fin n) (Fin d) k) (N : ℕ), valuation k (u : k) = 1 → (∀ j, p₁ i₀ j = if j = j₀ then 1 else 0) → (∀ i, i ≠ i₀ → p₁ i j₀ = 0) → (∀ i, p₂ i j₀ = 0) → {Y : Matrix (Fin n) (Fin d) k | ((dgl i₀ u).1)ᵀ * Y * (dgl j₀ u⁻¹).1 ∈ box ϖ p₁ (fun _ => N)} = box ϖ p₁ (fun _ => N) ∧ {Y : Matrix (Fin n) (Fin d) k | Y * (dgl j₀ u⁻¹).1 ∈ box ϖ p₂ (fun _ => N)} = box ϖ p₂ (fun _ => N) := by
  first | exact @GlobalTheory.UnitScaleBox.box_unit_scale | exact GlobalTheory.UnitScaleBox.box_unit_scale | (intros; apply GlobalTheory.UnitScaleBox.box_unit_scale <;> assumption)
