import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalUniformizerBoxTransform
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledBoxRadiiAtEntry
open ValuativeRel Matrix GlobalTheory.SplitFlip GlobalTheory.FullRankCoinv GlobalTheory.RankCoinv GlobalTheory.NormalCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagonal_uniformizer_box_transform : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ) (i₀ : Fin n) (j₀ : Fin d) (ϖ : kˣ) (p₁ p₂ : Matrix (Fin n) (Fin d) k) (N : ℕ), 1 ≤ N → (∀ j, p₁ i₀ j = if j = j₀ then 1 else 0) → (∀ i, i ≠ i₀ → p₁ i j₀ = 0) → (∀ i, p₂ i j₀ = 0) → {Y : Matrix (Fin n) (Fin d) k | ((dgl i₀ ϖ).1)ᵀ * Y * (dgl j₀ ϖ⁻¹).1 ∈ box ϖ p₁ (fun _ => N)} = ebox ϖ p₁ (scaledBoxRadiiAtEntry i₀ j₀ N) ∧ {Y : Matrix (Fin n) (Fin d) k | Y * (dgl j₀ ϖ⁻¹).1 ∈ box ϖ p₂ (fun _ => N)} = ebox ϖ p₂ (baseCellRadiiAtColumn j₀ N) := by
  first | exact @GlobalTheory.ScaleBoxPre.preimage_box_scale_eq_ebox | exact GlobalTheory.ScaleBoxPre.preimage_box_scale_eq_ebox | (intros; apply GlobalTheory.ScaleBoxPre.preimage_box_scale_eq_ebox <;> assumption)
