import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralRightInverseExists
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledBoxRadiiAtEntry
open ValuativeRel Matrix GlobalTheory.SplitFlip GlobalTheory.FullRankCoinv GlobalTheory.RankCoinv GlobalTheory.NormalCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_right_inverse_exists : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ) (i₀ : Fin n) (j₀ : Fin d) (ϖ : kˣ), IsUnif ϖ → ∀ (p₁ p₂ : Matrix (Fin n) (Fin d) k), (∀ i j, valuation k (p₁ i j) ≤ 1) → (∀ j, p₁ i₀ j = if j = j₀ then 1 else 0) → (∀ i, i ≠ i₀ → p₁ i j₀ = 0) → (∀ i, p₂ i j₀ = 0) → (∃ S : Matrix (Fin d) (Fin n) k, (∀ j i, valuation k (S j i) ≤ 1) ∧ (∀ i, S j₀ i = 0) ∧ p₂ * S = 1) → ∀ Z₁ ∈ box ϖ p₁ (fun _ => 1), ∀ Z₂ ∈ box ϖ p₂ (fun _ => 1), ∃ (g : GL (Fin n) k) (h : GL (Fin d) k), (∀ i j, valuation k (g.1 i j) ≤ 1) ∧ (∀ i j, valuation k ((g⁻¹).1 i j) ≤ 1) ∧ (∀ i j, valuation k (h.1 i j) ≤ 1) ∧ (∀ i j, valuation k ((h⁻¹).1 i j) ≤ 1) ∧ (∀ i j, valuation k (((g.1)ᵀ * Z₁ * h.1) i j) ≤ 1) ∧ (∀ j, ((g.1)ᵀ * Z₁ * h.1) i₀ j = if j = j₀ then 1 else 0) ∧ (∀ i, i ≠ i₀ → ((g.1)ᵀ * Z₁ * h.1) i j₀ = 0) ∧ (∀ i, (Z₂ * h.1) i j₀ = 0) ∧ ∃ S' : Matrix (Fin d) (Fin n) k, (∀ j i, valuation k (S' j i) ≤ 1) ∧ (∀ i, S' j₀ i = 0) ∧ Z₂ * h.1 * S' = 1 := by
  first | exact @GlobalTheory.NormalCore.Normalize.normalize | exact GlobalTheory.NormalCore.Normalize.normalize | (intros; apply GlobalTheory.NormalCore.Normalize.normalize <;> assumption)
