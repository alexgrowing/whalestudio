import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockCurvaturePeriodFormula
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtFormAdjEqNegSecondForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockModelPosFrameBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChTwoInvOfIsSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChTwoBlockDiagonalSumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChTwoImaginaryPartSymmetricZeroStatement
open Matrix Filter Topology GlobalTheory.HermFrame
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_curvature_period_formula : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] {ι : Type} [Fintype ι] {μ : ι → ℕ} {g : ℕ} {W : Set E} {w : E} (Q : ∀ τ, E → Matrix (Fin (μ τ)) (Fin g) ℂ) (Z : E → Matrix (Fin g) (Fin g) ℂ) (κ : ι → ℝ) (H : ∀ τ, E → Matrix (Fin (μ τ)) (Fin (μ τ)) ℂ), IsOpen W → w ∈ W → (∀ τ i l, DifferentiableOn ℂ (fun z => Q τ z i l) W) → (∀ i k, DifferentiableOn ℂ (fun z => Z z i k) W) → (∀ z ∈ W, (Z z).IsSymm) → (∀ z ∈ W, ((Z z).map fun c => ((c.im : ℝ) : ℂ)).PosDef) → Fintype.card (Σ τ, Fin (μ τ)) = g → LinearIndependent ℂ (fun p : Σ τ, Fin (μ τ) => Q p.1 w p.2) → (∀ τ, 0 < κ τ) → (∀ z ∈ W, (∀ τ, H τ z = ((κ τ : ℝ) : ℂ) • (Q τ z * ((Z z).map fun c => ((c.im : ℝ) : ℂ))⁻¹ * (Q τ z)ᴴ)) ∧ ∀ τ τ', τ ≠ τ' → Q τ z * ((Z z).map fun c => ((c.im : ℝ) : ℂ))⁻¹ * (Q τ' z)ᴴ = 0) → (∀ τ, MContDiffAt 2 (H τ) w ∧ IsUnit (H τ w).det) ∧ ∀ ξ₁ η₁ ξ₂ η₂ : E, ∑ τ, chTwo (H τ) w ξ₁ η₁ ξ₂ η₂ = 0 := by
  first | exact @GlobalTheory.BlockChTwoSum.sum_chTwo_blocks_eq_zero | exact GlobalTheory.BlockChTwoSum.sum_chTwo_blocks_eq_zero | (intros; apply GlobalTheory.BlockChTwoSum.sum_chTwo_blocks_eq_zero <;> assumption)
