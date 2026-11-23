import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNefSectionsAsymptotic
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNefSectionGrowth
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter
open GroundTheory.Heights₂.Heights.CoordinateConeArithVar

noncomputable section

set_option linter.unusedSectionVars false

section Coordinates

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]

theorem chartLatQ_eq_smul_one (y : (Σ k, ι k) → Ω) (a : K → ℤ) (τ : ℕ) :
    chartLatQ y a τ = chartLatQ y ((τ : ℤ) • a) 1 := by
  ext s
  show (∀ c : ∀ k, ι k, _ → _) ↔ (∀ c : ∀ k, ι k, _ → _)
  simp only [Pi.smul_apply, smul_eq_mul, Nat.cast_one, one_mul]

end Coordinates

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
