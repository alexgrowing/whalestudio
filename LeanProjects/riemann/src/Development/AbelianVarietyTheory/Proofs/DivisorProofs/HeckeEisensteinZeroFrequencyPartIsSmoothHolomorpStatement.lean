import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeEisensteinZeroFrequencyPartIsSmoothHolomorphic
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeEisensteinZeroFrequencyPart_isSmoothHolomorphic : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (Zb R : ℂ → ℂ), Differentiable ℂ R → (∀ s : ℂ, s ≠ 1 → Zb s = R s / (s - 1)) → GlobalTheory.HeckeTwo.IsGood (GlobalTheory.HeckeTwo.bZero Zb 𝔞 𝔟) := by
  first | exact @GlobalTheory.HeckeTwo.bZero_isGood | exact GlobalTheory.HeckeTwo.bZero_isGood | (intros; apply GlobalTheory.HeckeTwo.bZero_isGood <;> assumption)
