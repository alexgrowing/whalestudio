import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtHeckeTermDecayIntegrand
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnHeckeEisensteinFourierTerm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntZEqFourier
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.TermDecay
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDerivAt_heckeTermDecayIntegrand : ∀ (σ : ℂ) (a : ℤ) (b m : ℕ) (y : ℝ), y ≠ 0 → ∀ t : ℝ,
    HasDerivAt (qZ σ a b m y) (-(a : ℂ) * qZ σ (a + 1) b m y t
      + 2 * (-σ - (b : ℂ)) * (qZ σ (a - 1) (b + 1) m y t - I * qZ σ a (b + 1) (m + 1) y t)) t := by
  first | exact @GlobalTheory.HeckeTwo.TermDecay.hasDerivAt_qZ | exact GlobalTheory.HeckeTwo.TermDecay.hasDerivAt_qZ | (intros; apply GlobalTheory.HeckeTwo.TermDecay.hasDerivAt_qZ <;> assumption)
