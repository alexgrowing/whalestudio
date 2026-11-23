import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckePhiFourierTransformZeroEq
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckePhiFourierTransform_zero_eq : ∀ (σ : ℂ) (y : ℝ), y ≠ 0 → GlobalTheory.HeckeTwo.hTrans σ 0 y = GlobalTheory.HeckeTwo.cConst σ * ((|y| : ℝ) : ℂ) ^ (-1 - 2 * σ) := by
  first | exact @GlobalTheory.HeckeTwo.hTrans_zero_eq | exact GlobalTheory.HeckeTwo.hTrans_zero_eq | (intros; apply GlobalTheory.HeckeTwo.hTrans_zero_eq <;> assumption)
