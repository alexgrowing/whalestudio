import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactPiUpperHalfPlaneImBounds
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnHeckeEisensteinFourierTerm
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_im_bounds_of_isCompact_upperHalfPlane : ∀ (ι : Type) [Fintype ι] (L : Set (ι → ℂ)), IsCompact L → (∀ z ∈ L, ∀ i, 0 < (z i).im) →
    ∃ c c' : ℝ, 0 < c ∧ ∀ z ∈ L, ∀ i, c ≤ (z i).im ∧ (z i).im ≤ c' := by
  first | exact @GlobalTheory.isCompact_pi_upperHalfPlane_im_bounds | exact GlobalTheory.isCompact_pi_upperHalfPlane_im_bounds | (intros; apply GlobalTheory.isCompact_pi_upperHalfPlane_im_bounds <;> assumption)
