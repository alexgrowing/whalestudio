import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRadiusMoebiusPerturbationUpperHalfPlane
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_radius_moebius_perturbation_upperHalfPlane : ∀ (τ c t : ℂ), 0 < τ.im → ∃ r : ℝ, 0 < r ∧ ∀ z : ℂ, ‖z‖ < r → 1 / 2 ≤ ‖1 + z * c‖ ∧ τ.im / 2 ≤ (τ + t * z / (1 + z * c)).im := by
  first | exact @GlobalTheory.HilbFam.exists_radius_moebius_perturbation | exact GlobalTheory.HilbFam.exists_radius_moebius_perturbation | (intros; apply GlobalTheory.HilbFam.exists_radius_moebius_perturbation <;> assumption)
