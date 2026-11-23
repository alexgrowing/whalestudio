import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaProductSiegelEqZeroIffLattice
import Development.AbelianVarietyTheory.Definitions.Foundations.Imports
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.oddThetaProductSiegel_eq_zero_iff_lattice : ∀ (τ : ℍ) (z : ℂ), th z τ = 0 ↔ ∃ m n : ℤ, z = (m : ℂ) * (τ : ℂ) + n := by
  first | exact @GlobalTheory.ThZero.th_eq_zero_iff | exact GlobalTheory.ThZero.th_eq_zero_iff | (intros; apply GlobalTheory.ThZero.th_eq_zero_iff <;> assumption)
