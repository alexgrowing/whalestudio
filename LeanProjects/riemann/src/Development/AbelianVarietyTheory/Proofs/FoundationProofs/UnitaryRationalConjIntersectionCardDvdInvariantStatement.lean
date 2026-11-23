import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryRationalConjIntersectionCardDvdInvariant
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryRationalConjIntersectionCard_dvd_invariant : ∀ (D : D7) (N : ℕ) (J : Subgroup (GA D N)), J ≤ intG D N → ∀ g, gam D J g ≠ 0 ∧ gam D J g ∣ 8 ^ (2 * fF D * N) * (2 * (2 * fF D * N)).factorial ∧ ∀ γ ∈ ratG D N, ∀ j ∈ J, gam D J (γ * g * j) = gam D J g := by
  first | exact @GlobalTheory.StabOrder.gam_ne_zero_dvd_invariant | exact GlobalTheory.StabOrder.gam_ne_zero_dvd_invariant | (intros; apply GlobalTheory.StabOrder.gam_ne_zero_dvd_invariant <;> assumption)
