import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaNormUnimodularLattice
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.odd_theta_norm_unimodular_lattice : ∀ (Λ : AddSubgroup ℂ), (∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂}) → TaylorLogMetric.discr Λ = 1 → nrm1Sq Λ (sgStar Λ) ^ 2 = 2 * Real.pi ^ 2 / area Λ ∧ ∀ t, U1 Λ t (sgStar Λ) 0 ≠ 0 → nrm1Sq Λ (GL3Theta.th0 Λ t) = nrm1Sq Λ (sgStar Λ) / ‖U1 Λ t (sgStar Λ) 0‖ ^ 2 := by
  first | exact @GlobalTheory.OddThetaNorm.odd_theta_norm_sigma_star | exact GlobalTheory.OddThetaNorm.odd_theta_norm_sigma_star | (intros; apply GlobalTheory.OddThetaNorm.odd_theta_norm_sigma_star <;> assumption)
