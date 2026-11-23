import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualWeylInvariantPairing
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSystemOf
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame GlobalTheory.FrameAut
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_weyl_invariant_pairing : ∀ (n : ℕ) (ν : Fin n → ℕ), ∃ b : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] ℂ, (∀ u ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ n n ν, u ≠ 0 → ∃ v ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ n n ν, b v u ≠ 0) ∧ ∀ (g : GL (Fin n) ℂ) v u, b (Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) (g : Matrix (Fin n) (Fin n) ℂ).transpose v) (Formalism.UG.dwAct ℂ n n g u) = b v u := by
  first | exact @GlobalTheory.FischerInvariance.fischer_dualWeyl_invariant | exact GlobalTheory.FischerInvariance.fischer_dualWeyl_invariant | (intros; apply GlobalTheory.FischerInvariance.fischer_dualWeyl_invariant <;> assumption)
