import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MaximalIdealMembershipOfLocal
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maximal_ideal_membership_of_local : ∀ {K : Type} [Field K] (R : Subring K) [IsLocalRing R] (P : Ideal (integralClosure R K).toSubring), P.IsMaximal → ∀ (t : (integralClosure R K).toSubring), (t : K) ∈ R → (t ∈ P ↔ ¬ ((t : K) ≠ 0 ∧ (t : K)⁻¹ ∈ R)) := by
  first | exact @GlobalTheory.CompanionTheory.IntegralClosureLocal.mem_maximal_iff_not_inv_mem | exact GlobalTheory.CompanionTheory.IntegralClosureLocal.mem_maximal_iff_not_inv_mem | (intros; apply GlobalTheory.CompanionTheory.IntegralClosureLocal.mem_maximal_iff_not_inv_mem <;> assumption)
