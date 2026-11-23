import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantsMonomialApproximation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerEquivLocPart
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbit_sum_local_parts : ∀ (G : Type) [Group G] (H K : Subgroup G) (F : G ⧸ K → ℂ), (∀ h : H, ∀ x : G ⧸ K, F (h • x) = F x) →
    ∑ᶠ q : DoubleCoset.Quotient (H : Set G) (K : Set G),
        (1 / (Nat.card (GlobalTheory.LKLoc.locPart H K (Quotient.out q)) : ℂ)) * F (QuotientGroup.mk (Quotient.out q)) =
      ∑ᶠ a : MulAction.orbitRel.Quotient H (G ⧸ K),
        (1 / (Nat.card (MulAction.stabilizer H (Quotient.out a)) : ℂ)) * F (Quotient.out a) := by
  first | exact @GlobalTheory.FinTrace.sum_doubleCoset_eq_sum_orbit | exact GlobalTheory.FinTrace.sum_doubleCoset_eq_sum_orbit | (intros; apply GlobalTheory.FinTrace.sum_doubleCoset_eq_sum_orbit <;> assumption)
