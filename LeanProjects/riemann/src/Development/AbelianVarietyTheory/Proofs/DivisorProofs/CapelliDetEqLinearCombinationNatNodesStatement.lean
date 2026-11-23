import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapelliDetEqLinearCombinationNatNodes
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QdetPolyMapMonic
open NumberField GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.capelliDet_eq_linearCombination_nat_nodes : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (b : ℕ) (τ : E →+* ℂ) (u : ℂ), ∃ w : Fin (b + 1) → ℂ, cap (a := b) τ u = ∑ j : Fin (b + 1), w j • cap (a := b) τ ((j : ℕ) : ℂ) := by
  first | exact @GlobalTheory.CuspRep.cap_eq_sum_nodes | exact GlobalTheory.CuspRep.cap_eq_sum_nodes | (intros; apply GlobalTheory.CuspRep.cap_eq_sum_nodes <;> assumption)
