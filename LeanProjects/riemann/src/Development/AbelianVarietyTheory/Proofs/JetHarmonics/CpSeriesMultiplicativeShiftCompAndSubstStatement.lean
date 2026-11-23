import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpSeriesMultiplicativeShiftCompAndSubst
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cpSeriesMultiplicativeShift_comp_and_subst : ∀ (q : ℕ) [Fact q.Prime], (∀ (ζ ξ : ℂ_[q]) (f : ℂ_[q]⟦X⟧), ‖ζ - 1‖ < 1 → ‖ξ - 1‖ < 1 → Bdd f → shiftS ζ (shiftS ξ f) = shiftS (ζ * ξ) f) ∧ ∀ (ζ : ℂ_[q]) (n k : ℕ) (a : ℤ_[q]) (f : ℂ_[q]⟦X⟧), ζ ^ (q ^ n) = 1 → ‖a - (k : ℤ_[q])‖ ≤ (q : ℝ) ^ (-(n : ℤ)) → Bdd f → ‖ζ - 1‖ < 1 ∧ shiftS ζ (f.subst (mulS a : ℂ_[q]⟦X⟧)) = (shiftS (ζ ^ k) f).subst (mulS a : ℂ_[q]⟦X⟧) := by
  first | exact @GlobalTheory.MomOne.ShiftComp.main | exact GlobalTheory.MomOne.ShiftComp.main | (intros; apply GlobalTheory.MomOne.ShiftComp.main <;> assumption)
