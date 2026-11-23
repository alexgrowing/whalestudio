import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryIrrepCompConjIsoDual
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyInvFunEquiv
open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryIrrep_comp_conj_iso_dual : ∀ (n : ℕ), 0 < n → ∀ lam : DomWeight n, Iso ((irr n lam).comp (conjU n) : Representation ℂ (U n) (nablaSq ℂ n lam)) (irr n lam.dual) := by
  first | exact @GlobalTheory.OneFunctional.iso_irr_comp_conjU | exact GlobalTheory.OneFunctional.iso_irr_comp_conjU | (intros; apply GlobalTheory.OneFunctional.iso_irr_comp_conjU <;> assumption)
