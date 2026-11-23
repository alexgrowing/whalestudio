import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OuterTensorFockOnePlaceIsoUnitaryFock
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyInvFunEquiv
open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.outerTensor_fockOnePlace_iso_unitaryFock : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (a b : ℕ) (α β : ι → ℤ), Iso (outer₂ fun τ => fockOne a b (α τ) (β τ)) (fock a b α β) := by
  first | exact @GlobalTheory.OneFunctional.FockTensor.outer₂_fockOne_iso | exact GlobalTheory.OneFunctional.FockTensor.outer₂_fockOne_iso | (intros; apply GlobalTheory.OneFunctional.FockTensor.outer₂_fockOne_iso <;> assumption)
