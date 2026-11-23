import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.XiMuAssociatedOfPrimitiveRoots
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDetEltOne
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.xi_mu_associated_of_primitive_roots : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ ε' : PreTilt O p, IsPrimitiveRoot (root ε').untilt p → Associated (xi ε) (xi ε') ∧ Associated (mu ε) (mu ε') := by
  first | exact @GlobalTheory.DetInv.xi_mu_associated | exact GlobalTheory.DetInv.xi_mu_associated | (intros; apply GlobalTheory.DetInv.xi_mu_associated <;> assumption)
