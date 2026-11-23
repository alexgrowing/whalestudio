import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicRingHomEqCanonical
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padic_ring_hom_eq_canonical : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (g : ℤ_[p] →+* O), g = padicToO p O := by
  first | exact @GlobalTheory.padicToO_unique | exact GlobalTheory.padicToO_unique | (intros; apply GlobalTheory.padicToO_unique <;> assumption)
