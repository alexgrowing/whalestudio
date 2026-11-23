import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicRingHomUniqueAdicComplete
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padic_ring_hom_unique_adic_complete : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], (∀ f : ℤ_[p] →+* O, f = padicToO p O) ∧ ∀ (h : ℕ) (f : ℤ_[p] →+* Matrix (Fin h) (Fin h) O) (c : ℤ_[p]), f c = padicToO p O c • (1 : Matrix (Fin h) (Fin h) O) := by
  first | exact @GlobalTheory.padic_ringHom_unique | exact GlobalTheory.padic_ringHom_unique | (intros; apply GlobalTheory.padic_ringHom_unique <;> assumption)
