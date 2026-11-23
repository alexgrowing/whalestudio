import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SandwichDatumActionsRingHoms
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sandwich_datum_actions_ring_homs : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (ε : PreTilt O p) (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (h : ℕ) (D : Datum ε h Λ), (∃ ρ : Λ →+* Matrix (Fin h) (Fin h) O, ⇑ρ = actT D) ∧ (∃ ρ : Λ →+* Matrix (Fin h) (Fin h) O, ⇑ρ = actH D) := by
  first | exact @GlobalTheory.Proof.sandwich_datum_actions_ring_homs.actions_ringHom | exact GlobalTheory.Proof.sandwich_datum_actions_ring_homs.actions_ringHom | (intros; apply GlobalTheory.Proof.sandwich_datum_actions_ring_homs.actions_ringHom <;> assumption)
