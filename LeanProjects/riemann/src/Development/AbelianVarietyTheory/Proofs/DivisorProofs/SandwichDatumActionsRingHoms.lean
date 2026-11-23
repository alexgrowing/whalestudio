import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory.Proof.sandwich_datum_actions_ring_homs

theorem actions_ringHom : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (ε : PreTilt O p) (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (h : ℕ) (D : Datum ε h Λ), (∃ ρ : Λ →+* Matrix (Fin h) (Fin h) O, ⇑ρ = actT D) ∧ (∃ ρ : Λ →+* Matrix (Fin h) (Fin h) O, ⇑ρ = actH D) := by
  intro p _ O _ _ _ ε Λ _ _ h D
  exact ⟨⟨(RingHom.mapMatrix (padicToO p O)).comp (D.ρT : Λ →+* Matrix (Fin h) (Fin h) ℤ_[p]), rfl⟩,
    ⟨(RingHom.mapMatrix (WittVector.fontaineTheta O p)).comp D.ρM, rfl⟩⟩

end GlobalTheory.Proof.sandwich_datum_actions_ring_homs
