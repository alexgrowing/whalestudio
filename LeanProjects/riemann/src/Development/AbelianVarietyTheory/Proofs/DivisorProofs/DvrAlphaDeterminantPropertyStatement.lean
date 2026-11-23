import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrAlphaDeterminantProperty
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsBasisOfBot
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvr_alpha_determinant_property : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ (α : Λ), Algebra.adjoin ℤ_[p] {α} = ⊤ → ∀ (N h : ℕ), h = Module.finrank ℤ_[p] Λ * N → ∀ D : Datum ε h Λ, ∃ Φ : (Fin h → C) ≃ₗ[C] ((Λ →+* O) → Fin N → C), (∀ l z σ, Φ ((actH D l).map (algebraMap O C) *ᵥ z) σ = algebraMap O C (σ l) • Φ z σ) ∧ ∀ z, (∀ i, z i ∈ (algebraMap O C).range) ↔ ∀ i, ∃ f : Polynomial O, ∀ σ, Φ z σ i = algebraMap O C (f.eval (σ α)) := by
  first | exact @GlobalTheory.DetInv.exists_frame_model | exact GlobalTheory.DetInv.exists_frame_model | (intros; apply GlobalTheory.DetInv.exists_frame_model <;> assumption)
