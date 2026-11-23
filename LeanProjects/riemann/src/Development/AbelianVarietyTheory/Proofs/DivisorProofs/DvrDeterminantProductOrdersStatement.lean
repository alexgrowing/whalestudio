import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrDeterminantProductOrders
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsBasisOfBot
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvr_determinant_product_orders : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ (a b h : ℕ) (D : Datum ε h Λ) (τ : Λ →+* O) (w : Fin a → Fin h → C) (n : Fin b → Fin h → C), IsBasisOf C (wQuot C D τ) w → IsBasisOf C (alQuot C D τ) n → ∃ x : Fin (a + b) → eig C (actT D) τ, (∀ i, (x (Fin.castAdd b i) : Fin h → C) = w i) ∧ (∀ i, alC C D (x (Fin.natAdd a i)) = n i) ∧ IsBasisOf C (eigPart C (actT D) τ ⊤) (fun i => (x i : Fin h → C)) ∧ detLattice C (actT D) τ (a + b) = Submodule.span O {exteriorPower.ιMulti C (a + b) x} := by
  first | exact @GlobalTheory.ShiftBasis.shift_basis | exact GlobalTheory.ShiftBasis.shift_basis | (intros; apply GlobalTheory.ShiftBasis.shift_basis <;> assumption)
