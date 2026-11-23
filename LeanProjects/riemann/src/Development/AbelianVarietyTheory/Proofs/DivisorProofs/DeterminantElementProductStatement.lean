import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantElementProduct
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDetEltOne
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.determinant_element_product : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (C : Type) [Field C] [Algebra O C] (ε : PreTilt O p) (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (ψ : RL p O Λ →+* RL p O Λ) (N N' : ℕ) (Δ Δ' : RL p O Λ) (a a' : (Λ →+* O) → ℕ) (c c' : (Λ →+* O) → C), IsDetElt ε ψ N Δ → IsDetElt ε ψ N' Δ' → HasOrders C ε N Δ a c → HasOrders C ε N' Δ' a' c' → IsDetElt ε ψ (N + N') (Δ * Δ') ∧ HasOrders C ε (N + N') (Δ * Δ') (a + a') (c * c') := by
  first | exact @GlobalTheory.DetInv.detData_mul | exact GlobalTheory.DetInv.detData_mul | (intros; apply GlobalTheory.DetInv.detData_mul <;> assumption)
