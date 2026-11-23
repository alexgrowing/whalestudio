import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiDeterminantEigenProperty
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDetEltOne
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psi_determinant_eigen_property : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ (ψ : RL p O Λ →+* RL p O Λ), IsPsi ψ → ∀ (N : ℕ) (Δ Δ' : RL p O Λ) (a : (Λ →+* O) → ℕ) (c : (Λ →+* O) → C) (c' : (Λ →+* O) → C), IsDetElt ε ψ N Δ → IsDetElt ε ψ N Δ' → HasOrders C ε N Δ a c → HasOrders C ε N Δ' a c' → ∀ τ, v (c τ) = v (c' τ) := by
  first | exact @GlobalTheory.DetInv.lead_valuation_eq | exact GlobalTheory.DetInv.lead_valuation_eq | (intros; apply GlobalTheory.DetInv.lead_valuation_eq <;> assumption)
