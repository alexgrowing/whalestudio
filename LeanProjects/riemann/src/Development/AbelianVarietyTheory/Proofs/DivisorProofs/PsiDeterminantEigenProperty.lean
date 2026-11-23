import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDetEltOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiDeterminantOrdersPropertyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeadMulUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfElementThetaCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTensorExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FontaineAinfLocalDomainXiAdicOrderStatement
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem lead_valuation_eq : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ (ψ : RL p O Λ →+* RL p O Λ), IsPsi ψ → ∀ (N : ℕ) (Δ Δ' : RL p O Λ) (a : (Λ →+* O) → ℕ) (c : (Λ →+* O) → C) (c' : (Λ →+* O) → C), IsDetElt ε ψ N Δ → IsDetElt ε ψ N Δ' → HasOrders C ε N Δ a c → HasOrders C ε N Δ' a c' → ∀ τ, v (c τ) = v (c' τ) := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ _ _ _ _ ψ hψ N Δ Δ' a c c' hΔ hΔ' hO hO' τ
  obtain ⟨f, hf, -, hfξ, -⟩ := GlobalTheory.DetInv.theta_tensor_exists p C v O hv ε hε Λ τ
  have hξ0 : xi ε ≠ 0 := (GlobalTheory.T.fontaineAinf_localDomain_xiAdic_order p C v O hv ε hε).2.2.2.2.2.1
  have hreg : (inA (xi ε) : RL p O Λ) ∈ nonZeroDivisors (RL p O Λ) :=
    GlobalTheory.T.ainf_element_theta_compatible p C v O hv ε hε Λ (xi ε) hξ0
  obtain ⟨y, hy⟩ := GlobalTheory.T.psi_determinant_orders_property p C v O hv ε hε Λ ψ hψ N Δ Δ' a c c' hΔ hΔ' hO hO'
  obtain ⟨y', hy'⟩ := GlobalTheory.T.psi_determinant_orders_property p C v O hv ε hε Λ ψ hψ N Δ' Δ a c' c hΔ' hΔ hO' hO
  obtain ⟨-, -, hL⟩ := hO τ f hf
  obtain ⟨-, -, hL'⟩ := hO' τ f hf
  set F := (algebraMap O C).comp f
  have hL2 : Lead F (inA (xi ε)) (y * Δ) (a τ) (c' τ) := by rw [mul_comm, ← hy]; exact hL'
  have hL2' : Lead F (inA (xi ε)) (y' * Δ') (a τ) (c τ) := by rw [mul_comm, ← hy']; exact hL
  have e1 := GlobalTheory.DetInv.lead_mul_unique _ _ F _ _ _ _ _ _ hreg hL hL2
  have e2 := GlobalTheory.DetInv.lead_mul_unique _ _ F _ _ _ _ _ _ hreg hL' hL2'
  have b1 : v (F y) ≤ 1 := hv.map_le_one (f y)
  have b2 : v (F y') ≤ 1 := hv.map_le_one (f y')
  apply le_antisymm
  · rw [e2, map_mul]; exact mul_le_of_le_one_left' b2
  · rw [e1, map_mul]; exact mul_le_of_le_one_left' b1

end GlobalTheory.DetInv
