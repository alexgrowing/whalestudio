import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepTraceEqMulAlgebraTraceDvr
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rep_trace_eq_mul_algebra_trace_dvr : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ] (N h : ℕ) (ρ : Λ →+* Matrix (Fin h) (Fin h) O), (∀ a, (ρ a).trace = (N : O) * padicToO p O (Algebra.trace ℤ_[p] Λ a)) → ∀ τ : Λ →+* O, Module.finrank C (eig C (⇑ρ) τ) = N := by
  first | exact @GlobalTheory.finrank_eig_of_trace_eq_mul_trace | exact GlobalTheory.finrank_eig_of_trace_eq_mul_trace | (intros; apply GlobalTheory.finrank_eig_of_trace_eq_mul_trace <;> assumption)
