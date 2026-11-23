import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenDecompositionTraceMultiple
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigen_decomposition_trace_multiple : ∀ (C : Type) [Field C] [CharZero C] (O : Type) [CommRing O] [Algebra O C] (Λ : Type) [CommRing Λ] (h h' m : ℕ) (ρ : Λ → Matrix (Fin h) (Fin h) O) (ρ' : Λ → Matrix (Fin h') (Fin h') O), Function.Injective (algebraMap O C) → iSupIndep (fun σ : Λ →+* O => eig C ρ σ) → (⨆ σ : Λ →+* O, eig C ρ σ) = ⊤ → iSupIndep (fun σ : Λ →+* O => eig C ρ' σ) → (⨆ σ : Λ →+* O, eig C ρ' σ) = ⊤ → (∀ a, (ρ a).trace = (m : O) * (ρ' a).trace) → ∀ τ : Λ →+* O, Module.finrank C (eig C ρ τ) = m * Module.finrank C (eig C ρ' τ) := by
  first | exact @GlobalTheory.finrank_eig_eq_mul_of_trace_eq_mul | exact GlobalTheory.finrank_eig_eq_mul_of_trace_eq_mul | (intros; apply GlobalTheory.finrank_eig_eq_mul_of_trace_eq_mul <;> assumption)
