import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrRepEigenspacesSpanTop
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvr_rep_eigenspaces_span_top : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ] (h : ℕ) (ρ : Λ →+* Matrix (Fin h) (Fin h) O), (⨆ σ : Λ →+* O, eig C (⇑ρ) σ) = ⊤ := by
  first | exact @GlobalTheory.eigenspaces_span_of_integral_action | exact GlobalTheory.eigenspaces_span_of_integral_action | (intros; apply GlobalTheory.eigenspaces_span_of_integral_action <;> assumption)
