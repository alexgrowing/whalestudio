import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenProjectionQuotientLattice
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigen_projection_quotient_lattice : ∀ (C : Type) [Field C] (O : Type) [CommRing O] [Algebra O C] (Λ : Type) [CommRing Λ] (h : ℕ) (ρ : Λ → Matrix (Fin h) (Fin h) O) (τ : Λ →+* O), iSupIndep (fun σ : Λ →+* O => eig C ρ σ) → (⨆ σ : Λ →+* O, eig C ρ σ) = ⊤ → ∃ π : (Fin h → C) →ₗ[C] eig C ρ τ, (∀ x : eig C ρ τ, π x = x) ∧ (∀ (z : Fin h → C) (x : eig C ρ τ), (z - (x : Fin h → C) ∈ ⨆ σ : {σ : Λ →+* O // σ ≠ τ}, eig C ρ σ.1) ↔ x = π z) ∧ quotLattice C ρ τ = Set.range (fun t : Fin h → O => π (fun i => algebraMap O C (t i))) := by
  first | exact @GlobalTheory.eig_projection_quotLattice | exact GlobalTheory.eig_projection_quotLattice | (intros; apply GlobalTheory.eig_projection_quotLattice <;> assumption)
