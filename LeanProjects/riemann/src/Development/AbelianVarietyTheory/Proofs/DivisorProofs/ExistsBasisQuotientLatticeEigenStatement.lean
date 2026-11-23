import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisQuotientLatticeEigen
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basis_quotient_lattice_eigen : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (Λ : Type) [CommRing Λ] (h N : ℕ), v.Integers O → ∀ (ρ : Λ → Matrix (Fin h) (Fin h) O) (τ : Λ →+* O), iSupIndep (fun σ : Λ →+* O => eig C ρ σ) → (⨆ σ : Λ →+* O, eig C ρ σ) = ⊤ → Module.finrank C (eig C ρ τ) = N → ∃ b : Module.Basis (Fin N) C (eig C ρ τ), quotLattice C ρ τ = (Submodule.span O (Set.range b) : Set (eig C ρ τ)) ∧ Module.finrank C (detLine C ρ τ N) = 1 ∧ exteriorPower.ιMulti C N b ≠ 0 ∧ detLattice C ρ τ N = Submodule.span O {exteriorPower.ιMulti C N b} := by
  first | exact @GlobalTheory.eigenQuotient_basis_detLattice_eq_span_wedge | exact GlobalTheory.eigenQuotient_basis_detLattice_eq_span_wedge | (intros; apply GlobalTheory.eigenQuotient_basis_detLattice_eq_span_wedge <;> assumption)
