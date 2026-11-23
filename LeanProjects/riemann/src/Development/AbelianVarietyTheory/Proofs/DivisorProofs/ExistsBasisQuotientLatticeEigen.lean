import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExteriorPowerBasisLatticePrincipalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisOfLatticeSpanStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpanningImageLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenProjectionQuotientLatticeStatement
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

theorem eigenQuotient_basis_detLattice_eq_span_wedge : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (Λ : Type) [CommRing Λ] (h N : ℕ), v.Integers O → ∀ (ρ : Λ → Matrix (Fin h) (Fin h) O) (τ : Λ →+* O), iSupIndep (fun σ : Λ →+* O => eig C ρ σ) → (⨆ σ : Λ →+* O, eig C ρ σ) = ⊤ → Module.finrank C (eig C ρ τ) = N → ∃ b : Module.Basis (Fin N) C (eig C ρ τ), quotLattice C ρ τ = (Submodule.span O (Set.range b) : Set (eig C ρ τ)) ∧ Module.finrank C (detLine C ρ τ N) = 1 ∧ exteriorPower.ιMulti C N b ≠ 0 ∧ detLattice C ρ τ N = Submodule.span O {exteriorPower.ιMulti C N b} := by
  intro C _ v O _ _ Λ _ h N hv ρ τ hind hsup hrank
  obtain ⟨π, hπ1, -, hq⟩ := GlobalTheory.T.eigen_projection_quotient_lattice C O Λ h ρ τ hind hsup
  have hsurj : Function.Surjective π := fun x => ⟨(x : Fin h → C), hπ1 x⟩
  obtain ⟨g, hgC, hgO⟩ := GlobalTheory.T.exists_spanning_image_lattice C O (eig C ρ τ) h π hsurj
  obtain ⟨b, hb⟩ := GlobalTheory.T.exists_basis_of_lattice_span C v O (eig C ρ τ) h N g hv hgC hrank
  have hQ : quotLattice C ρ τ = (Submodule.span O (Set.range b) : Set (eig C ρ τ)) := by
    rw [hq, hgO, hb]
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.exteriorPower_basis_lattice_principal C O (eig C ρ τ) N b
  refine ⟨b, hQ, h1, h2, ?_⟩
  unfold detLattice
  rw [hQ]
  exact h3

end GlobalTheory
