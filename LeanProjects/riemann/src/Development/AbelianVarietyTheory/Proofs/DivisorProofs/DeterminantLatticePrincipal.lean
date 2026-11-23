import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenProjectionQuotientLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpanningImageLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExteriorPowerSpanOfLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExteriorPowerTopFinrankOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOneLatticeSpanSingletonStatement
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

theorem detLattice_eq_span_singleton : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (Λ : Type) [CommRing Λ] (h N : ℕ), v.Integers O → ∀ (ρ : Λ → Matrix (Fin h) (Fin h) O) (τ : Λ →+* O), iSupIndep (fun σ : Λ →+* O => eig C ρ σ) → (⨆ σ : Λ →+* O, eig C ρ σ) = ⊤ → Module.finrank C (eig C ρ τ) = N → Module.finrank C (detLine C ρ τ N) = 1 ∧ ∃ w : detLine C ρ τ N, w ≠ 0 ∧ detLattice C ρ τ N = Submodule.span O {w} := by
  intro C _ v O _ _ Λ _ h N hv ρ τ hind htop hN
  obtain ⟨π, hπ, -, hq⟩ := GlobalTheory.T.eigen_projection_quotient_lattice C O Λ h ρ τ hind htop
  have hsurj : Function.Surjective π := fun x => ⟨x, hπ x⟩
  obtain ⟨g, hgC, hgO⟩ := GlobalTheory.T.exists_spanning_image_lattice C O (eig C ρ τ) h π hsurj
  have hq' : quotLattice C ρ τ = (Submodule.span O (Set.range g) : Set (eig C ρ τ)) := by
    rw [hq, hgO]
  obtain ⟨hrank, s, hs⟩ := GlobalTheory.T.exteriorPower_top_finrank_one C (eig C ρ τ) h N g hgC hN
  have hspan : detLattice C ρ τ N =
      Submodule.span O (Set.range (fun s : Fin N → Fin h => exteriorPower.ιMulti C N (g ∘ s))) := by
    unfold detLattice
    rw [hq']
    exact GlobalTheory.T.exteriorPower_span_of_lattice C O (eig C ρ τ) h N g
  refine ⟨hrank, ?_⟩
  obtain ⟨w, hw, hwspan⟩ := GlobalTheory.T.rank_one_lattice_span_singleton C v O (⋀[C]^N (eig C ρ τ)) (Fin N → Fin h)
    (fun s : Fin N → Fin h => exteriorPower.ιMulti C N (g ∘ s)) hv hrank ⟨s, hs⟩
  exact ⟨w, hw, hspan.trans hwspan⟩

end GlobalTheory
