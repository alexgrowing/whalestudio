import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GroupBplus.Aff

theorem exists_away_range_torsMap_subset : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (N : ℕ) (C D : Type) [CommRing C] [Algebra R C] [CommRing D] [Algebra R D] (ψ : C →ₐ[R] D) (j : Tors G N C) (W : G.left.Opens) (P : PrimeSpectrum D), (torsMap ψ j).1.left P ∈ W → ∃ e : C, ψ e ∉ P.asIdeal ∧ Set.range (torsMap (IsScalarTower.toAlgHom R C (Localization.Away e)) j).1.left ⊆ W := by
  intro R _ G _ _ N C D _ _ _ _ ψ j W P hP
  let x : PrimeSpectrum C := PrimeSpectrum.comap (ψ : C →+* D) P
  have key : ∀ (E : Type) [CommRing E] [Algebra R E] (φ : C →ₐ[R] E) (Q : PrimeSpectrum E),
      (torsMap φ j).1.left Q = j.1.left (PrimeSpectrum.comap (φ : C →+* E) Q) := by
    intro E _ _ φ Q
    rfl
  have hx : j.1.left x ∈ W := by rw [key] at hP; exact hP
  have hopen : IsOpen (X := PrimeSpectrum C) ((fun y : PrimeSpectrum C => j.1.left y) ⁻¹' (W : Set G.left)) :=
    W.isOpen.preimage j.1.left.continuous
  obtain ⟨U, ⟨e, rfl⟩, hxe, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open (a := x) hx hopen
  refine ⟨e, hxe, ?_⟩
  rintro _ ⟨Q, rfl⟩
  have hQ : PrimeSpectrum.comap (algebraMap C (Localization.Away e)) Q ∈
      (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum C)) := by
    rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away e) e]
    exact ⟨Q, rfl⟩
  have := hsub hQ
  exact (key _ (IsScalarTower.toAlgHom R C (Localization.Away e)) Q) ▸ this

end GlobalTheory.GroupBplus.Aff
