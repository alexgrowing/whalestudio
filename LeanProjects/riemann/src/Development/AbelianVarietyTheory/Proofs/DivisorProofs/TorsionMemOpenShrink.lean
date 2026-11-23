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

theorem torsMap_left_apply {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {N : ℕ}
    {B C : Type} [CommRing B] [Algebra R B] [CommRing C] [Algebra R C] (φ : B →ₐ[R] C) (z : Tors G N B)
    (x : PrimeSpectrum C) :
    (torsMap φ z).1.left x = z.1.left (PrimeSpectrum.comap (φ : B →+* C) x) := rfl

theorem torsion_mem_open_shrink : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (N : ℕ) (B : Type) [CommRing B] [Algebra R B], ∀ (z : Tors G N B) (W : G.left.Opens) (P : PrimeSpectrum B), Set.range (torsMap (IsScalarTower.toAlgHom R B P.asIdeal.ResidueField) z).1.left ⊆ W → ∃ f : B, f ∉ P.asIdeal ∧ ∀ g : B, f ∣ g → Set.range (torsMap (IsScalarTower.toAlgHom R B (Localization.Away g)) z).1.left ⊆ W := by
  intro R _ G _ _ N B _ _ z W P h
  have hP : z.1.left P ∈ W := by
    have := h ⟨(⊥ : PrimeSpectrum P.asIdeal.ResidueField), rfl⟩
    rw [torsMap_left_apply] at this
    have e : PrimeSpectrum.comap
        ((IsScalarTower.toAlgHom R B P.asIdeal.ResidueField : B →ₐ[R] _) : B →+* P.asIdeal.ResidueField) ⊥ = P := by
      ext1
      exact Ideal.ker_algebraMap_residueField P.asIdeal
    rwa [e] at this
  have hopen : IsOpen {x : PrimeSpectrum B | z.1.left x ∈ W} := (z.1.left ⁻¹ᵁ W).isOpen
  obtain ⟨_, ⟨f, rfl⟩, hf, hsub⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (show P ∈ {x : PrimeSpectrum B | z.1.left x ∈ W} from hP) hopen
  refine ⟨f, hf, ?_⟩
  rintro g ⟨c, rfl⟩ _ ⟨x, rfl⟩
  have hx : PrimeSpectrum.comap (algebraMap B (Localization.Away (f * c))) x ∈
      (PrimeSpectrum.basicOpen (f * c) : Set (PrimeSpectrum B)) := by
    rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away (f * c)) (f * c)]
    exact ⟨x, rfl⟩
  exact hsub (PrimeSpectrum.basicOpen_mul_le_left f c hx)

end GlobalTheory.GroupBplus.Aff
