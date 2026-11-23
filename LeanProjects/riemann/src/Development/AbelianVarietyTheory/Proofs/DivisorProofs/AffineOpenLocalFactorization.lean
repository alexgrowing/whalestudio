import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitObj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem affine_factor_basicOpen_affineOpen :
    ∀ (M : Scheme.{0}) (W : M.Opens) (hW : IsAffineOpen W) (R : Type) [CommRing R] (b : Sp R ⟶ M) (p : PrimeSpectrum R),
    b p ∈ W → ∃ (f : R) (g : Γ(M, W) →+* Localization.Away f), f ∉ p.asIdeal ∧
      spMap g ≫ hW.fromSpec = spMap (algebraMap R (Localization.Away f)) ≫ b := by
  intro M W hW R _ b p hp
  have hopen : IsOpen (X := PrimeSpectrum R) (b ⁻¹ᵁ W).carrier := (b ⁻¹ᵁ W).isOpen
  obtain ⟨_, ⟨f, rfl⟩, hpf, hsub⟩ :=
    (PrimeSpectrum.isTopologicalBasis_basic_opens (R := R)).exists_subset_of_mem_open
      (a := p) (show p ∈ (b ⁻¹ᵁ W).carrier from hp) hopen
  have H : Set.range (spMap (algebraMap R (Localization.Away f)) ≫ b) ⊆ Set.range hW.fromSpec := by
    rw [IsAffineOpen.range_fromSpec]
    rintro _ ⟨x, rfl⟩
    have hx : (spMap (algebraMap R (Localization.Away f))) x ∈ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) := by
      rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away f) f]
      exact ⟨x, rfl⟩
    exact hsub hx
  let h := IsOpenImmersion.lift hW.fromSpec _ H
  refine ⟨f, (Spec.preimage h).hom, hpf, ?_⟩
  have e : spMap (Spec.preimage h).hom = h := by
    simp [spMap, Spec.map_preimage]
  rw [e]
  exact IsOpenImmersion.lift_fac _ _ _

end GlobalTheory
