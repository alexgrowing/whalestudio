import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

theorem spMap_factor_residueField_of_closedPoint (R : Type) [CommRing R] [IsLocalRing R] (Ω : Type) [Field Ω]
    (g : Sp Ω ⟶ Sp R) (hg : ∀ w, g w = closedPoint R) :
    ∃ κ : ResidueField R →+* Ω, g = spMap (κ.comp (residue R)) := by
  set φ : R →+* Ω := (Spec.preimage g).hom with hφ
  have hgφ : g = spMap φ := by
    simp only [spMap, hφ, CommRingCat.ofHom_hom, Spec.map_preimage]
  have hker : ∀ x ∈ maximalIdeal R, φ x = 0 := by
    intro x hx
    let w : Sp Ω := ⟨⊥, Ideal.isPrime_bot⟩
    have h1 := hg w
    rw [hgφ] at h1
    have h2 : (spMap φ w).asIdeal = Ideal.comap φ ⊥ := rfl
    rw [h1, closedPoint] at h2
    have : x ∈ Ideal.comap φ ⊥ := h2 ▸ hx
    simpa using this
  refine ⟨Ideal.Quotient.lift (maximalIdeal R) φ hker, ?_⟩
  rw [hgφ]
  congr 2

end GlobalTheory.Mum
