import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefSpecMap
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_algHom_tensorInt_of_ringHom (R₀ : Type) {A S : Type} [CommRing R₀] [CommRing A] [CommRing S]
    [Algebra R₀ S] (ψ : A →+* S) :
    ∃ g : R₀ ⊗[ℤ] A →ₐ[R₀] S, ∀ a, g (1 ⊗ₜ[ℤ] a) = ψ a :=
  ⟨Algebra.TensorProduct.lift (Algebra.ofId R₀ S) ψ.toIntAlgHom (fun _ _ => Commute.all _ _),
    fun a => by simp⟩

theorem exists_away_factor_coefSpecMap (M : Scheme.{0}) (R₀ R : Type) [CommRing R₀] [CommRing R] [Algebra R₀ R] (b : Sp R ⟶ M)
    (W : M.Opens) (hW : IsAffineOpen W) (x : Sp R) (hx : b x ∈ W) :
    ∃ (f : R) (_ : f ∉ x.asIdeal) (g : R₀ ⊗[ℤ] Γ(M, W) →ₐ[R₀] Localization.Away f),
      spMap (g : R₀ ⊗[ℤ] Γ(M, W) →+* Localization.Away f) ≫ coefSpecMap hW R₀ =
        spMap (algebraMap R (Localization.Away f)) ≫ b := by
  have ho : IsOpen (X := PrimeSpectrum R) (b ⁻¹ᵁ W).carrier := (b ⁻¹ᵁ W).isOpen
  obtain ⟨_, ⟨f, rfl⟩, hxf, hle⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open (a := x) hx ho
  have hrange : Set.range (spMap (algebraMap R (Localization.Away f)) ≫ b) ⊆ Set.range hW.fromSpec := by
    rw [hW.range_fromSpec]
    rintro _ ⟨y, rfl⟩
    have hy : PrimeSpectrum.comap (algebraMap R (Localization.Away f)) y ∈
        (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) := by
      rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away f) f]
      exact ⟨y, rfl⟩
    exact hle hy
  let l := IsOpenImmersion.lift hW.fromSpec _ hrange
  have hl : l ≫ hW.fromSpec = _ := IsOpenImmersion.lift_fac _ _ _
  let ψ : Γ(M, W) →+* Localization.Away f := (Spec.preimage l).hom
  have hψ : spMap ψ = l := Spec.map_preimage l
  obtain ⟨g, hg⟩ := exists_algHom_tensorInt_of_ringHom R₀ ψ
  refine ⟨f, hxf, g, ?_⟩
  rw [← hl, ← hψ, coefSpecMap, ← Category.assoc]
  congr 1
  rw [← Spec.map_comp]
  congr 1
  ext a
  exact hg a

end GlobalTheory
