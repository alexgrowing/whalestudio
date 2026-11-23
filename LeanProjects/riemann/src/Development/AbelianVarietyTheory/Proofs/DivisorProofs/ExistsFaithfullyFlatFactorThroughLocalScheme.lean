import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem flat_stalkClosedPointTo {S : Scheme.{0}} {R : CommRingCat.{0}} [IsLocalRing R]
    (ξ : Spec R ⟶ S) [Flat ξ] : (Scheme.stalkClosedPointTo ξ).hom.Flat := by
  unfold Scheme.stalkClosedPointTo
  rw [CommRingCat.hom_comp]
  exact (Flat.stalkMap ξ _).comp
    (RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso (stalkClosedPointIso R).hom))

theorem exists_faithfullyFlat_factor_localScheme :
    ∀ (S : Scheme.{0}) (R₁ : Type) [CommRing R₁] [IsLocalRing R₁] (ξ : Sp R₁ ⟶ S) (x : S),
      ξ (closedPoint R₁) = x → Flat ξ → ∃ ξ' : Sp R₁ ⟶ Spec (S.presheaf.stalk x),
        ξ' ≫ S.fromSpecStalk x = ξ ∧ Flat ξ' ∧ Surjective ξ' ∧ QuasiCompact ξ' := by
  intro S R₁ _ _ ξ x hx hf
  subst hx
  have hflat := flat_stalkClosedPointTo (R := CommRingCat.of R₁) ξ
  refine ⟨Spec.map (Scheme.stalkClosedPointTo (R := CommRingCat.of R₁) ξ),
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of R₁) ξ,
    (HasRingHomProperty.Spec_iff (P := @Flat)).2 hflat, ⟨?_⟩, inferInstance⟩
  set φ := (Scheme.stalkClosedPointTo (R := CommRingCat.of R₁) ξ).hom with hφ
  have hl : IsLocalHom φ := by rw [hφ]; infer_instance
  letI := φ.toAlgebra
  have : Module.Flat (S.presheaf.stalk (ξ (closedPoint R₁))) R₁ := hflat
  have : IsLocalHom (algebraMap (S.presheaf.stalk (ξ (closedPoint R₁))) R₁) := hl
  have := Module.FaithfullyFlat.of_flat_of_isLocalHom
    (A := S.presheaf.stalk (ξ (closedPoint R₁))) (B := R₁)
  exact PrimeSpectrum.comap_surjective_of_faithfullyFlat
    (A := S.presheaf.stalk (ξ (closedPoint R₁))) (B := R₁)

end GlobalTheory.Desc
