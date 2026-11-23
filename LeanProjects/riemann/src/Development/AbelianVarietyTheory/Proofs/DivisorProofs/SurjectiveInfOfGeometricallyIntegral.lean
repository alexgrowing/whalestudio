import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory

theorem surjective_inf_of_geometricallyIntegral :
    ∀ (Z T : Scheme.{0}) (f : Z ⟶ T) [GeometricallyIntegral f] (O O' : Z.Opens),
      Surjective (O.ι ≫ f) → Surjective (O'.ι ≫ f) → Surjective ((O ⊓ O').ι ≫ f) := by
  intro Z T f _ O O' hO hO'
  refine ⟨fun t => ?_⟩
  have hint : IsIntegral (f.fiber t) :=
    GeometricallyIntegral.geometrically_isIntegral _ _ _ (IsPullback.of_hasPullback f (T.fromSpecResidueField t))
  have hi : IsPreirreducible (f ⁻¹' {t}) := by
    rw [← Scheme.Hom.range_fiberι, ← Set.image_univ]
    exact (PreirreducibleSpace.isPreirreducible_univ).image _ (f.fiberι t).continuous.continuousOn
  obtain ⟨x, hx⟩ := (O.ι ≫ f).surjective t
  obtain ⟨x', hx'⟩ := (O'.ι ≫ f).surjective t
  obtain ⟨y, hy, k₁, k₂⟩ := hi _ _ O.2 O'.2
    ⟨x.1, by rw [← hx]; rfl, x.2⟩ ⟨x'.1, by rw [← hx']; rfl, x'.2⟩
  exact ⟨⟨y, k₁, k₂⟩, hy⟩

end GlobalTheory
