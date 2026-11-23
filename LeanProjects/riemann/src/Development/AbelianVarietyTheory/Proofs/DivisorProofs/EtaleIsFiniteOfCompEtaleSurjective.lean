import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeckeMap
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FormallyUnramifiedOfCompOfEtaleOfSurjective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinitePartLePreimageOfClosedFibreSubset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyFinitePresentationOfEtaleCoverStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke

namespace GlobalTheory

theorem etale_isFinite_of_comp_etale_surjective :
    ∀ (X Y Z : Scheme.{0}) (h : X ⟶ Y) (f : Y ⟶ Z), Etale h → Surjective h → Etale (h ≫ f) →
      IsFinite (h ≫ f) → IsSeparated f → LocallyOfFiniteType f → Etale f ∧ IsFinite f := by
  intro X Y Z h f h1 h2 h3 h4 h5 h6
  have : LocallyOfFinitePresentation f := GlobalTheory.T.locally_finite_presentation_of_etale_cover X Y Z h f h1 h2 h3 h4 h5 h6
  exact ⟨etale_of_comp_of_etale_of_surjective h f, isFinite_of_comp_surjective h f⟩

end GlobalTheory
