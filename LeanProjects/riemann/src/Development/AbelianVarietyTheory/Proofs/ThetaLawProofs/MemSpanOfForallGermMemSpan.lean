import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
open GlobalTheory

namespace GlobalTheory

private theorem gs_id_eq_germ (X : Scheme.{0}) (V : X.Opens) (y : X) (hy : y ∈ V) (a : Γ(X, V)) :
    gs (𝟙 X) y V a = X.presheaf.germ V y hy a := by
  rw [gs_eq (𝟙 X) y V hy a]
  rfl

theorem mem_span_of_forall_germ_mem_span : ∀ (X : Scheme.{0}) (V : X.Opens) (J : Type) (f : J → Γ(X, V)) (r : Γ(X, V)), IsAffineOpen V → (∀ y : X, y ∈ V → (∀ i, y ∉ X.basicOpen (f i)) → gs (𝟙 X) y V r ∈ Ideal.span (Set.range fun i => gs (𝟙 X) y V (f i))) → r ∈ Ideal.span (Set.range f) := by
  intro X V J f r hV h
  rw [hV.mem_ideal_iff]
  intro y hy
  rw [Ideal.map_span, ← Set.range_comp]
  by_cases hz : ∀ i, y ∉ X.basicOpen (f i)
  · have hr := h y hy hz
    simp only [gs_id_eq_germ X V y hy] at hr
    exact hr
  · simp only [not_forall, not_not] at hz
    obtain ⟨i, hi⟩ := hz
    rw [X.mem_basicOpen (f i) y hy] at hi
    have hmem : X.presheaf.germ V y hy (f i) ∈ Ideal.span (Set.range (⇑(X.presheaf.germ V y hy).hom ∘ f)) :=
      Ideal.subset_span ⟨i, rfl⟩
    rw [Ideal.eq_top_of_isUnit_mem _ hmem hi]
    trivial

end GlobalTheory
