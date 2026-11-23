import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.ExistsIsInvariantSectionMemBasicOpenIff

open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem exists_isAffineOpen_le_of_isQProjOver :
    ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsQProjOver s →
      ∀ (F : Set X) (U : X.Opens), F.Finite → F ⊆ U →
        ∃ V : X.Opens, IsAffineOpen V ∧ F ⊆ V ∧ V ≤ U := by
  intro R _ X s hs F U hF hFU
  haveI := FiniteSubsetsInAffineOpens.of_isQProjOver hs
  exact FiniteSubsetsInAffineOpens.exists_isAffineOpen_le hF U hFU

end GlobalTheory
