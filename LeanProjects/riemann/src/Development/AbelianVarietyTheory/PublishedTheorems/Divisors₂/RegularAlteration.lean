import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.Published

def RegularAlteration : Prop := ∀ (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp ℤ) (d : ℕ), IsArithVar p d →
  ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (ρ : Y ⟶ X), IsArithVar (ρ ≫ p) d ∧
    (∀ y, IsRegularLocalRing (Y.presheaf.stalk y)) ∧ ρ (genericPoint Y) = genericPoint X ∧
    ρ.residueDegree (genericPoint Y) ≠ 0

end GlobalTheory.Published

end
