import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuativeLiftUniqueClosedPoint
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Side
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.GalCarry GlobalTheory.ShFam.GalCarry.Corr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuative_lift_unique_closed_point : ∀ (F : Type) [Field F] (Y Y' : Var F) (p' : Sp Y.Fn ⟶ Y'.X), p' ≫ Y'.str = genericPt Y ≫ Y.str →
    ∀ y : Y.X, (∀ (W₁ W₂ : ValuationSubring Y.Fn) (q₁ : Sp W₁ ⟶ Y'.X) (q₂ : Sp W₂ ⟶ Y'.X),
        GlobalTheory.DominatesStalk W₁ y → GlobalTheory.DominatesStalk W₂ y → spMap (algebraMap W₁ Y.Fn) ≫ q₁ = p' →
        spMap (algebraMap W₂ Y.Fn) ≫ q₂ = p' → q₁ (IsLocalRing.closedPoint W₁) = q₂ (IsLocalRing.closedPoint W₂)) →
      ∃ l : Sp (Y.X.presheaf.stalk y) ⟶ Y'.X, spMap (algebraMap (Y.X.presheaf.stalk y) Y.Fn) ≫ l = p' := by
  first | exact @GlobalTheory.ShFam.GalCarry.Corr.extends_stalk_of_unique_centre | exact GlobalTheory.ShFam.GalCarry.Corr.extends_stalk_of_unique_centre | (intros; apply GlobalTheory.ShFam.GalCarry.Corr.extends_stalk_of_unique_centre <;> assumption)
