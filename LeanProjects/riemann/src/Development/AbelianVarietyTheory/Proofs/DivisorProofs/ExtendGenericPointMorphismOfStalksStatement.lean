import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendGenericPointMorphismOfStalks
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Side
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.GalCarry GlobalTheory.ShFam.GalCarry.Corr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extend_generic_point_morphism_of_stalks : ∀ (F : Type) [Field F] (Y Y' : Var F) (p' : Sp Y.Fn ⟶ Y'.X), p' ≫ Y'.str = genericPt Y ≫ Y.str →
    (∀ y : Y.X, ∃ l : Sp (Y.X.presheaf.stalk y) ⟶ Y'.X, spMap (algebraMap (Y.X.presheaf.stalk y) Y.Fn) ≫ l = p') →
      ∃ φ : Y.X ⟶ Y'.X, genericPt Y ≫ φ = p' ∧ φ ≫ Y'.str = Y.str := by
  first | exact @GlobalTheory.ShFam.GalCarry.Corr.exists_hom_of_extends | exact GlobalTheory.ShFam.GalCarry.Corr.exists_hom_of_extends | (intros; apply GlobalTheory.ShFam.GalCarry.Corr.exists_hom_of_extends <;> assumption)
