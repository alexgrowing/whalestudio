import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsMonHomLift
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_isMonHom_lift_of_grpPullback_abelian : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → IsNilpotent (RingHom.ker π) →
    ∀ (A₀ B₀ : Over (Sp R₀)) [GrpObj A₀] [GrpObj B₀] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (i : A₀.left ⟶ A.left) (j : B₀.left ⟶ B.left),
    IsGrpPullback A₀ A (spMap π) i → IsGrpPullback B₀ B (spMap π) j → IsAbelianScheme A → IsAbelianScheme B →
    ∀ (f₀ : A₀ ⟶ B₀) [IsMonHom f₀] (φ : A ⟶ B), i ≫ φ.left = f₀.left ≫ j → ∃! f : A ⟶ B, IsMonHom f ∧ i ≫ f.left = f₀.left ≫ j := by
  first | exact @GlobalTheory.HomLift.existsUnique_isMonHom_lift | exact GlobalTheory.HomLift.existsUnique_isMonHom_lift | (intros; apply GlobalTheory.HomLift.existsUnique_isMonHom_lift <;> assumption)
